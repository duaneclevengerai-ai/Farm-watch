"""
Farm Watch: a complete farm monitoring website in one file (Python, no extra packages).
Runs on Render (python app.py) or Vercel (api/index.py).

What it does
  - People create accounts and log in. Each person sees only their own farms.
  - Farmers add a farm by tapping its corners on a satellite map.
  - Every day it fetches Copernicus Sentinel-2 readings (moisture index NDMI, vegetation index NDVI),
    skipping cloudy passes, and fetches a 7-day weather forecast for each farm.
  - Fields of 2 ha or more are split into zones (2x2 or 3x3) and each zone is measured separately, so the page can
    show which part of a field is driest, wettest or weakest and say where to inspect.
  - It runs a daily soil-water balance for each field (FAO-56 method): the starting point comes from the satellite
    moisture index, then rain, crop water use, the farmer's irrigation log and field feedback update it day by day.
    The result is irrigation advice (when, and how many mm), stress and disease-risk flags, good spraying days,
    and a morning briefing (shown on the page and, if email is set up, emailed).

Settings (Render: Environment tab. Vercel: Project > Settings > Environment Variables)
  DATABASE_URL         Neon Postgres connection string                       (required)
  CDSE_CLIENT_ID       Copernicus Data Space OAuth client ID                 (required for satellite data)
  CDSE_CLIENT_SECRET   Copernicus Data Space OAuth client secret             (required for satellite data)
  ADMIN_TOKEN          password the daily timer uses to call /?r=cron        (required for automation)
  INVITE_CODE          optional; if set, people need this code to sign up
  SESSION_SECRET       optional; random text used to sign login cookies
  OPEN_METEO_API_KEY   optional; Open-Meteo's free service is for non-commercial use, set this for paid use
  SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASS, ALERT_FROM   optional, enables emailed alerts, briefings and password resets
  APP_URL              optional; your website address, used in password reset emails (Render sets one automatically)
  NDMI_WATCH, NDMI_DRY optional moisture thresholds, default 0.15 and 0.05
"""
import base64
import hashlib
import hmac
import json
import math
import os
import re
import secrets
import smtplib
import sys
import time
import statistics
import traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from http.server import BaseHTTPRequestHandler
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urlencode, urlparse
from urllib.request import Request, urlopen


class ConfigError(RuntimeError):
    """A problem the person setting this up needs to see, shown as-is."""


def _envf(name, default):
    try:
        return float(os.environ.get(name, default))
    except ValueError:
        return default


DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
ADMIN_TOKEN = os.environ.get("ADMIN_TOKEN", "")
CRON_SECRET = os.environ.get("CRON_SECRET", "")
INVITE_CODE = os.environ.get("INVITE_CODE", "")
SQL_HTTP_BASE = os.environ.get("SQL_HTTP_BASE", "")  # for testing only

TOKEN_URL = "https://identity.dataspace.copernicus.eu/auth/realms/CDSE/protocol/openid-connect/token"
STATS_URL = "https://sh.dataspace.copernicus.eu/api/v1/statistics"

NDMI_WATCH = _envf("NDMI_WATCH", 0.15)   # below this: Watch
NDMI_DRY = _envf("NDMI_DRY", 0.05)       # below this: Dry
MIN_CLEAR = 0.5            # skip a pass if less than half of the farm is clear of cloud
MAX_TILE_CLOUD = 80        # skip scenes over 80% cloudy before processing
FIRST_LOOKBACK_DAYS = 30   # history to pull the first time a farm is fetched
RES_DEG = 0.0001           # about 10 m; pixel size in degrees
MAX_BBOX_DEG = 0.2         # reject boundaries wider or taller than about 20 km
SERIES_LEN = 60            # readings per farm sent to the page
FETCH_BUDGET_S = 240       # stop starting new farms after this long
MAX_FARMS_PER_USER = 20
FORECAST_TTL_S = 3 * 3600
PBKDF2_ITERS = 200_000
RESET_TTL_S = 3600
LOG_KINDS = ("irrigation", "spray", "scouting", "other")
SESSION_DAYS = 30

EVALSCRIPT = """
//VERSION=3
function setup() {
  return {
    input: [{bands: ["B04", "B08", "B8A", "B11", "SCL", "dataMask"]}],
    output: [
      {id: "ndmi", bands: 1},
      {id: "ndvi", bands: 1},
      {id: "dataMask", bands: 1}
    ]
  };
}
function evaluatePixel(s) {
  // SCL classes masked out: 0 no data, 1 saturated, 3 cloud shadow,
  // 8 and 9 cloud, 10 thin cirrus, 11 snow or ice
  var bad = [0, 1, 3, 8, 9, 10, 11].indexOf(s.SCL) !== -1;
  return {
    ndmi: [(s.B8A - s.B11) / (s.B8A + s.B11)],
    ndvi: [(s.B08 - s.B04) / (s.B08 + s.B04)],
    dataMask: [(s.dataMask === 1 && !bad) ? 1 : 0]
  };
}
"""

STATUS_RANK = {"Moist": 0, "Watch": 1, "Dry": 2}


def status_of(ndmi):
    if ndmi is None:
        return None
    if ndmi < NDMI_DRY:
        return "Dry"
    if ndmi < NDMI_WATCH:
        return "Watch"
    return "Moist"


def _f(x):
    try:
        return None if x is None else float(x)
    except (TypeError, ValueError):
        return None


# ---------- database: Neon Postgres over HTTPS (no driver needed) ----------

def _conn_string():
    if not DATABASE_URL:
        raise ConfigError("DATABASE_URL is not set in the environment variables.")
    return DATABASE_URL.replace("-pooler", "", 1)  # Neon's HTTP API needs the direct host


def sql(query, params=()):
    conn = _conn_string()
    base = SQL_HTTP_BASE or "https://" + (urlparse(conn).hostname or "")
    body = json.dumps({"query": query, "params": [None if v is None else str(v) for v in params]}).encode()
    req = Request(base + "/sql", data=body, method="POST", headers={
        "Content-Type": "application/json", "Neon-Connection-String": conn})
    try:
        with urlopen(req, timeout=25) as r:
            data = json.loads(r.read())
    except HTTPError as e:
        raise RuntimeError("Database error: " + e.read().decode("utf-8", "replace")[:300])
    except URLError as e:
        raise RuntimeError(f"Could not reach the database: {e.reason}")
    fields = [f["name"] for f in data.get("fields") or []]
    return [dict(zip(fields, row)) if isinstance(row, list) else row for row in data.get("rows") or []]


_ready = False


def ensure_schema():
    global _ready
    if _ready:
        return
    for attempt in range(2):
        try:
            sql("""CREATE TABLE IF NOT EXISTS fw_users (
                id SERIAL PRIMARY KEY, email TEXT UNIQUE NOT NULL, name TEXT,
                pw_hash TEXT NOT NULL, email_briefing INTEGER NOT NULL DEFAULT 1, created TEXT)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_farms (
                id SERIAL PRIMARY KEY,
                user_id INTEGER NOT NULL REFERENCES fw_users(id) ON DELETE CASCADE,
                name TEXT NOT NULL, crop TEXT, area_ha DOUBLE PRECISION,
                lat DOUBLE PRECISION, lon DOUBLE PRECISION, geometry TEXT NOT NULL)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_readings (
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                date TEXT NOT NULL, ndmi DOUBLE PRECISION NOT NULL,
                ndvi DOUBLE PRECISION, clear_fraction DOUBLE PRECISION,
                PRIMARY KEY (farm_id, date))""")
            sql("""CREATE TABLE IF NOT EXISTS fw_forecasts (
                farm_id INTEGER PRIMARY KEY REFERENCES fw_farms(id) ON DELETE CASCADE,
                fetched TEXT NOT NULL, data TEXT NOT NULL)""")
            sql("CREATE TABLE IF NOT EXISTS fw_meta (key TEXT PRIMARY KEY, value TEXT)")
            sql("""CREATE TABLE IF NOT EXISTS fw_logs (
                id SERIAL PRIMARY KEY,
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                kind TEXT NOT NULL, amount DOUBLE PRECISION, note TEXT, date TEXT NOT NULL, created TEXT)""")
            sql("ALTER TABLE fw_farms ADD COLUMN IF NOT EXISTS soil TEXT")
            sql("ALTER TABLE fw_farms ADD COLUMN IF NOT EXISTS irrigation TEXT")
            sql("""CREATE TABLE IF NOT EXISTS fw_feedback (
                id SERIAL PRIMARY KEY,
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                date TEXT NOT NULL, verdict TEXT NOT NULL, note TEXT, snapshot TEXT)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_zone_readings (
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                zone INTEGER NOT NULL, date TEXT NOT NULL, ndmi DOUBLE PRECISION NOT NULL,
                ndvi DOUBLE PRECISION, clear_fraction DOUBLE PRECISION,
                PRIMARY KEY (farm_id, zone, date))""")
            sql("""CREATE TABLE IF NOT EXISTS fw_resets (
                token_hash TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL REFERENCES fw_users(id) ON DELETE CASCADE,
                expires TEXT NOT NULL)""")
            _ready = True
            return
        except RuntimeError:
            if attempt:
                raise
            time.sleep(0.7)  # two cold starts can race to create the tables


def get_meta(key):
    rows = sql("SELECT value FROM fw_meta WHERE key=$1", (key,))
    return rows[0]["value"] if rows else None


def set_meta(key, value):
    sql("INSERT INTO fw_meta (key, value) VALUES ($1, $2) "
        "ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value", (key, value))


# ---------- accounts and login sessions ----------

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")
_FAILS = {}  # email -> recent failed login times (per server process)


def hash_pw(pw):
    salt = os.urandom(16)
    dk = hashlib.pbkdf2_hmac("sha256", pw.encode(), salt, PBKDF2_ITERS)
    return f"pbkdf2${PBKDF2_ITERS}${salt.hex()}${dk.hex()}"


def check_pw(pw, stored):
    try:
        _, n, salt, dk = stored.split("$")
        test = hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), int(n))
        return hmac.compare_digest(test.hex(), dk)
    except Exception:
        return False


def _secret():
    s = os.environ.get("SESSION_SECRET") or ("farmwatch|" + DATABASE_URL)
    return hashlib.sha256(s.encode()).digest()


def make_session(uid):
    payload = base64.urlsafe_b64encode(json.dumps(
        {"u": uid, "e": int(time.time()) + SESSION_DAYS * 86400}).encode()).decode().rstrip("=")
    return payload + "." + hmac.new(_secret(), payload.encode(), hashlib.sha256).hexdigest()


def read_session(token):
    try:
        payload, sig = token.rsplit(".", 1)
        if not hmac.compare_digest(sig, hmac.new(_secret(), payload.encode(), hashlib.sha256).hexdigest()):
            return None
        data = json.loads(base64.urlsafe_b64decode(payload + "=" * (-len(payload) % 4)))
        return int(data["u"]) if data["e"] > time.time() else None
    except Exception:
        return None


def _user_row(r):
    return {"id": int(r["id"]), "email": r["email"], "name": r["name"] or "",
            "emailBriefing": str(r["email_briefing"]) in ("1", "True", "true")}


def get_user(uid):
    rows = sql("SELECT id, email, name, email_briefing FROM fw_users WHERE id=$1", (uid,))
    return _user_row(rows[0]) if rows else None


def signup(email, name, password, invite):
    email = (email or "").strip().lower()
    if not EMAIL_RE.match(email) or len(email) > 200:
        raise ValueError("Enter a valid email address.")
    if len(password or "") < 8 or len(password) > 200:
        raise ValueError("Choose a password of at least 8 characters.")
    if INVITE_CODE and not hmac.compare_digest((invite or "").encode(), INVITE_CODE.encode()):
        raise ValueError("That invite code is not right.")
    if sql("SELECT id FROM fw_users WHERE email=$1", (email,)):
        raise ValueError("There is already an account with that email. Log in instead.")
    try:
        rows = sql("INSERT INTO fw_users (email, name, pw_hash, created) VALUES ($1,$2,$3,$4) RETURNING id",
                   (email, (name or "").strip()[:80], hash_pw(password), date.today().isoformat()))
    except RuntimeError as e:
        if "duplicate" in str(e).lower() or "unique" in str(e).lower():
            raise ValueError("There is already an account with that email. Log in instead.")
        raise
    return int(rows[0]["id"])


def login(email, password):
    email = (email or "").strip().lower()
    now = time.time()
    recent = [t for t in _FAILS.get(email, []) if now - t < 900]
    if len(recent) >= 8:
        raise ValueError("Too many attempts. Wait 15 minutes and try again.")
    rows = sql("SELECT id, pw_hash FROM fw_users WHERE email=$1", (email,))
    ok = bool(rows) and check_pw(password or "", rows[0]["pw_hash"])
    if not ok:
        _FAILS[email] = recent + [now]
        raise ValueError("Wrong email or password.")
    _FAILS.pop(email, None)
    return int(rows[0]["id"])


_RESET_REQ = {}  # email -> recent reset request times (per server process)


def _hash_token(token):
    return hashlib.sha256(token.encode()).hexdigest()


def start_reset(email, base_url):
    """Email a one-hour reset link. Always behaves the same, whether or not the account exists."""
    email = (email or "").strip().lower()
    now = time.time()
    recent = [x for x in _RESET_REQ.get(email, []) if now - x < 3600]
    if len(recent) >= 3:
        return
    _RESET_REQ[email] = recent + [now]
    rows = sql("SELECT id FROM fw_users WHERE email=$1", (email,))
    if not rows:
        return
    token = secrets.token_urlsafe(32)
    expires = (datetime.now(timezone.utc) + timedelta(seconds=RESET_TTL_S)).isoformat(timespec="seconds")
    sql("INSERT INTO fw_resets (token_hash, user_id, expires) VALUES ($1,$2,$3)",
        (_hash_token(token), int(rows[0]["id"]), expires))
    send_mail(email, "Reset your Farm Watch password",
              f"Someone asked to reset the password for this Farm Watch account.\n\n"
              f"Open this link within one hour to choose a new password:\n{base_url}/?reset={token}\n\n"
              "If you did not ask for this, you can ignore this email.")


def finish_reset(token, password):
    if len(password or "") < 8 or len(password) > 200:
        raise ValueError("Choose a password of at least 8 characters.")
    rows = sql("SELECT user_id, expires FROM fw_resets WHERE token_hash=$1", (_hash_token(token or ""),))
    if not rows or datetime.fromisoformat(rows[0]["expires"]) < datetime.now(timezone.utc):
        raise ValueError("That reset link has expired or was already used. Ask for a new one.")
    uid = int(rows[0]["user_id"])
    sql("UPDATE fw_users SET pw_hash=$1 WHERE id=$2", (hash_pw(password), uid))
    sql("DELETE FROM fw_resets WHERE user_id=$1", (uid,))
    return uid


# ---------- farms ----------

def parse_polygon(g):
    """Accept a GeoJSON geometry, Feature or FeatureCollection holding one Polygon. Outer ring only."""
    try:
        if g.get("type") == "FeatureCollection":
            g = g["features"][0]
        if g.get("type") == "Feature":
            g = g["geometry"]
        if g.get("type") != "Polygon":
            raise ValueError("The boundary must be a single Polygon.")
        ring = [[float(p[0]), float(p[1])] for p in g["coordinates"][0]]
    except (AttributeError, KeyError, IndexError, TypeError):
        raise ValueError("That is not a valid farm boundary.")
    if len(ring) < 4 or ring[0] != ring[-1]:
        raise ValueError("The boundary needs at least 3 corners and must end where it starts.")
    if any(not (-180 <= lon <= 180 and -90 <= lat <= 90) for lon, lat in ring):
        raise ValueError("Coordinates must be longitude then latitude, in degrees.")
    lons, lats = [p[0] for p in ring], [p[1] for p in ring]
    if max(lons) - min(lons) > MAX_BBOX_DEG or max(lats) - min(lats) > MAX_BBOX_DEG:
        raise ValueError("That boundary is too large (over about 20 km across). Split it into smaller farms.")
    return {"type": "Polygon", "coordinates": [ring]}


def area_ha(geom):
    ring = geom["coordinates"][0]
    lat0 = sum(p[1] for p in ring) / len(ring)
    kx, ky = 111320 * math.cos(math.radians(lat0)), 110540
    pts = [(p[0] * kx, p[1] * ky) for p in ring]
    total = sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(pts, pts[1:] + pts[:1]))
    return round(abs(total) / 2 / 10000, 1)


def centroid(geom):
    ring = geom["coordinates"][0][:-1]
    return sum(p[1] for p in ring) / len(ring), sum(p[0] for p in ring) / len(ring)  # lat, lon


ZONE_MIN_HA = 2.0       # fields smaller than this are too small for a meaningful zone map (the moisture bands are 20 m)
ZONE_DRY_ANOM = 0.06    # a zone this much below the field median moisture is flagged for inspection
ZONE_WET_ANOM = 0.08    # a zone this much above the median is flagged as unusually wet
ZONE_NDVI_ANOM = 0.10   # a zone this much below the median greenness is flagged as weak growth
ZONE_NAMES = {2: ["NW", "NE", "SW", "SE"], 3: ["NW", "N", "NE", "W", "Centre", "E", "SW", "S", "SE"]}


def zone_grid(ha):
    ha = ha or 0
    return 0 if ha < ZONE_MIN_HA else (2 if ha < 12 else 3)


def clip_rect(ring, xmin, ymin, xmax, ymax):
    """Clip a polygon ring to a rectangle (Sutherland-Hodgman)."""
    pts = [list(p) for p in (ring[:-1] if ring[0] == ring[-1] else ring)]
    for axis, bound, keep_ge in ((0, xmin, True), (0, xmax, False), (1, ymin, True), (1, ymax, False)):
        if not pts:
            break
        out = []
        for i in range(len(pts)):
            a, b = pts[i - 1], pts[i]
            ina = a[axis] >= bound if keep_ge else a[axis] <= bound
            inb = b[axis] >= bound if keep_ge else b[axis] <= bound
            if ina != inb:
                tt = (bound - a[axis]) / (b[axis] - a[axis])
                out.append([a[0] + tt * (b[0] - a[0]), a[1] + tt * (b[1] - a[1])])
            if inb:
                out.append(b)
        pts = out
    return pts


def make_zones(geom, n):
    """Split a farm polygon into an n x n grid of zones (row 0 is the north edge)."""
    ring = geom["coordinates"][0]
    xs, ys = [p[0] for p in ring], [p[1] for p in ring]
    xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
    avg = area_ha(geom) / (n * n)
    zones = []
    for row in range(n):
        for col in range(n):
            x0, x1 = xmin + (xmax - xmin) * col / n, xmin + (xmax - xmin) * (col + 1) / n
            y1, y0 = ymax - (ymax - ymin) * row / n, ymax - (ymax - ymin) * (row + 1) / n
            pts = clip_rect(ring, x0, y0, x1, y1)
            if len(pts) < 3:
                continue
            closed = [[round(p[0], 6), round(p[1], 6)] for p in pts]
            closed.append(closed[0])
            g = {"type": "Polygon", "coordinates": [closed]}
            ha = area_ha(g)
            if ha < max(0.3, 0.2 * avg):
                continue
            zones.append({"id": row * n + col, "name": ZONE_NAMES[n][row * n + col], "geometry": g, "ha": ha})
    return zones


def zones_view(geom, ha, rows):
    """Zones with their latest readings, plus plain-language flags about uneven parts of the field."""
    n = zone_grid(ha)
    if not n or len(rows) < 3:
        return [], [], []
    try:
        layout = {z["id"]: z for z in make_zones(geom, n)}
    except Exception:
        return [], [], []
    items = []
    for r in rows:
        z = layout.get(int(r["zone"]))
        if z and _f(r["ndmi"]) is not None:
            items.append({"id": z["id"], "name": z["name"], "geometry": z["geometry"], "ha": z["ha"],
                          "ndmi": _f(r["ndmi"]), "ndvi": _f(r["ndvi"]), "date": r["date"]})
    if len(items) < 3:
        return [], [], []
    med = statistics.median(i["ndmi"] for i in items)
    nd = [i["ndvi"] for i in items if i["ndvi"] is not None]
    medv = statistics.median(nd) if nd else None
    dry, wet, weak = [], [], []
    for i in items:
        i["status"], i["anomaly"], i["flags"] = status_of(i["ndmi"]), round(i["ndmi"] - med, 3), []
        if i["anomaly"] <= -ZONE_DRY_ANOM:
            i["flags"].append("drier"); dry.append(i)
        elif i["anomaly"] >= ZONE_WET_ANOM:
            i["flags"].append("wetter"); wet.append(i)
        if medv is not None and i["ndvi"] is not None and i["ndvi"] <= medv - ZONE_NDVI_ANOM:
            i["flags"].append("weak"); weak.append(i)
    flags = []
    nm = lambda lst: ", ".join(i["name"] for i in sorted(lst, key=lambda x: x["ndmi"]))
    if dry:
        flags.append({"kind": "Uneven field", "level": "Check", "text":
                      f"Drier zones: {nm(dry)} (moisture {abs(min(i['anomaly'] for i in dry)):.2f} or more below the field median). "
                      "Inspect them: blocked or uneven watering, shallow soil or weaker roots are common causes."})
    if weak:
        flags.append({"kind": "Weak growth zone", "level": "Check", "text":
                      f"Greenness is well below the rest of the field in: {nm(weak)}. Scout there for pests, disease, nutrient or water "
                      "problems. A satellite cannot tell which."})
    if wet:
        flags.append({"kind": "Unusually wet zone", "level": "Info", "text":
                      f"Wetter than the rest of the field: {nm(wet)}. Check for leaks, overlapping coverage or poor drainage."})
    return sorted(items, key=lambda x: x["id"]), flags, [i["name"] for i in sorted(dry, key=lambda x: x["ndmi"])]


def insert_farm(user_id, name, crop, raw_geometry):
    if int(sql("SELECT COUNT(*) AS n FROM fw_farms WHERE user_id=$1", (user_id,))[0]["n"]) >= MAX_FARMS_PER_USER:
        raise ValueError(f"You can have up to {MAX_FARMS_PER_USER} farms on one account.")
    geom = parse_polygon(raw_geometry)
    ha, (lat, lon) = area_ha(geom), centroid(geom)
    rows = sql("INSERT INTO fw_farms (user_id, name, crop, area_ha, lat, lon, geometry) "
               "VALUES ($1,$2,$3,$4,$5,$6,$7) RETURNING id",
               (user_id, name.strip()[:80], (crop or "").strip()[:60], ha, lat, lon, json.dumps(geom)))
    return int(rows[0]["id"]), ha


def add_log(user_id, farm_id, kind, d, amount, note):
    if kind not in LOG_KINDS:
        raise ValueError("Choose what you did: irrigated, sprayed, scouted or other.")
    try:
        date.fromisoformat(d or "")
    except ValueError:
        raise ValueError("Enter a valid date.")
    amt = None
    if amount not in (None, ""):
        try:
            amt = float(amount)
        except (TypeError, ValueError):
            raise ValueError("The amount must be a number.")
        if not 0 <= amt <= 500:
            raise ValueError("The amount must be between 0 and 500 mm.")
    if not sql("SELECT id FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id)):
        raise ValueError("Farm not found.")
    rows = sql("INSERT INTO fw_logs (farm_id, kind, amount, note, date, created) VALUES ($1,$2,$3,$4,$5,$6) RETURNING id",
               (farm_id, kind, amt, (note or "").strip()[:200], d, datetime.now(timezone.utc).isoformat(timespec="seconds")))
    return int(rows[0]["id"])


SOILS = ("sandy", "loam", "clay")
METHODS = ("drip", "sprinkler", "flood", "unsure")
VERDICTS = ("ok", "wetter", "drier")


def update_settings(user_id, farm_id, crop, soil, method):
    if soil and soil not in SOILS:
        raise ValueError("Choose a soil type from the list.")
    if method and method not in METHODS:
        raise ValueError("Choose an irrigation method from the list.")
    if not sql("SELECT id FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id)):
        raise ValueError("Farm not found.")
    sql("UPDATE fw_farms SET crop=$1, soil=$2, irrigation=$3 WHERE id=$4 AND user_id=$5",
        ((crop or "").strip()[:60], soil or "", method or "", farm_id, user_id))


def add_feedback(user_id, farm_id, verdict, note):
    if verdict not in VERDICTS:
        raise ValueError("Choose one of the answers.")
    if not sql("SELECT id FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id)):
        raise ValueError("Farm not found.")
    sql("INSERT INTO fw_feedback (farm_id, date, verdict, note) VALUES ($1,$2,$3,$4)",
        (farm_id, date.today().isoformat(), verdict, (note or "").strip()[:200]))


def delete_log(user_id, log_id):
    sql("DELETE FROM fw_logs WHERE id=$1 AND farm_id IN (SELECT id FROM fw_farms WHERE user_id=$2)", (log_id, user_id))


def delete_farm(user_id, farm_id):
    sql("DELETE FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id))  # cascades to readings


# ---------- weather forecast (Open-Meteo) ----------

def fetch_forecast_remote(lat, lon):
    key = os.environ.get("OPEN_METEO_API_KEY", "")
    base = ("https://customer-api.open-meteo.com" if key else "https://api.open-meteo.com") + "/v1/forecast"
    q = {"latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}", "timezone": "auto", "forecast_days": "7", "past_days": "10",
         "daily": "temperature_2m_max,temperature_2m_min,precipitation_sum,precipitation_hours,"
                  "et0_fao_evapotranspiration,wind_speed_10m_max"}
    if key:
        q["apikey"] = key
    with urlopen(Request(base + "?" + urlencode(q), headers={"User-Agent": "FarmWatch/1.0"}), timeout=20) as r:
        d = json.loads(r.read())["daily"]
    days = []
    for i, t in enumerate(d["time"]):
        days.append({"date": t, "tmax": _f(d["temperature_2m_max"][i]), "tmin": _f(d["temperature_2m_min"][i]),
                     "rain": _f(d["precipitation_sum"][i]) or 0.0, "rainHours": _f(d["precipitation_hours"][i]) or 0.0,
                     "et0": _f(d["et0_fao_evapotranspiration"][i]) or 0.0, "wind": _f(d["wind_speed_10m_max"][i]) or 0.0})
    return days


def get_forecast(farm_id, lat, lon, force=False):
    rows = sql("SELECT fetched, data FROM fw_forecasts WHERE farm_id=$1", (farm_id,))
    if rows and not force:
        try:
            if time.time() - datetime.fromisoformat(rows[0]["fetched"]).timestamp() < FORECAST_TTL_S:
                return json.loads(rows[0]["data"])
        except ValueError:
            pass
    try:
        days = fetch_forecast_remote(lat, lon)
        sql("INSERT INTO fw_forecasts (farm_id, fetched, data) VALUES ($1,$2,$3) "
            "ON CONFLICT (farm_id) DO UPDATE SET fetched = EXCLUDED.fetched, data = EXCLUDED.data",
            (farm_id, datetime.now(timezone.utc).isoformat(timespec="seconds"), json.dumps(days)))
        return days
    except Exception as e:
        print("Forecast failed:", e, file=sys.stderr)
        return json.loads(rows[0]["data"]) if rows else None


# ---------- advice: irrigation, stress and disease risk, spraying days ----------

KC = [("rice", 1.15), ("maize", 1.1), ("corn", 1.1), ("tomato", 1.1), ("potato", 1.05), ("soy", 1.05),
      ("cotton", 1.1), ("sugar", 1.1), ("sunflower", 1.0), ("wheat", 1.0), ("barley", 0.95), ("lettuce", 0.9),
      ("almond", 0.9), ("grape", 0.7), ("vine", 0.7), ("olive", 0.65), ("citrus", 0.65), ("orange", 0.65),
      ("lemon", 0.65), ("pumpkin", 1.0), ("squash", 1.0), ("apple", 0.95), ("berry", 0.9), ("alfalfa", 1.15)]
DEFAULT_KC = 0.85  # typical mid-season crop coefficients; tune per crop and growth stage


def kc_for(crop):
    c = (crop or "").lower()
    for word, k in KC:
        if word in c:
            return k
    return DEFAULT_KC


def wd(iso):
    return datetime.strptime(iso, "%Y-%m-%d").strftime("%a")


def _irrigation_core(crop, status, days):
    if not days:
        by = {"Dry": ("Irrigate", "Irrigate soon", "The moisture index is low. No forecast is available right now, so check the weather before you water."),
              "Watch": ("Monitor", "Watch closely", "Moisture is getting low. Check the forecast and plan irrigation if no rain is due."),
              "Moist": ("Hold", "No irrigation needed now", "Moisture looks fine. Re-check after the next satellite pass.")}
        a = by.get(status, ("Monitor", "Waiting for data", "There is no satellite reading yet for this farm."))
        return {"action": a[0], "headline": a[1], "detail": a[2], "weekRainMm": None, "weekEtMm": None, "balanceMm": None}
    et = sum(d["et0"] for d in days) * kc_for(crop)
    rain = sum(0.8 * min(d["rain"], 25) for d in days if d["rain"] >= 2)
    bal = rain - et  # negative means the crop will use more water than rain supplies
    nums = {"weekRainMm": round(sum(d["rain"] for d in days), 1), "weekEtMm": round(et, 1), "balanceMm": round(bal, 1)}
    heavy = [d for d in days[:2] if d["rain"] >= 10]
    window = [d for d in days[:3] if d["rain"] < 2 and d["wind"] < 30]
    when = f" Best window: {wd(window[0]['date'])}." if window else " Wait for a calmer, drier day."
    if heavy:
        action, head = "Hold", "Hold off, rain is coming"
        detail = f"About {heavy[0]['rain']:.0f} mm is forecast on {wd(heavy[0]['date'])}. Re-check after it falls."
    elif status == "Dry":
        need = 5 * round(min(max(-bal + 10, 10), 45) / 5)
        action, head = "Irrigate", f"Irrigate soon, about {need} mm"
        detail = f"Moisture is low and the week looks dry (crop use about {nums['weekEtMm']:.0f} mm, rain about {nums['weekRainMm']:.0f} mm)." + when
    elif status == "Watch" and bal < -5:
        action, head = "Plan", "Plan irrigation this week"
        detail = f"Moisture is dropping and rain will not cover crop use (short by about {-bal:.0f} mm)." + when
    elif status in ("Moist", None) and bal < -15:
        action, head = "Plan", "Dry week ahead"
        detail = f"Moisture is fine now, but crop use exceeds rain by about {-bal:.0f} mm. Plan irrigation later in the week."
    elif status == "Watch":
        action, head = "Monitor", "Watch closely"
        detail = "Moisture is getting low, but rain in the forecast should help."
    else:
        action, head = ("Hold", "No irrigation needed") if status == "Moist" else ("Monitor", "Waiting for data")
        detail = "Moisture and the forecast look fine this week." if status == "Moist" else "There is no satellite reading yet for this farm."
    return dict(action=action, headline=head, detail=detail, **nums)


SOIL_AWC = {"sandy": 80, "loam": 150, "clay": 170}  # typical plant-available water, mm per metre of root zone
METHOD_EFF = {"drip": 0.9, "sprinkler": 0.75, "flood": 0.6, "unsure": 0.75}  # share of applied water the crop can use
ROOT_P = [("rice", 0.5, 0.2), ("maize", 1.0, 0.55), ("corn", 1.0, 0.55), ("tomato", 0.7, 0.4), ("potato", 0.5, 0.35),
          ("soy", 0.8, 0.5), ("cotton", 1.0, 0.65), ("sugar", 1.0, 0.65), ("sunflower", 0.9, 0.45), ("wheat", 1.0, 0.55),
          ("barley", 1.0, 0.55), ("lettuce", 0.35, 0.3), ("almond", 1.0, 0.4), ("grape", 1.0, 0.45), ("vine", 1.0, 0.45),
          ("olive", 1.2, 0.65), ("citrus", 1.0, 0.5), ("orange", 1.0, 0.5), ("lemon", 1.0, 0.5), ("pumpkin", 0.8, 0.4),
          ("squash", 0.8, 0.5), ("apple", 1.0, 0.5), ("berry", 0.5, 0.4), ("alfalfa", 1.2, 0.55)]
MAX_SINGLE_NET = 40  # mm of water to the crop in one irrigation; larger needs are split into passes
DEFAULT_ROOT_P = (0.8, 0.5)  # root depth in m, share of water the crop can use before it is stressed


def root_p_for(crop):
    c = (crop or "").lower()
    for word, zr, p in ROOT_P:
        if word in c:
            return zr, p
    return DEFAULT_ROOT_P


def ndvi_kc(ndvi, kc_max):
    """Crop factor from satellite greenness: Kc = 1.457 x NDVI - 0.1725 (general published relationship), capped per crop."""
    if ndvi is None:
        return round(kc_max * 0.8, 2)
    return round(max(0.15, min(kc_max, 1.457 * ndvi - 0.1725)), 2)


def depletion_fraction(ndmi):
    """Estimated share of the allowable root-zone water already used (1.0 = at the irrigation trigger)."""
    pts = [(NDMI_WATCH + 0.15, 0.10), (NDMI_WATCH, 0.60), (NDMI_DRY, 1.0), (NDMI_DRY - 0.10, 1.3)]
    if ndmi >= pts[0][0]:
        return pts[0][1]
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        if ndmi >= x1:
            return y0 + (y1 - y0) * (x0 - ndmi) / (x0 - x1)
    return pts[-1][1]


def water_balance(crop, soil, method, readings, days, logs, feedback):
    """Daily root-zone water balance, started from the latest satellite reading and rolled forward."""
    last = readings[-1]
    fut = days[-7:]
    today = fut[0]["date"]
    awc = SOIL_AWC.get(soil or "", SOIL_AWC["loam"])
    zr, p = root_p_for(crop)
    taw, eff, kc_max = awc * zr, METHOD_EFF.get(method or "", 0.75), kc_for(crop)
    raw = p * taw
    kc = ndvi_kc(last.get("ndvi"), kc_max)
    clamp = lambda v: max(0.0, min(taw, v))
    dr = clamp(depletion_fraction(last["ndmi"]) * raw)
    traj = [{"date": last["date"], "dr": dr, "future": last["date"] >= today}]
    irr = {}
    for lg in logs:
        if lg["kind"] == "irrigation" and lg.get("amount"):
            irr[lg["date"]] = irr.get(lg["date"], 0.0) + lg["amount"] * eff
    fb = {}
    for f in feedback:
        fb.setdefault(f["date"], f["verdict"])
    for d in days:
        if d["date"] <= last["date"]:
            continue
        dr = clamp(dr + {"wetter": -0.3 * raw, "drier": 0.3 * raw}.get(fb.get(d["date"]), 0.0))
        rain = 0.8 * min(d["rain"], 25) if d["rain"] >= 2 else 0.0
        ks = 1.0 if dr <= raw or taw <= raw else max(0.1, (taw - dr) / (taw - raw))
        dr = clamp(dr - rain - irr.get(d["date"], 0.0) + kc * d["et0"] * ks)
        traj.append({"date": d["date"], "dr": dr, "future": d["date"] >= today})
    return {"traj": traj, "taw": taw, "raw": raw, "eff": eff, "kc": kc, "zr": zr, "p": p, "today": today, "irr": irr, "fb": fb}


def smart_advice(crop, soil, method, readings, days, logs, feedback):
    wb = water_balance(crop, soil, method, readings, days, logs, feedback)
    traj, raw, taw, eff, today = wb["traj"], wb["raw"], wb["taw"], wb["eff"], wb["today"]
    fut = days[-7:]
    prior = [t for t in traj if t["date"] < today]
    adj_today = {"wetter": -0.3 * raw, "drier": 0.3 * raw}.get(wb["fb"].get(today), 0.0)  # an answer given today counts now
    now_dr = max(0.0, min(taw, (prior[-1] if prior else traj[0])["dr"] - wb["irr"].get(today, 0.0) + adj_today))  # also counts water applied today
    pct = round(now_dr / raw * 100)
    ahead = [t for t in traj if t["future"]]
    trigger = next((t for t in ahead if t["dr"] >= raw), None)
    heavy = next((d for d in fut[:2] if d["rain"] >= 10), None)
    window = [d for d in fut[:3] if d["rain"] < 2 and d["wind"] < 30]
    when = f" Best window: {wd(window[0]['date'])}." if window else " Pick a calm, dry day."
    et = sum(d["et0"] for d in fut) * wb["kc"]
    rain_w = sum(d["rain"] for d in fut)
    res = {"weekRainMm": round(rain_w, 1), "weekEtMm": round(et, 1), "balanceMm": round(rain_w - et, 1)}
    gross = lambda net: 5 * max(1, round(min(net, MAX_SINGLE_NET) / eff / 5))  # one application, capped at a realistic depth
    more = lambda net: (f" That is a lot of water for one go, so apply it in 2 or 3 passes over the next few days (about "
                        f"{5 * round(net / eff / 5)} mm in total).") if net > MAX_SINGLE_NET else ""
    if now_dr >= raw and heavy:
        res.update(action="Hold", headline="Hold off, rain is coming",
                   detail=f"The soil is at the irrigation trigger, but about {heavy['rain']:.0f} mm is forecast on {wd(heavy['date'])}. Re-check after it falls.")
    elif now_dr >= raw:
        res.update(action="Irrigate", headline=f"Irrigate now, about {gross(now_dr)} mm",
                   detail=f"The root zone has used about {pct}% of its allowable water, so it needs roughly {now_dr:.0f} mm to refill. "
                          f"At {eff * 100:.0f}% system efficiency, apply about {gross(now_dr)} mm now." + more(now_dr) + when)
    elif trigger:
        idx = ahead.index(trigger)
        net = trigger["dr"]
        res.update(action="Irrigate" if idx <= 1 else "Plan",
                   headline=f"Irrigate by {wd(trigger['date'])}, about {gross(net)} mm",
                   detail=f"Soil water is at {pct}% of the trigger today and is forecast to reach it on {wd(trigger['date'])}. "
                          f"Plan about {gross(net)} mm from your system." + more(net) + when)
    else:
        end = round(ahead[-1]["dr"] / raw * 100) if ahead else pct
        res.update(action="Hold", headline="No irrigation needed this week",
                   detail=f"Soil water is at {pct}% of the irrigation trigger and is forecast to be at {end}% by {wd(fut[-1]['date'])}.")
    res["soil"] = {"depletionPct": pct, "rawMm": round(raw), "tawMm": round(taw),
                   "trajectory": [{"date": t["date"], "pct": round(t["dr"] / raw * 100), "future": t["future"]}
                                  for t in traj if t["date"] >= (date.fromisoformat(today) - timedelta(days=4)).isoformat()]}
    last = readings[-1]
    res["why"] = (f"This uses a daily soil water balance (the FAO-56 method). Your {soil or 'loam'} soil and {wb['zr']} m of roots hold about "
                  f"{taw:.0f} mm of usable water, and irrigation is due when {wb['p'] * 100:.0f}% of it is used (about {raw:.0f} mm). "
                  f"The starting point is estimated from the satellite moisture index ({last['ndmi']:.2f} on {last['date']}), then updated "
                  f"day by day with rain, crop water use (crop factor {wb['kc']:.2f}, from greenness NDVI "
                  f"{'n/a' if last.get('ndvi') is None else format(last['ndvi'], '.2f')}), your irrigation log and your answers to "
                  "Does this match your field. Soil water is estimated, not measured, so tell Farm Watch when it looks wrong. "
                  "Advice is indicative and depends on your soil, crop stage and equipment.")
    return res


def irrigation_advice(crop, status, days, ndmi=None, logs=(), soil=None, method=None, readings=None, feedback=(), all_days=None):
    if readings and days and readings[-1].get("ndmi") is not None:
        return smart_advice(crop, soil, method, readings, all_days or days, logs, feedback)
    return _legacy_advice(crop, status, days, ndmi, logs)


def _legacy_advice(crop, status, days, ndmi=None, logs=()):
    res = _irrigation_core(crop, status, days)
    why = []
    if ndmi is not None:
        why.append(f"Latest moisture index {ndmi:.2f} ({status}).")
    if days:
        kc = kc_for(crop)
        why.append(f"Over the next 7 days the forecast gives about {sum(d['rain'] for d in days):.0f} mm of rain, while the crop "
                   f"is expected to use about {res['weekEtMm']:.0f} mm (reference evapotranspiration {sum(d['et0'] for d in days):.0f} mm "
                   f"times a crop factor of {kc}). Only rain days of 2 mm or more are counted, at 80 percent.")
    else:
        why.append("No weather forecast is available right now, so this uses the satellite reading alone.")
    recent = 0.0
    for lg in logs:
        try:
            age = (date.today() - date.fromisoformat(lg["date"])).days
        except ValueError:
            continue
        if lg["kind"] == "irrigation" and 0 <= age <= 3:
            recent += lg.get("amount") or 0
    if recent >= 10 and res["action"] in ("Irrigate", "Plan"):
        res.update(action="Monitor", headline="You irrigated recently",
                   detail=f"You logged about {recent:.0f} mm in the last 3 days. Satellite readings lag by several days, "
                          "so wait for the next clear pass before irrigating again.")
        why.append("Your recent irrigation log changed this advice.")
    why.append("Crop factors are typical mid-season values. Advice is indicative and depends on soil, crop stage and equipment.")
    res["why"] = " ".join(why)
    return res


def risk_flags(readings, days):
    flags, spray = [], []
    if len(readings) >= 2:
        a, b = readings[-2], readings[-1]
        dv = (b["ndvi"] - a["ndvi"]) if a["ndvi"] is not None and b["ndvi"] is not None else 0
        dm = b["ndmi"] - a["ndmi"]
        if dv <= -0.08 or dm <= -0.07:
            flags.append({"kind": "Satellite stress", "level": "Check", "text":
                          f"Crop vegetation or moisture fell since {a['date']} (greenness {dv:+.2f}, moisture {dm:+.2f}). "
                          "Walk the field. Water shortage, pests, disease or nutrients can all cause this, and a satellite cannot tell which."})
    if readings:
        age = (date.today() - date.fromisoformat(readings[-1]["date"])).days
        if age > 14:
            flags.append({"kind": "No recent image", "level": "Info",
                          "text": f"No clear satellite image for {age} days, usually because of cloud."})
    if days:
        wet = [d for d in days if d["rain"] >= 1 and d["rainHours"] >= 3 and d["tmax"] is not None and d["tmin"] is not None
               and 10 <= (d["tmax"] + d["tmin"]) / 2 <= 28]
        if len(wet) >= 2:
            flags.append({"kind": "Disease pressure", "level": "High" if len(wet) >= 3 else "Moderate", "text":
                          f"Wet, mild weather is forecast on {', '.join(wd(d['date']) for d in wet)}. That favours fungal "
                          "diseases such as mildews, blights and rusts. Scout the crop and talk to your agronomist about protection."})
        heat = [d for d in days if d["tmax"] is not None and d["tmax"] >= 35]
        if heat:
            flags.append({"kind": "Heat stress", "level": "Moderate", "text":
                          f"Very hot days forecast: {', '.join(wd(d['date']) for d in heat)}. Make sure irrigation keeps up."})
        frost = [d for d in days if d["tmin"] is not None and d["tmin"] <= 1]
        if frost:
            flags.append({"kind": "Frost risk", "level": "High", "text":
                          f"Near-freezing nights forecast: {', '.join(wd(d['date']) for d in frost)}."})
        spray = [wd(d["date"]) for d in days[:5] if d["wind"] < 15 and d["rain"] < 1]
    return flags, spray


def farm_view(f, readings, days, logs=(), feedback=(), zone_rows=()):
    last = readings[-1] if readings else None
    status = status_of(last["ndmi"]) if last else None
    fut = days[-7:] if days else days
    flags, spray = risk_flags(readings, fut)
    zones, zflags, zfirst = zones_view(json.loads(f["geometry"]), _f(f["area_ha"]), zone_rows) if zone_rows else ([], [], [])
    flags = flags + zflags
    advice = irrigation_advice(f["crop"], status, fut, last["ndmi"] if last else None, logs,
                               f.get("soil"), f.get("irrigation"), readings, feedback, days)
    if zfirst and advice["action"] in ("Irrigate", "Plan"):
        advice["detail"] += " Start with the driest zones: " + ", ".join(zfirst) + "."
        advice["zonesFirst"] = zfirst
    return {"id": int(f["id"]), "name": f["name"], "crop": f["crop"] or "", "areaHa": _f(f["area_ha"]),
            "soil": f.get("soil") or "", "irrigation": f.get("irrigation") or "",
            "geometry": json.loads(f["geometry"]), "series": readings, "status": status,
            "forecast": fut, "advice": advice, "zones": zones,
            "feedback": feedback[0] if feedback else None, "logs": list(logs)[:15],
            "risks": flags, "sprayDays": spray}


def build_briefing(farms):
    order = {"Dry": 0, "Watch": 1, "Moist": 2, None: 3}
    items = []
    for f in farms:
        high = any(r["level"] == "High" for r in f["risks"])
        pr = order[f["status"]] - (0.5 if high else 0) - (0.25 if f["risks"] else 0)
        bits = [f"{f['name']}: {f['status'] or 'no satellite reading yet'}. {f['advice']['headline']}."]
        if f["risks"]:
            bits.append(f["risks"][0]["kind"] + ": " + f["risks"][0]["text"].split(". ")[0] + ".")
        items.append({"farm": f["name"], "priority": pr, "text": " ".join(bits)})
    items.sort(key=lambda i: i["priority"])
    n = len(farms)
    need = sum(1 for f in farms if f["advice"]["action"] in ("Irrigate", "Plan")
               or any(r["level"] in ("High", "Check") for r in f["risks"]))
    watch = sum(1 for f in farms if f["status"] in ("Dry", "Watch"))
    waiting = sum(1 for f in farms if f["status"] is None)
    s = "s" if n != 1 else ""
    if not n:
        head = "Add a farm to get your daily briefing."
    elif waiting == n:
        head = "Waiting for the first satellite reading. Tap Update satellite data."
    elif need:
        head = f"{need} of {n} farm{s} {'needs' if need == 1 else 'need'} attention today."
    elif watch:
        head = (f"Keep an eye on {farms[0]['name']} today." if n == 1
                else f"{watch} of {n} farms to keep an eye on today.")
    else:
        head = "Your farm looks fine today." if n == 1 else f"All {n} farms look fine today."
    return {"headline": head, "items": items}


def farms_payload(user_id):
    ensure_schema()
    farms = sql("SELECT id, name, crop, area_ha, lat, lon, geometry, soil, irrigation FROM fw_farms WHERE user_id=$1 ORDER BY name", (user_id,))
    rows = sql("SELECT r.farm_id, r.date, r.ndmi, r.ndvi FROM ("
               "SELECT farm_id, date, ndmi, ndvi, ROW_NUMBER() OVER (PARTITION BY farm_id ORDER BY date DESC) AS rn "
               "FROM fw_readings WHERE farm_id IN (SELECT id FROM fw_farms WHERE user_id=$1)) r "
               "WHERE r.rn <= $2 ORDER BY r.farm_id, r.date", (user_id, SERIES_LEN))
    by = {}
    for r in rows:
        by.setdefault(int(r["farm_id"]), []).append({"date": r["date"], "ndmi": _f(r["ndmi"]), "ndvi": _f(r["ndvi"])})
    since = (date.today() - timedelta(days=60)).isoformat()
    logs_by = {}
    for lg in sql("SELECT id, farm_id, kind, amount, note, date FROM fw_logs WHERE date >= $2 AND farm_id IN "
                  "(SELECT id FROM fw_farms WHERE user_id=$1) ORDER BY date DESC, id DESC", (user_id, since)):
        logs_by.setdefault(int(lg["farm_id"]), []).append({"id": int(lg["id"]), "kind": lg["kind"], "amount": _f(lg["amount"]),
                                                          "note": lg["note"] or "", "date": lg["date"]})
    fb_by = {}
    for fb in sql("SELECT farm_id, date, verdict FROM fw_feedback WHERE date >= $2 AND farm_id IN "
                  "(SELECT id FROM fw_farms WHERE user_id=$1) ORDER BY date DESC, id DESC", (user_id, since)):
        fb_by.setdefault(int(fb["farm_id"]), []).append({"date": fb["date"], "verdict": fb["verdict"]})
    zr_by = {}
    for z in sql("SELECT z.farm_id, z.zone, z.date, z.ndmi, z.ndvi FROM fw_zone_readings z JOIN "
                 "(SELECT farm_id, MAX(date) AS d FROM fw_zone_readings GROUP BY farm_id) m "
                 "ON z.farm_id = m.farm_id AND z.date = m.d WHERE z.farm_id IN "
                 "(SELECT id FROM fw_farms WHERE user_id=$1)", (user_id,)):
        zr_by.setdefault(int(z["farm_id"]), []).append(z)
    with ThreadPoolExecutor(max_workers=5) as pool:
        forecasts = list(pool.map(lambda f: get_forecast(int(f["id"]), _f(f["lat"]), _f(f["lon"])), farms))
    views = [farm_view(f, by.get(int(f["id"]), []), fc, logs_by.get(int(f["id"]), []), fb_by.get(int(f["id"]), []),
                       zr_by.get(int(f["id"]), []))
             for f, fc in zip(farms, forecasts)]
    return {"farms": views, "briefing": build_briefing(views),
            "thresholds": {"watch": NDMI_WATCH, "dry": NDMI_DRY}, "lastFetch": get_meta("last_fetch")}


# ---------- satellite fetch ----------

def get_token():
    cid, secret = os.environ.get("CDSE_CLIENT_ID"), os.environ.get("CDSE_CLIENT_SECRET")
    if not cid or not secret:
        raise ConfigError("Satellite data is not set up yet: add CDSE_CLIENT_ID and CDSE_CLIENT_SECRET.")
    req = Request(TOKEN_URL, method="POST",
                  data=urlencode({"grant_type": "client_credentials", "client_id": cid,
                                  "client_secret": secret}).encode(),
                  headers={"Content-Type": "application/x-www-form-urlencoded"})
    try:
        with urlopen(req, timeout=30) as r:
            return json.loads(r.read())["access_token"]
    except HTTPError as e:
        raise ConfigError(f"Copernicus rejected the login (HTTP {e.code}). Check the client ID and secret.")
    except URLError as e:
        raise RuntimeError(f"Could not reach Copernicus: {e.reason}")


def request_stats(token, geometry, start, end):
    """One call returns daily NDMI/NDVI averages for the whole farm polygon."""
    payload = {
        "input": {
            "bounds": {"geometry": geometry,
                       "properties": {"crs": "http://www.opengis.net/def/crs/EPSG/0/4326"}},
            "data": [{"type": "sentinel-2-l2a",
                      "dataFilter": {"mosaickingOrder": "leastCC", "maxCloudCoverage": MAX_TILE_CLOUD}}],
        },
        "aggregation": {
            "timeRange": {"from": f"{start}T00:00:00Z", "to": f"{end + timedelta(days=1)}T00:00:00Z"},
            "aggregationInterval": {"of": "P1D"},
            "evalscript": EVALSCRIPT, "resx": RES_DEG, "resy": RES_DEG,
        },
    }
    for attempt in range(3):
        req = Request(STATS_URL, data=json.dumps(payload).encode(), method="POST", headers={
            "Content-Type": "application/json", "Authorization": f"Bearer {token}"})
        try:
            with urlopen(req, timeout=120) as r:
                return json.loads(r.read()).get("data", [])
        except HTTPError as e:
            if e.code == 429:
                time.sleep(5 * (attempt + 1))
                continue
            raise RuntimeError(f"Copernicus error {e.code}: " + e.read().decode("utf-8", "replace")[:200])
    raise RuntimeError("Rate limited by Copernicus; it will retry on the next run.")


def parse_stats(items):
    """Turn API rows into readings, dropping passes that are too cloudy."""
    out = []
    for item in items:
        try:
            o = item["outputs"]
            n = o["ndmi"]["bands"]["B0"]["stats"]
            v = o["ndvi"]["bands"]["B0"]["stats"]
            total = n["sampleCount"]
            clear = (total - n["noDataCount"]) / total if total else 0
            ndmi, ndvi = float(n["mean"]), float(v["mean"])
        except (KeyError, TypeError, ValueError, ZeroDivisionError):
            continue
        if clear < MIN_CLEAR or math.isnan(ndmi) or math.isnan(ndvi):
            continue
        out.append({"date": item["interval"]["from"][:10],
                    "ndmi": round(ndmi, 4), "ndvi": round(ndvi, 4), "clear": round(clear, 2)})
    return out


def fetch_zones(token, farm, d):
    """Measure each zone of a field on one image date. Returns how many zone readings were stored."""
    n = zone_grid(_f(farm["area_ha"]))
    if not n:
        return 0
    day = date.fromisoformat(d)
    rows = []
    for z in make_zones(json.loads(farm["geometry"]), n):
        for r in parse_stats(request_stats(token, z["geometry"], day, day)):
            if r["date"] == d:
                rows.append((int(farm["id"]), z["id"], d, r["ndmi"], r["ndvi"], r["clear"]))
    if len(rows) < 3:
        return 0
    marks, params = [], []
    for i, row in enumerate(rows):
        marks.append("(" + ",".join(f"${i * 6 + k}" for k in range(1, 7)) + ")")
        params += list(row)
    return len(sql("INSERT INTO fw_zone_readings (farm_id, zone, date, ndmi, ndvi, clear_fraction) VALUES "
                   + ",".join(marks) + " ON CONFLICT DO NOTHING RETURNING zone", params))


def fetch_all(user_id=None):
    """Fetch new satellite readings for one person's farms (or everyone's), in parallel."""
    t0 = time.time()
    token = get_token()
    cols = "f.id, f.name, f.crop, f.geometry, f.area_ha, u.email, u.email_briefing"
    base = f"SELECT {cols} FROM fw_farms f JOIN fw_users u ON u.id = f.user_id"
    farms = sql(base + " WHERE f.user_id=$1 ORDER BY f.id", (user_id,)) if user_id else sql(base + " ORDER BY f.id")
    if not farms:
        return {"messages": ["No farms yet. Add one first."], "stored": 0, "alerts": 0}
    ids = ",".join(str(int(f["id"])) for f in farms)
    last = {int(r["farm_id"]): r for r in sql(
        "SELECT r.farm_id, r.date, r.ndmi FROM fw_readings r "
        "JOIN (SELECT farm_id, MAX(date) AS d FROM fw_readings GROUP BY farm_id) m "
        f"ON r.farm_id = m.farm_id AND r.date = m.d WHERE r.farm_id IN ({ids})")}
    today = date.today()

    zone_have = {int(r["farm_id"]): r["d"] for r in sql(
        f"SELECT farm_id, MAX(date) AS d FROM fw_zone_readings WHERE farm_id IN ({ids}) GROUP BY farm_id")}

    def work(farm):
        name, fid = farm["name"], int(farm["id"])
        try:
            if time.time() - t0 > FETCH_BUDGET_S:
                return f"{name}: skipped, out of time (it will continue on the next run)", 0, None
            prev = last.get(fid)
            start = date.fromisoformat(prev["date"]) + timedelta(days=1) if prev \
                else today - timedelta(days=FIRST_LOOKBACK_DAYS)
            msgs, stored_n, alert, latest = [], 0, None, (prev["date"] if prev else None)
            if start > today:
                msgs.append("already up to date")
            else:
                readings = parse_stats(request_stats(token, json.loads(farm["geometry"]), start, today))
                if not readings:
                    msgs.append("no new clear pass yet")
                else:
                    marks, params = [], []
                    for i, r in enumerate(readings):
                        marks.append("(" + ",".join(f"${i * 5 + k}" for k in range(1, 6)) + ")")
                        params += [fid, r["date"], r["ndmi"], r["ndvi"], r["clear"]]
                    stored = sql("INSERT INTO fw_readings (farm_id, date, ndmi, ndvi, clear_fraction) VALUES "
                                 + ",".join(marks) + " ON CONFLICT DO NOTHING RETURNING farm_id", params)
                    stored_n = len(stored)
                    msgs.append(f"stored {stored_n} new reading(s)")
                    newest = max(readings, key=lambda r: r["date"])
                    latest = max(latest or "", newest["date"])
                    if prev and _f(prev["ndmi"]) is not None:
                        before, now = status_of(_f(prev["ndmi"])), status_of(newest["ndmi"])
                        if STATUS_RANK[now] > STATUS_RANK[before]:
                            alert = (farm["email"], name, farm["crop"], before, now, newest)
            if latest and zone_grid(_f(farm["area_ha"])) and latest > zone_have.get(fid, ""):
                try:
                    zn = fetch_zones(token, farm, latest)
                    if zn:
                        msgs.append(f"measured {zn} field zones")
                except Exception as e:
                    msgs.append(f"zones failed ({e})")
            return f"{name}: " + ", ".join(msgs), stored_n, alert
        except Exception as e:  # one failing farm should not stop the rest
            return f"{name}: failed ({e})", 0, None

    with ThreadPoolExecutor(max_workers=5) as pool:
        results = list(pool.map(work, farms))
    alerts = [a for _, _, a in results if a]
    for a in alerts:
        try:
            send_alert(*a)
        except Exception as e:
            print("Alert email failed:", e, file=sys.stderr)
    return {"messages": [m for m, _, _ in results], "stored": sum(n for _, n, _ in results), "alerts": len(alerts)}


def refresh_forecasts(user_id=None):
    q = "SELECT id, lat, lon FROM fw_farms" + (" WHERE user_id=$1" if user_id else "")
    farms = sql(q, (user_id,) if user_id else ())
    with ThreadPoolExecutor(max_workers=5) as pool:
        list(pool.map(lambda f: get_forecast(int(f["id"]), _f(f["lat"]), _f(f["lon"]), force=True), farms))


def run_user_fetch(user_id):
    ensure_schema()
    result = fetch_all(user_id)
    refresh_forecasts(user_id)
    set_meta("last_fetch", datetime.now(timezone.utc).isoformat(timespec="seconds"))
    return result


def run_daily():
    """Everything the daily timer does: satellite data, forecasts, and morning briefing emails."""
    ensure_schema()
    result = fetch_all(None)
    refresh_forecasts(None)
    sent = 0
    if os.environ.get("SMTP_HOST"):
        for u in sql("SELECT id, email, name, email_briefing FROM fw_users WHERE email_briefing=1"):
            try:
                p = farms_payload(int(u["id"]))
                if p["farms"]:
                    send_mail(u["email"], "Your Farm Watch morning briefing", briefing_text(u["name"], p["briefing"]))
                    sent += 1
            except Exception as e:
                print("Briefing email failed:", e, file=sys.stderr)
    set_meta("last_fetch", datetime.now(timezone.utc).isoformat(timespec="seconds"))
    result["briefings"] = sent
    return result


# ---------- email ----------

def send_mail(to, subject, body):
    host = os.environ.get("SMTP_HOST")
    if not host or not to:
        return False  # email not configured
    msg = EmailMessage()
    msg["Subject"], msg["To"] = subject, to
    msg["From"] = os.environ.get("ALERT_FROM", os.environ.get("SMTP_USER", "farmwatch@localhost"))
    msg.set_content(body)
    with smtplib.SMTP(host, int(os.environ.get("SMTP_PORT", "587")), timeout=20) as s:
        s.starttls()
        if os.environ.get("SMTP_USER"):
            s.login(os.environ["SMTP_USER"], os.environ.get("SMTP_PASS", ""))
        s.send_message(msg)
    return True


def briefing_text(name, b):
    lines = [f"Good morning{' ' + name if name else ''}.", "", b["headline"], ""]
    lines += ["- " + i["text"] for i in b["items"]]
    lines += ["", "Open Farm Watch for the full forecast, irrigation advice and trends."]
    return "\n".join(lines)


def send_alert(to, name, crop, previous, current, reading):
    subject = f"{name} moved from {previous} to {current}"
    body = (f"{name} ({crop or 'crop not set'}) is now {current}.\n"
            f"Moisture index (NDMI): {reading['ndmi']:.2f} on {reading['date']}.\n"
            f"Open Farm Watch for the trend and irrigation advice.")
    print("ALERT:", subject, file=sys.stderr)
    send_mail(to, subject, body)


# ---------- page ----------

APP_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Farm Watch</title>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.css">
<style>
:root{--bg:#eef2f0;--panel:#fff;--ink:#14231f;--mute:#5b6b66;--line:#d3dcd8;--wet:#1f6fb5;--ok:#2f7d4f;--watch:#b87a10;--dry:#b3412e}
@media (prefers-color-scheme:dark){:root{--bg:#0f1815;--panel:#17231f;--ink:#e6efeb;--mute:#93a39d;--line:#2a3a35;--wet:#5aa6e6;--ok:#58b57c;--watch:#e0a63c;--dry:#e2705a}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:16px/1.5 system-ui,-apple-system,"Segoe UI",sans-serif}
a{color:var(--wet)}h1{margin:0;font-size:22px;letter-spacing:-.01em}h2{margin:0 0 8px;font-size:17px}h3{margin:14px 0 4px;font-size:15px}
.wrap{max-width:1100px;margin:0 auto;padding:14px 16px 36px}
header{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-bottom:10px}
.sub,.help{color:var(--mute);font-size:14px}
.panel{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px;margin-bottom:12px}
.tiles{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:12px}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:8px 12px}
.tile b{display:block;font-size:24px;line-height:1.1}.tile span{font-size:13px;color:var(--mute)}
.grid{display:grid;grid-template-columns:320px 1fr;gap:12px}
@media(max-width:800px){.grid{grid-template-columns:1fr}.tiles{grid-template-columns:repeat(2,1fr)}}
.list{padding:0;overflow:hidden}
.item{display:block;width:100%;text-align:left;font:inherit;color:inherit;background:none;border:0;border-bottom:1px solid var(--line);padding:12px 14px;cursor:pointer}
.item:last-child{border-bottom:0}.item[aria-current=true],.item:hover{background:var(--bg)}
.row{display:flex;justify-content:space-between;align-items:baseline;gap:8px}
.pill{font-size:13px;font-weight:650}
label{display:block;font-size:14px;color:var(--mute);margin:8px 0 3px}
input:not([type=checkbox]),select,textarea{width:100%;padding:11px;border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink);font:inherit}
.b{font:inherit;font-weight:600;padding:10px 14px;border-radius:8px;border:0;background:var(--wet);color:#fff;cursor:pointer;min-height:44px;margin:8px 8px 0 0}
.b.alt{background:transparent;color:var(--ink);border:1px solid var(--line)}
.b.danger{background:transparent;color:var(--dry);border:1px solid var(--line)}
.b:disabled{opacity:.55;cursor:default}
button:focus-visible,input:focus-visible,.item:focus-visible{outline:2px solid var(--wet);outline-offset:2px}
.auth{max-width:400px;margin:24px auto}
.two{display:grid;grid-template-columns:1fr 1fr;gap:8px}
details.why{margin-top:8px;font-size:14px}details.why summary{cursor:pointer;color:var(--wet)}
.logrow{display:flex;justify-content:space-between;align-items:center;gap:8px;border-bottom:1px solid var(--line);padding:6px 0;font-size:14px}
.logrow button{background:none;border:0;color:var(--dry);font-size:18px;cursor:pointer;padding:4px 10px}
.bar{height:6px;border-radius:3px;background:var(--line);margin-top:6px;overflow:hidden}.bar i{display:block;height:100%}
.b.sm{min-height:36px;padding:4px 12px;margin:6px 6px 0 0}
ol.steps{margin:6px 0 0;padding-left:20px}ol.steps li{margin-bottom:6px}
#map,#dmap{height:300px;border-radius:8px;margin-top:8px;background:var(--bg)}
#dmap{height:210px}
.bar{display:flex;gap:8px;flex-wrap:wrap}.bar input{flex:1;min-width:140px}.bar .b{margin:0}
.fc{display:grid;grid-template-columns:repeat(7,1fr);gap:4px;margin-top:6px}
.fc div{background:var(--bg);border-radius:8px;padding:6px 2px;text-align:center;font-size:12px;line-height:1.35}
.fc b{display:block;font-size:13px}
.adv{border-left:4px solid var(--mute);padding:8px 12px;background:var(--bg);border-radius:6px;margin-top:6px}
.adv b{display:block;font-size:17px}
.risk{display:flex;gap:8px;margin-top:6px;font-size:14px}.risk i{font-style:normal;font-weight:650;white-space:nowrap}
.stats{display:flex;gap:24px;flex-wrap:wrap;margin:10px 0 0}.stats b{display:block;font-size:22px}.stats span{font-size:13px;color:var(--mute)}
svg.chart{width:100%;height:auto;display:block;margin-top:6px}
#status{min-height:1.4em;font-size:14px;margin:0 0 8px}.bad{color:var(--dry)}.good{color:var(--ok)}
.note{color:var(--mute);font-size:13px;margin-top:10px}
ul.brief{margin:6px 0 0;padding-left:18px}ul.brief li{margin-bottom:4px}
</style>
</head>
<body>
<div class="wrap">
  <header><h1>Farm Watch</h1><div id="who" class="sub" hidden><span id="whoName"></span> <button id="logout" class="b alt" type="button" style="min-height:36px;margin:0 0 0 8px;padding:4px 12px">Log out</button></div></header>
  <p id="status" role="status" aria-live="polite"></p>

  <section id="auth" class="panel auth" hidden>
    <h2 id="authTitle">Log in</h2>
    <p class="sub">Satellite moisture, a 7-day forecast and irrigation advice for your farms.</p>
    <div id="nameRow" hidden><label for="nm">Your name</label><input id="nm" autocomplete="name"></div>
    <div id="emRow"><label for="em">Email</label><input id="em" type="email" autocomplete="email"></div>
    <div id="pwRow"><label for="pw" id="pwLabel">Password</label><input id="pw" type="password" autocomplete="current-password"></div>
    <div id="invRow" hidden><label for="inv">Invite code</label><input id="inv" autocomplete="off"></div>
    <button id="authGo" class="b" type="button">Log in</button>
    <button id="authSwap" class="b alt" type="button">Create an account</button>
    <p id="forgotRow" class="help" style="margin:10px 0 0"><a href="#" id="forgot">Forgot your password?</a></p>
    <p id="authErr" class="bad" role="alert"></p>
  </section>

  <div id="app" hidden>
    <div class="panel"><h2>Morning briefing</h2><div id="brief"></div></div>
    <div id="tiles" class="tiles"></div>
    <div style="margin-bottom:12px">
      <button id="addToggle" class="b" type="button" style="margin-top:0">Add a farm</button>
      <button id="fetch" class="b alt" type="button" style="margin-top:0">Update satellite data</button>
    </div>
    <div id="addPanel" class="panel" hidden>
      <h2>Add a farm</h2>
      <label for="fn">Farm name</label><input id="fn" maxlength="80">
      <label for="fc">Crop</label><input id="fc" maxlength="60" placeholder="Wheat, maize, olives…">
      <label for="q">Find the farm on the map</label>
      <div class="bar"><input id="q" placeholder="Village, town or address" aria-label="Search for a place"><button id="go" class="b alt" type="button">Search</button><button id="loc" class="b alt" type="button">My location</button></div>
      <div id="map" aria-label="Map for drawing the farm boundary"></div>
      <p class="help">Tap each corner of the field in order. Switch to Satellite view (top right of the map) to see field boundaries.</p>
      <p id="area" class="help"></p>
      <button id="undo" class="b alt" type="button">Undo last corner</button><button id="clear" class="b alt" type="button">Clear</button><button id="save" class="b" type="button">Save farm</button>
    </div>
    <div class="grid">
      <nav class="panel list" id="list" aria-label="Farms"></nav>
      <section class="panel" id="detail" aria-live="polite"></section>
    </div>
    <p class="note"><label style="display:inline;margin:0"><input id="emailPref" type="checkbox"> Email me the morning briefing and moisture alerts</label> <button id="testMail" class="b alt" type="button" style="min-height:34px;padding:2px 12px;margin:0 0 0 8px">Send me a test email</button></p>
    <p class="note">Guidance only. Irrigation and risk advice is indicative and depends on your soil, crop stage and equipment. Satellite moisture (NDMI) measures canopy moisture, not soil moisture directly. Weather forecast data: Open-Meteo. Satellite data: Copernicus Sentinel-2.</p>
  </div>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.js"></script>
<script>
(function(){
var API="/api/index";
var SAT="https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}";
var OSM="https://tile.openstreetmap.org/{z}/{x}/{y}.png";
var $=function(id){return document.getElementById(id)};
var esc=function(s){return String(s==null?"":s).replace(/[&<>"']/g,function(c){return {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]})};
var DATA=null,TH={watch:0.15,dry:0.05},ORDER=[],sel=null,dmap=null,amap=null,pts=[],poly=null,dots=[],mode="login",armed=null;
var COL={Dry:"var(--dry)",Watch:"var(--watch)",Moist:"var(--ok)","No data":"var(--mute)"};
var HEX={Dry:"#e2705a",Watch:"#e0a63c",Moist:"#58b57c","No data":"#9fb0aa"};
var ACOL={Irrigate:"var(--dry)",Plan:"var(--watch)",Hold:"var(--wet)",Monitor:"var(--mute)"};
function say(m,bad){var s=$("status");s.textContent=m||"";s.className=bad?"bad":"good"}
function lab(f){return f.status||"No data"}
function lastOf(f){return f.series.length?f.series[f.series.length-1]:null}
function ago(d){var n=Math.round((Date.now()-new Date(d+"T00:00:00Z").getTime())/864e5);return n<=0?"today":n===1?"1 day ago":n+" days ago"}
function wd(d){return new Date(d+"T00:00:00").toLocaleDateString(undefined,{weekday:"short"})}
async function api(method,route,body){
  var r=await fetch(API+"?r="+route,{method:method,credentials:"same-origin",headers:{"Content-Type":"application/json"},body:method==="GET"?undefined:JSON.stringify(body||{})});
  var data=await r.json().catch(function(){return {}});
  if(r.status===401&&route!=="login"&&route!=="signup"){showAuth(false);throw new Error("Please log in.")}
  if(!r.ok)throw new Error(data.error||("The server returned "+r.status));
  return data;
}

/* ---------- login ---------- */
var INVITE=false,RESET=(new URLSearchParams(location.search)).get("reset")||"";
function showAuth(){
  $("app").hidden=true;$("who").hidden=true;$("auth").hidden=false;
  var su=mode==="signup",fg=mode==="forgot",rs=mode==="reset";
  $("authTitle").textContent=su?"Create your account":fg?"Reset your password":rs?"Choose a new password":"Log in";
  $("authGo").textContent=su?"Create account":fg?"Send reset link":rs?"Save new password":"Log in";
  $("authSwap").textContent=(su||fg||rs)?"Back to log in":"Create an account";
  $("nameRow").hidden=!su;$("invRow").hidden=!(su&&INVITE);
  $("emRow").hidden=rs;$("pwRow").hidden=fg;$("forgotRow").hidden=mode!=="login";
  $("pwLabel").textContent=rs?"New password (at least 8 characters)":"Password";
  $("pw").setAttribute("autocomplete",(su||rs)?"new-password":"current-password");
}
function authMsg(t,good){var e=$("authErr");e.textContent=t||"";e.className=good?"good":"bad"}
$("authSwap").addEventListener("click",function(){mode=mode==="login"?"signup":"login";authMsg("");showAuth()});
$("forgot").addEventListener("click",function(e){e.preventDefault();mode="forgot";authMsg("");showAuth()});
$("authGo").addEventListener("click",async function(){
  authMsg("");$("authGo").disabled=true;
  try{
    if(mode==="forgot"){
      var f=await api("POST","forgot",{email:$("em").value});
      authMsg(f.emailConfigured?"If that email has an account, a reset link is on its way. Check your inbox.":"Email is not set up on this server yet, so reset links cannot be sent.",f.emailConfigured);
    }else if(mode==="reset"){
      await api("POST","reset",{token:RESET,password:$("pw").value});
      RESET="";try{history.replaceState(null,"",location.pathname)}catch(e){}
      $("pw").value="";mode="login";showAuth();authMsg("Password changed. Log in with your new password.",true);
    }else{
      await api("POST",mode,{email:$("em").value,password:$("pw").value,name:$("nm").value,invite:$("inv").value});
      $("pw").value="";await enter();
    }
  }catch(e){authMsg(e.message)}
  $("authGo").disabled=false;
});
$("pw").addEventListener("keydown",function(e){if(e.key==="Enter")$("authGo").click()});
$("logout").addEventListener("click",async function(){try{await api("POST","logout")}catch(e){}DATA=null;sel=null;mode="login";showAuth()});

/* ---------- dashboard ---------- */
function chart(s){
  var W=640,H=200,p=30,v=s.map(function(x){return x.ndmi}),lo=Math.min.apply(null,[-0.05].concat(v))-0.02,hi=Math.max.apply(null,[0.4].concat(v))+0.02;
  var X=function(i){return p+i*(W-2*p)/Math.max(1,s.length-1)},Y=function(y){return H-p-(y-lo)/(hi-lo)*(H-2*p)};
  var band=function(a,b,c){var y1=Y(Math.min(b,hi)),y2=Y(Math.max(a,lo));return '<rect x="'+p+'" y="'+y1+'" width="'+(W-2*p)+'" height="'+Math.max(0,y2-y1)+'" fill="'+c+'" opacity=".13"/>'};
  var line=s.map(function(x,i){return (i?"L":"M")+X(i)+" "+Y(x.ndmi)}).join(" ");
  var d=s.map(function(x,i){return '<circle cx="'+X(i)+'" cy="'+Y(x.ndmi)+'" r="3.5" fill="var(--wet)"><title>'+x.date+": NDMI "+x.ndmi.toFixed(2)+'</title></circle>'}).join("");
  return '<svg class="chart" viewBox="0 0 '+W+' '+H+'" role="img" aria-label="Moisture index over time">'+band(lo,TH.dry,"var(--dry)")+band(TH.dry,TH.watch,"var(--watch)")+band(TH.watch,hi,"var(--ok)")+'<path d="'+line+'" fill="none" stroke="var(--wet)" stroke-width="2.5"/>'+d+'<text x="'+p+'" y="'+(H-8)+'" font-size="12" fill="var(--mute)">'+s[0].date+'</text><text x="'+(W-p)+'" y="'+(H-8)+'" font-size="12" fill="var(--mute)" text-anchor="end">'+s[s.length-1].date+'</text></svg>';
}
function drawDetailMap(f){
  if(dmap){dmap.remove();dmap=null}
  var el=$("dmap");if(!el)return;
  if(typeof L==="undefined"||!f.geometry){el.textContent="Map unavailable.";return}
  dmap=L.map(el,{scrollWheelZoom:false});
  L.tileLayer(SAT,{maxZoom:19,attribution:"Tiles &copy; Esri"}).addTo(dmap);
  var ring=f.geometry.coordinates[0].map(function(p){return [p[1],p[0]]});
  var pl=L.polygon(ring,{color:HEX[lab(f)],weight:3,fillOpacity:(f.zones&&f.zones.length)?0:0.15}).addTo(dmap);
  (f.zones||[]).forEach(function(z){
    var zr=z.geometry.coordinates[0].map(function(p){return [p[1],p[0]]});
    L.polygon(zr,{color:HEX[z.status],weight:1,fillColor:HEX[z.status],fillOpacity:0.4}).bindTooltip(z.name+": "+z.ndmi.toFixed(2)+" ("+z.status+")").addTo(dmap);
  });
  dmap.fitBounds(pl.getBounds(),{padding:[24,24]});
}
function soilChart(tr){
  if(!tr||tr.length<2)return "";
  var W=640,H=150,p=28,mx=Math.max(130,Math.max.apply(null,tr.map(function(t){return t.pct}))+10);
  var X=function(i){return p+i*(W-2*p)/(tr.length-1)},Y=function(v){return H-p-(Math.min(v,mx)/mx)*(H-2*p)};
  var line=tr.map(function(t,i){return (i?"L":"M")+X(i)+" "+Y(t.pct)}).join(" ");
  var ti=tr.findIndex(function(t){return t.future}),dots=tr.map(function(t,i){return '<circle cx="'+X(i)+'" cy="'+Y(t.pct)+'" r="3" fill="'+(t.future?"var(--wet)":"var(--mute)")+'"><title>'+t.date+": "+t.pct+"%</title></circle>"}).join("");
  return '<svg class="chart" viewBox="0 0 '+W+' '+H+'" role="img" aria-label="Projected soil water use"><line x1="'+p+'" x2="'+(W-p)+'" y1="'+Y(100)+'" y2="'+Y(100)+'" stroke="var(--dry)" stroke-dasharray="5 4"/><text x="'+(W-p)+'" y="'+(Y(100)-5)+'" font-size="12" fill="var(--dry)" text-anchor="end">Irrigation trigger (100%)</text>'+
    (ti>0?'<line x1="'+X(ti)+'" x2="'+X(ti)+'" y1="'+p+'" y2="'+(H-p)+'" stroke="var(--line)"/><text x="'+(X(ti)+4)+'" y="'+(p+10)+'" font-size="12" fill="var(--mute)">Today</text>':"")+
    '<path d="'+line+'" fill="none" stroke="var(--wet)" stroke-width="2.5"/>'+dots+'<text x="'+p+'" y="'+(H-6)+'" font-size="12" fill="var(--mute)">'+wd(tr[0].date)+'</text><text x="'+(W-p)+'" y="'+(H-6)+'" font-size="12" fill="var(--mute)" text-anchor="end">'+wd(tr[tr.length-1].date)+'</text></svg>';
}
function show(i){
  var f=DATA.farms[i];sel=f.id;armed=null;
  Array.prototype.forEach.call(document.querySelectorAll("#list button"),function(b){b.setAttribute("aria-current",b.getAttribute("data-id")==String(f.id))});
  var l=lastOf(f),a=f.advice,h='';
  h+='<div class="row"><div><h2 style="margin:0">'+esc(f.name)+'</h2><div class="sub">'+esc(f.crop||"Crop not set")+(f.areaHa?", "+f.areaHa+" ha":"")+'</div></div><span class="pill" style="color:'+COL[lab(f)]+'">'+lab(f)+'</span></div>';
  h+='<div id="dmap"></div>';
  h+='<div class="adv" style="border-color:'+(ACOL[a.action]||"var(--mute)")+'"><b>'+esc(a.headline)+'</b>'+esc(a.detail)+(a.weekRainMm!=null?'<div class="sub" style="margin-top:4px">Next 7 days: rain about '+Math.round(a.weekRainMm)+' mm, crop water use about '+Math.round(a.weekEtMm)+' mm</div>':'')+'</div>';
  if(a.soil){var pc=a.soil.depletionPct;
    h+='<div class="sub" style="margin:10px 0 2px">Soil water used: <b>'+pc+'%</b> of the way to the irrigation trigger (about '+a.soil.rawMm+' mm usable before you irrigate)</div><div class="bar"><i style="width:'+Math.min(100,pc)+'%;background:'+(pc>=100?"var(--dry)":pc>=70?"var(--watch)":"var(--ok)")+'"></i></div>'+soilChart(a.soil.trajectory);
    var VL={ok:"matched your field",wetter:"said the field is wetter",drier:"said the field is drier"};
    h+='<div class="sub" style="margin-top:8px">Does this match your field?'+(f.feedback?' <i>You '+esc(VL[f.feedback.verdict]||"")+' on '+esc(f.feedback.date)+'.</i>':'')+'</div><button class="b alt sm" type="button" data-fb="ok">Yes</button><button class="b alt sm" type="button" data-fb="wetter">Wetter than this</button><button class="b alt sm" type="button" data-fb="drier">Drier than this</button>';
  }
  h+='<details class="why"><summary>Why this advice?</summary><p class="help" style="margin:6px 0 0">'+esc(a.why||"")+'</p></details>';
  if(f.forecast&&f.forecast.length){
    h+='<h3>7-day forecast</h3><div class="fc">'+f.forecast.map(function(d){return '<div><b>'+wd(d.date)+'</b>'+Math.round(d.rain)+' mm<br>'+Math.round(d.tmax)+'°/'+Math.round(d.tmin)+'°</div>'}).join("")+'</div>';
  }else h+='<p class="help">The weather forecast is unavailable right now.</p>';
  h+='<h3>Pest, disease and stress watch</h3>';
  h+=f.risks.length?f.risks.map(function(r){var c=r.level==="High"?"var(--dry)":r.level==="Info"?"var(--mute)":"var(--watch)";return '<div class="risk"><i style="color:'+c+'">'+esc(r.kind)+' ('+esc(r.level)+')</i><span>'+esc(r.text)+'</span></div>'}).join(""):'<p class="help" style="margin:4px 0 0">No warning signs right now.</p>';
  h+='<h3>Inside this field</h3>';
  if(f.zones&&f.zones.length){
    var FT={drier:"drier than the rest, inspect",wetter:"unusually wet",weak:"weak growth"},zs=f.zones.slice().sort(function(a,b){return a.ndmi-b.ndmi});
    h+='<p class="help" style="margin:0 0 4px">Latest image '+esc(f.zones[0].date)+'. The coloured patches on the map are these zones, driest first below.</p>'+
      zs.map(function(z){return '<div class="logrow"><span><b>'+esc(z.name)+'</b> '+z.status+', moisture '+z.ndmi.toFixed(2)+' ('+(z.anomaly>0?"+":"")+z.anomaly.toFixed(2)+' vs field median)'+(z.flags.length?' · <span style="color:var(--watch)">'+esc(z.flags.map(function(x){return FT[x]}).join(", "))+'</span>':'')+'</span>'+(z.flags.length?'<button class="b alt sm" type="button" style="margin:0" data-zlog="'+esc(z.name)+'">I checked it</button>':'')+'</div>'}).join("");
  }else h+='<p class="help" style="margin:0">'+((f.areaHa||0)>=2?"Zones appear after the next satellite update.":"Fields of 2 ha or more get a zone map that shows which part of the field needs attention.")+'</p>';
  if(f.forecast&&f.forecast.length)h+='<p class="help" style="margin:8px 0 0">'+(f.sprayDays.length?"Good spraying days (calm and dry): "+f.sprayDays.join(", ")+".":"No calm, dry spraying day in the next 5 days.")+'</p>';
  if(l){
    var prev=f.series.length>1?f.series[f.series.length-2]:l,d=l.ndmi-prev.ndmi;
    h+='<h3>Satellite readings</h3><div class="stats"><div><b>'+l.ndmi.toFixed(2)+'</b><span>Moisture index (NDMI)</span></div><div><b>'+(d>0?"+":"")+d.toFixed(2)+'</b><span>Since previous pass</span></div><div><b>'+(l.ndvi==null?"n/a":l.ndvi.toFixed(2))+'</b><span>Greenness (NDVI)</span></div><div><b>'+esc(ago(l.date))+'</b><span>Latest clear image</span></div></div>'+chart(f.series);
  }else h+='<p class="help">No clear satellite image yet. Tap Update satellite data. Passes happen about every 5 days and cloudy ones are skipped.</p>';
  h+='<h3>Field settings</h3><p class="help" style="margin:0 0 4px">These make the irrigation advice fit your field.</p><div class="two"><div><label for="sc">Crop</label><input id="sc" maxlength="60" value="'+esc(f.crop)+'"></div><div><label for="ss">Soil</label><select id="ss"><option value="">Loam (default)</option><option value="sandy">Sandy (drains fast)</option><option value="loam">Loam</option><option value="clay">Clay (holds water)</option></select></div></div><label for="sm">Irrigation method</label><select id="sm"><option value="">Not sure</option><option value="drip">Drip</option><option value="sprinkler">Sprinkler or pivot</option><option value="flood">Flood or furrow</option></select><button class="b alt sm" type="button" id="setSave">Save field settings</button>';
  var KL={irrigation:"Irrigated",spray:"Sprayed",scouting:"Scouted",other:"Other"},today=new Date().toISOString().slice(0,10);
  h+='<h3>What you did</h3><p class="help" style="margin:0 0 4px">Logging irrigation makes the advice smarter, and helps build your farm record.</p>'+
    '<div class="two"><div><label for="lk">Action</label><select id="lk"><option value="irrigation">Irrigated</option><option value="spray">Sprayed</option><option value="scouting">Scouted</option><option value="other">Other</option></select></div><div><label for="la">Amount (mm, if irrigated)</label><input id="la" type="number" step="1" min="0" inputmode="decimal"></div></div>'+
    '<div class="two"><div><label for="ld">Date</label><input id="ld" type="date" value="'+today+'"></div><div><label for="ln">Note</label><input id="ln" maxlength="200" placeholder="Optional"></div></div>'+
    '<button class="b" type="button" id="logAdd">Save to log</button>'+
    (f.logs&&f.logs.length?'<div style="margin-top:8px">'+f.logs.map(function(g){return '<div class="logrow"><span>'+esc(KL[g.kind]||g.kind)+(g.amount!=null?" "+g.amount+" mm":"")+", "+esc(g.date)+(g.note?" · "+esc(g.note):"")+'</span><button type="button" data-log="'+g.id+'" aria-label="Delete this log entry">×</button></div>'}).join("")+'</div>':'');
  h+='<button class="b danger" type="button" id="del">'+(armed===f.id?"Tap again to delete":"Delete farm")+'</button>';
  $("detail").innerHTML=h;drawDetailMap(f);
  $("ss").value=f.soil||"";$("sm").value=f.irrigation||"";
  $("setSave").addEventListener("click",async function(){
    try{await api("POST","farmsettings",{farmId:f.id,crop:$("sc").value,soil:$("ss").value,method:$("sm").value});say("Field settings saved.");await load()}catch(e){say(e.message,1)}
  });
  Array.prototype.forEach.call(document.querySelectorAll("[data-zlog]"),function(b){b.addEventListener("click",async function(){
    try{await api("POST","addlog",{farmId:f.id,kind:"scouting",date:new Date().toISOString().slice(0,10),note:"Checked zone "+b.getAttribute("data-zlog")});say("Logged. Thanks for checking zone "+b.getAttribute("data-zlog")+".");await load()}catch(e){say(e.message,1)}
  })});
  Array.prototype.forEach.call(document.querySelectorAll("[data-fb]"),function(b){b.addEventListener("click",async function(){
    try{await api("POST","feedback",{farmId:f.id,verdict:b.getAttribute("data-fb")});say("Thanks. Your answer is used to improve this field's advice.");await load()}catch(e){say(e.message,1)}
  })});
  $("logAdd").addEventListener("click",async function(){
    try{await api("POST","addlog",{farmId:f.id,kind:$("lk").value,amount:$("la").value,date:$("ld").value,note:$("ln").value});say("Saved to your log.");await load()}catch(e){say(e.message,1)}
  });
  Array.prototype.forEach.call(document.querySelectorAll("[data-log]"),function(b){b.addEventListener("click",async function(){
    try{await api("POST","dellog&id="+b.getAttribute("data-log"));await load()}catch(e){say(e.message,1)}
  })});
  $("del").addEventListener("click",async function(){
    if(armed!==f.id){armed=f.id;this.textContent="Tap again to delete";return}
    try{await api("POST","delfarm&id="+f.id);sel=null;say("Farm deleted.");await load()}catch(e){say(e.message,1)}
  });
}
function render(){
  TH=DATA.thresholds||TH;var farms=DATA.farms;
  var b=DATA.briefing;
  $("brief").innerHTML='<p style="margin:0"><b>'+esc(b.headline)+'</b></p>'+(b.items.length?'<ul class="brief">'+b.items.map(function(i){return '<li>'+esc(i.text)+'</li>'}).join("")+'</ul>':'');
  var c={Dry:0,Watch:0,Moist:0,"No data":0};farms.forEach(function(f){c[lab(f)]++});
  $("tiles").innerHTML=["Dry","Watch","Moist","No data"].map(function(k){return '<div class="tile"><b style="color:'+COL[k]+'">'+c[k]+'</b><span>'+k+'</span></div>'}).join("");
  var rank={Dry:0,Watch:1,Moist:2,"No data":3};
  ORDER=farms.map(function(f,i){return i}).sort(function(a,b){return rank[lab(farms[a])]-rank[lab(farms[b])]||farms[a].name.localeCompare(farms[b].name)});
  $("list").innerHTML=ORDER.length?ORDER.map(function(i){var f=farms[i],l=lastOf(f);return '<button class="item" type="button" data-id="'+f.id+'" data-i="'+i+'"><div class="row"><b>'+esc(f.name)+'</b><span class="pill" style="color:'+COL[lab(f)]+'">'+lab(f)+'</span></div><div class="sub">'+esc(f.crop||"Crop not set")+(f.areaHa?", "+f.areaHa+" ha":"")+(l?", "+esc(ago(l.date)):"")+'</div></button>'}).join(""):'<p class="help" style="padding:14px;margin:0">No farms yet. Tap Add a farm.</p>';
  Array.prototype.forEach.call(document.querySelectorAll("#list button"),function(btn){btn.addEventListener("click",function(){show(parseInt(btn.getAttribute("data-i"),10))})});
  if(!farms.length){$("detail").innerHTML='<h2>Welcome to Farm Watch</h2><p class="help" style="margin:0 0 6px">You will have your first advice in about two minutes:</p><ol class="steps"><li>Tap <b>Add a farm</b>, search for your village or town, switch the map to Satellite, and tap the corners of a field.</li><li>Tap <b>Save farm</b>. The 7-day forecast and irrigation advice appear straight away.</li><li>Tap <b>Update satellite data</b> to load the latest Sentinel-2 moisture readings. This can take up to a minute.</li><li>Come back each morning for your briefing, and log what you irrigate or spray.</li></ol>';return}
  var idx=ORDER[0];farms.forEach(function(f,i){if(f.id===sel)idx=i});show(idx);
}
async function load(){
  DATA=await api("GET","farms");render();
}
async function enter(){
  var me=await api("GET","me");INVITE=!!me.inviteRequired;
  if(!me.user){showAuth();return}
  $("auth").hidden=true;$("app").hidden=false;$("who").hidden=false;$("whoName").textContent=me.user.name||me.user.email;
  $("emailPref").checked=!!me.user.emailBriefing;
  await load();
}
$("emailPref").addEventListener("change",async function(){try{await api("POST","prefs",{emailBriefing:this.checked});say("Saved.")}catch(e){say(e.message,1)}});
$("testMail").addEventListener("click",async function(){try{await api("POST","testmail");say("Test email sent. Check your inbox and spam folder.")}catch(e){say(e.message,1)}});
$("fetch").addEventListener("click",async function(){
  var b=this;b.disabled=true;say("Checking Sentinel-2 and the forecast. This can take up to a minute.");
  try{var r=await api("POST","fetch");await load();say(r.stored+" new satellite reading(s) stored. "+(r.messages||[]).slice(0,3).join(" "))}catch(e){say(e.message,1)}
  b.disabled=false;
});

/* ---------- add a farm: tap corners on the map ---------- */
function areaHa(p){if(p.length<3)return 0;var lat0=p.reduce(function(a,q){return a+q[0]},0)/p.length,kx=111320*Math.cos(lat0*Math.PI/180),ky=110540,xy=p.map(function(q){return [q[1]*kx,q[0]*ky]}),t=0;for(var i=0;i<xy.length;i++){var a=xy[i],b=xy[(i+1)%xy.length];t+=a[0]*b[1]-b[0]*a[1]}return Math.abs(t)/2/10000}
function redraw(){
  if(!amap)return;
  if(poly){amap.removeLayer(poly);poly=null}
  dots.forEach(function(d){amap.removeLayer(d)});dots=[];
  if(pts.length>=2)poly=L.polygon(pts,{color:"#1f6fb5",weight:2,fillOpacity:0.2}).addTo(amap);
  dots=pts.map(function(p){return L.circleMarker(p,{radius:6,color:"#fff",weight:2,fillColor:"#1f6fb5",fillOpacity:1}).addTo(amap)});
  $("area").textContent=pts.length<3?(pts.length+" corner"+(pts.length===1?"":"s")+" so far. A farm needs at least 3."):(pts.length+" corners, about "+areaHa(pts).toFixed(1)+" ha");
}
function initAddMap(){
  if(amap){amap.invalidateSize();return}
  if(typeof L==="undefined"){$("map").textContent="The map could not load. Check your connection and reload.";return}
  amap=L.map("map").setView([20,0],2);
  var sat=L.tileLayer(SAT,{maxZoom:19,attribution:"Tiles &copy; Esri"}),osm=L.tileLayer(OSM,{maxZoom:19,attribution:"&copy; OpenStreetMap contributors"});
  sat.addTo(amap);L.control.layers({"Satellite":sat,"Map":osm}).addTo(amap);
  amap.on("click",function(e){pts.push([e.latlng.lat,e.latlng.lng]);redraw()});
  amap.on("locationerror",function(){say("Could not get your location. Search for a place instead.",1)});
  redraw();
}
$("addToggle").addEventListener("click",function(){var p=$("addPanel");p.hidden=!p.hidden;if(!p.hidden){initAddMap();p.scrollIntoView({behavior:"smooth",block:"start"})}});
$("undo").addEventListener("click",function(){pts.pop();redraw()});
$("clear").addEventListener("click",function(){pts=[];redraw()});
$("loc").addEventListener("click",function(){if(amap)amap.locate({setView:true,maxZoom:17})});
async function search(){
  var q=$("q").value.trim();if(!q||!amap)return;
  try{var r=await fetch("https://nominatim.openstreetmap.org/search?format=json&limit=1&q="+encodeURIComponent(q));var j=await r.json();
    if(!j.length)return say("Place not found. Try a nearby town.",1);amap.setView([parseFloat(j[0].lat),parseFloat(j[0].lon)],16);say("")}
  catch(e){say("Search is unavailable right now.",1)}
}
$("go").addEventListener("click",search);
$("q").addEventListener("keydown",function(e){if(e.key==="Enter")search()});
$("save").addEventListener("click",async function(){
  if(pts.length<3)return say("Tap at least 3 corners on the map first.",1);
  var ring=pts.map(function(p){return [p[1],p[0]]});ring.push(ring[0]);
  var b=this;b.disabled=true;
  try{
    var r=await api("POST","addfarm",{name:$("fn").value,crop:$("fc").value,geometry:{type:"Polygon",coordinates:[ring]}});
    say("Added the farm ("+r.areaHa+" ha). Tap Update satellite data to load its first readings.");
    $("fn").value="";$("fc").value="";pts=[];redraw();$("addPanel").hidden=true;sel=r.id;await load();
  }catch(e){say(e.message,1)}
  b.disabled=false;
});

if(RESET){mode="reset";api("GET","me").then(function(m){INVITE=!!m.inviteRequired}).catch(function(){}).then(showAuth)}
else enter().catch(function(e){say("Could not load Farm Watch. "+e.message,1)});
})();
</script>
</body>
</html>
"""


# ---------- web handler ----------

class handler(BaseHTTPRequestHandler):
    def _send(self, code, body, ctype="application/json", extra=None):
        if not isinstance(body, bytes):
            body = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "same-origin")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _json(self, code, obj, cookie=None):
        extra = {"Cache-Control": "no-store"}
        if cookie is not None:
            extra["Set-Cookie"] = cookie
        self._send(code, obj, extra=extra)

    def _query(self):
        return {k: v[0] for k, v in parse_qs(urlparse(self.path).query).items()}

    def _bearer(self):
        auth = self.headers.get("Authorization", "")
        return auth[7:] if auth.startswith("Bearer ") else ""

    @staticmethod
    def _same(a, b):
        return bool(b) and hmac.compare_digest(a.encode(), b.encode())

    def _can_cron(self):
        b = self._bearer()
        return self._same(b, CRON_SECRET) or self._same(b, ADMIN_TOKEN)

    def _session_cookie(self, token, clear=False):
        parts = [f"fw_session={'' if clear else token}", "HttpOnly", "SameSite=Lax", "Path=/",
                 "Max-Age=0" if clear else f"Max-Age={SESSION_DAYS * 86400}"]
        if self.headers.get("X-Forwarded-Proto", "").split(",")[0].strip() == "https":
            parts.append("Secure")
        return "; ".join(parts)

    def _user(self):
        for part in self.headers.get("Cookie", "").split(";"):
            k, _, v = part.strip().partition("=")
            if k == "fw_session":
                uid = read_session(v)
                return get_user(uid) if uid else None
        return None

    def _base_url(self):
        env = os.environ.get("APP_URL") or os.environ.get("RENDER_EXTERNAL_URL")
        if env:
            return env.rstrip("/")
        proto = self.headers.get("X-Forwarded-Proto", "http").split(",")[0].strip()
        return f"{proto}://{self.headers.get('Host', 'localhost')}"

    def _read_json(self):
        if "application/json" not in self.headers.get("Content-Type", ""):
            raise ValueError("Unsupported request.")
        n = int(self.headers.get("Content-Length") or 0)
        if n > 200_000:
            raise ValueError("Request too large.")
        return json.loads(self.rfile.read(n) or b"{}")

    def _fail(self, e):
        traceback.print_exc(file=sys.stderr)
        self._json(500, {"error": str(e) if isinstance(e, ConfigError) else "Something went wrong. Please try again."})

    def do_GET(self):
        r = self._query().get("r", "")
        try:
            if r in ("", "app"):
                return self._send(200, APP_HTML.encode("utf-8"), "text/html; charset=utf-8", {"Cache-Control": "no-cache"})
            if r == "health":
                return self._json(200, {"ok": True})
            if r == "cron":
                if not self._can_cron():
                    return self._json(401, {"error": "Not allowed."})
                return self._json(200, run_daily())
            ensure_schema()
            user = self._user()
            if r == "me":
                return self._json(200, {"user": user, "inviteRequired": bool(INVITE_CODE)})
            if r == "farms":
                if not user:
                    return self._json(401, {"error": "Please log in."})
                return self._json(200, farms_payload(user["id"]))
            self._json(404, {"error": "not found"})
        except Exception as e:
            self._fail(e)

    def do_POST(self):
        r = self._query().get("r", "")
        try:
            data = self._read_json()
            ensure_schema()
            if r == "signup":
                uid = signup(data.get("email"), data.get("name"), data.get("password"), data.get("invite"))
                return self._json(201, {"user": get_user(uid)}, self._session_cookie(make_session(uid)))
            if r == "login":
                uid = login(data.get("email"), data.get("password"))
                return self._json(200, {"user": get_user(uid)}, self._session_cookie(make_session(uid)))
            if r == "logout":
                return self._json(200, {"ok": True}, self._session_cookie("", clear=True))
            if r == "forgot":
                configured = bool(os.environ.get("SMTP_HOST"))
                if configured:
                    try:
                        start_reset(data.get("email"), self._base_url())
                    except Exception as e:
                        print("Reset email failed:", e, file=sys.stderr)
                return self._json(200, {"ok": True, "emailConfigured": configured})
            if r == "reset":
                finish_reset(data.get("token"), data.get("password"))
                return self._json(200, {"ok": True})
            user = self._user()
            if not user:
                return self._json(401, {"error": "Please log in."})
            if r == "addfarm":
                name = (data.get("name") or "").strip()
                if not name:
                    raise ValueError("Give the farm a name.")
                farm_id, ha = insert_farm(user["id"], name, data.get("crop"), data.get("geometry"))
                try:
                    f = sql("SELECT lat, lon FROM fw_farms WHERE id=$1", (farm_id,))[0]
                    get_forecast(farm_id, _f(f["lat"]), _f(f["lon"]))
                except Exception as e:
                    print("First forecast failed:", e, file=sys.stderr)
                return self._json(201, {"id": farm_id, "areaHa": ha})
            if r == "delfarm":
                fid = self._query().get("id", "")
                if not fid.isdigit():
                    raise ValueError("Missing farm id.")
                delete_farm(user["id"], int(fid))
                return self._json(200, {"deleted": True})
            if r == "fetch":
                return self._json(200, run_user_fetch(user["id"]))
            if r == "addlog":
                lid = add_log(user["id"], int(data.get("farmId") or 0), data.get("kind"), data.get("date"),
                              data.get("amount"), data.get("note"))
                return self._json(201, {"id": lid})
            if r == "dellog":
                lid = self._query().get("id", "")
                if not lid.isdigit():
                    raise ValueError("Missing log id.")
                delete_log(user["id"], int(lid))
                return self._json(200, {"deleted": True})
            if r == "farmsettings":
                update_settings(user["id"], int(data.get("farmId") or 0), data.get("crop"), data.get("soil"), data.get("method"))
                return self._json(200, {"ok": True})
            if r == "feedback":
                add_feedback(user["id"], int(data.get("farmId") or 0), data.get("verdict"), data.get("note"))
                return self._json(201, {"ok": True})
            if r == "testmail":
                if not os.environ.get("SMTP_HOST"):
                    raise ValueError("Email is not set up on the server yet. Add SMTP_HOST, SMTP_USER and SMTP_PASS in the hosting settings.")
                try:
                    send_mail(user["email"], "Farm Watch test email", "This is a test from Farm Watch. Email is working.")
                except Exception as e:
                    raise ValueError(f"The email server refused the message: {e}")
                return self._json(200, {"ok": True})
            if r == "prefs":
                sql("UPDATE fw_users SET email_briefing=$1 WHERE id=$2", (1 if data.get("emailBriefing") else 0, user["id"]))
                return self._json(200, {"ok": True})
            self._json(404, {"error": "not found"})
        except (ValueError, json.JSONDecodeError) as e:
            self._json(400, {"error": str(e)})
        except Exception as e:
            self._fail(e)

    def log_message(self, *args):
        pass


# ---------- run as a normal web server (Render and similar hosts) ----------

if __name__ == "__main__":
    from http.server import ThreadingHTTPServer
    port = int(os.environ.get("PORT", "8000"))
    print(f"Farm Watch running on port {port}", flush=True)
    ThreadingHTTPServer(("0.0.0.0", port), handler).serve_forever()
