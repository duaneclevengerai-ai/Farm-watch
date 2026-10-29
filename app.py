"""
Farm Watch: a complete farm monitoring website in one file (Python, no extra packages).
Runs on Render (python app.py) or Vercel (api/index.py).

What it does
  - People create accounts and log in. Each person sees only their own farms.
  - Farmers add a farm by tapping its corners on a satellite map.
  - Every day it fetches Copernicus Sentinel-2 readings (moisture index NDMI, vegetation index NDVI),
    skipping cloudy passes, and fetches a 7-day weather forecast for each farm.
  - Each field gets a satellite moisture heat map (about 10-20 m pixels), a "right now" weather panel, a day-by-day
    irrigation calendar for the week, and a portfolio card, Today's irrigation plan, with water volume and pump hours.
  - AQAS Pro control room (/?r=aqas): simulated, approval-only agents (ARAIAH, Pluto, Orion), a proposal queue,
    an audit trail, and a live Farm Watch health panel. Phase 1 never takes live actions.
  - An almanac per field (sunrise, sunset, moon, frost dates and season length from local weather history, planting
    windows, typical climate), an AI crop advisor you can talk to and send photos, and labor and hours tracking.
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
  ANTHROPIC_API_KEY    optional; switches on the AI crop advisor with photos (or GEMINI_API_KEY for Google Gemini)
  ANTHROPIC_MODEL, GEMINI_MODEL, AI_DAILY_LIMIT   optional AI settings (default 20 questions per person per day)
  AQAS_ADMIN_TOKEN     password for the AQAS control room at /?r=aqas (use a separate long random secret)
  OPENAI_API_KEY       optional; switches on the AI crop advisor with GPT (OPENAI_MODEL, default gpt-4.1-mini).
                       AI_PROVIDER can pick anthropic, openai or gemini when more than one key is set.
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
FORECAST_TTL_S = 3600
PBKDF2_ITERS = 200_000
RESET_TTL_S = 3600
LOG_KINDS = ("irrigation", "spray", "scouting", "other")
SESSION_DAYS = 30
AQAS_ADMIN_TOKEN = os.environ.get("AQAS_ADMIN_TOKEN", "").strip()
_AQAS_READY = False

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
            sql("ALTER TABLE fw_farms ADD COLUMN IF NOT EXISTS flow_m3h DOUBLE PRECISION")
            sql("""CREATE TABLE IF NOT EXISTS fw_maps (
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                kind TEXT NOT NULL, date TEXT NOT NULL, bbox TEXT NOT NULL, png TEXT NOT NULL,
                PRIMARY KEY (farm_id, kind))""")
            sql("""CREATE TABLE IF NOT EXISTS fw_feedback (
                id SERIAL PRIMARY KEY,
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                date TEXT NOT NULL, verdict TEXT NOT NULL, note TEXT, snapshot TEXT)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_zone_readings (
                farm_id INTEGER NOT NULL REFERENCES fw_farms(id) ON DELETE CASCADE,
                zone INTEGER NOT NULL, date TEXT NOT NULL, ndmi DOUBLE PRECISION NOT NULL,
                ndvi DOUBLE PRECISION, clear_fraction DOUBLE PRECISION,
                PRIMARY KEY (farm_id, zone, date))""")
            sql("""CREATE TABLE IF NOT EXISTS fw_climate (
                farm_id INTEGER PRIMARY KEY REFERENCES fw_farms(id) ON DELETE CASCADE,
                fetched TEXT NOT NULL, data TEXT NOT NULL)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_workers (
                id SERIAL PRIMARY KEY,
                user_id INTEGER NOT NULL REFERENCES fw_users(id) ON DELETE CASCADE,
                name TEXT NOT NULL, role TEXT, rate DOUBLE PRECISION, active INTEGER NOT NULL DEFAULT 1)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_labor (
                id SERIAL PRIMARY KEY,
                worker_id INTEGER NOT NULL REFERENCES fw_workers(id) ON DELETE CASCADE,
                farm_id INTEGER REFERENCES fw_farms(id) ON DELETE SET NULL,
                task TEXT, start_ts TEXT NOT NULL, end_ts TEXT, hours DOUBLE PRECISION,
                units DOUBLE PRECISION, piece_rate DOUBLE PRECISION, note TEXT)""")
            sql("""CREATE TABLE IF NOT EXISTS fw_chats (
                id SERIAL PRIMARY KEY,
                user_id INTEGER NOT NULL REFERENCES fw_users(id) ON DELETE CASCADE,
                farm_id INTEGER REFERENCES fw_farms(id) ON DELETE CASCADE,
                question TEXT NOT NULL, answer TEXT NOT NULL, had_image INTEGER NOT NULL DEFAULT 0, created TEXT NOT NULL)""")
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


def update_settings(user_id, farm_id, crop, soil, method, flow=None):
    if soil and soil not in SOILS:
        raise ValueError("Choose a soil type from the list.")
    if method and method not in METHODS:
        raise ValueError("Choose an irrigation method from the list.")
    if not sql("SELECT id FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id)):
        raise ValueError("Farm not found.")
    fl = None
    if flow not in (None, ""):
        try:
            fl = float(flow)
        except (TypeError, ValueError):
            raise ValueError("Flow must be a number of cubic metres per hour.")
        if not 0 < fl <= 100000:
            raise ValueError("Flow must be between 0 and 100000 cubic metres per hour.")
    sql("UPDATE fw_farms SET crop=$1, soil=$2, irrigation=$3, flow_m3h=$4 WHERE id=$5 AND user_id=$6",
        ((crop or "").strip()[:60], soil or "", method or "", fl, farm_id, user_id))


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
    basic = "temperature_2m,relative_humidity_2m,precipitation,wind_speed_10m,wind_gusts_10m"
    variants = [basic + ",soil_temperature_6cm", basic, None]  # fall back if the service rejects an extra variable
    data = None
    for i, cur_vars in enumerate(variants):
        qq = dict(q)
        if cur_vars:
            qq["current"] = cur_vars
        try:
            with urlopen(Request(base + "?" + urlencode(qq), headers={"User-Agent": "FarmWatch/1.0"}), timeout=20) as r:
                data = json.loads(r.read())
            break
        except HTTPError as e:
            if e.code != 400 or i == len(variants) - 1:
                raise
    d = data["daily"]
    days = []
    for i, t_ in enumerate(d["time"]):
        days.append({"date": t_, "tmax": _f(d["temperature_2m_max"][i]), "tmin": _f(d["temperature_2m_min"][i]),
                     "rain": _f(d["precipitation_sum"][i]) or 0.0, "rainHours": _f(d["precipitation_hours"][i]) or 0.0,
                     "et0": _f(d["et0_fao_evapotranspiration"][i]) or 0.0, "wind": _f(d["wind_speed_10m_max"][i]) or 0.0})
    cur = data.get("current") or {}
    now = {"temp": _f(cur.get("temperature_2m")), "humidity": _f(cur.get("relative_humidity_2m")),
           "rain": _f(cur.get("precipitation")), "wind": _f(cur.get("wind_speed_10m")),
           "gusts": _f(cur.get("wind_gusts_10m")), "soil": _f(cur.get("soil_temperature_6cm")),
           "time": cur.get("time"), "utc": data.get("utc_offset_seconds")}
    return days, now


def _parse_weather(raw):
    d = json.loads(raw)
    return (d["days"], d.get("now")) if isinstance(d, dict) else (d, None)


def get_weather(farm_id, lat, lon, force=False):
    """Forecast days (past 10 + next 7) and current conditions, cached for an hour."""
    rows = sql("SELECT fetched, data FROM fw_forecasts WHERE farm_id=$1", (farm_id,))
    if rows and not force:
        try:
            if time.time() - datetime.fromisoformat(rows[0]["fetched"]).timestamp() < FORECAST_TTL_S:
                return _parse_weather(rows[0]["data"])
        except ValueError:
            pass
    try:
        res = fetch_forecast_remote(lat, lon)
        days, now = res if isinstance(res, tuple) else (res, None)
        sql("INSERT INTO fw_forecasts (farm_id, fetched, data) VALUES ($1,$2,$3) "
            "ON CONFLICT (farm_id) DO UPDATE SET fetched = EXCLUDED.fetched, data = EXCLUDED.data",
            (farm_id, datetime.now(timezone.utc).isoformat(timespec="seconds"), json.dumps({"days": days, "now": now})))
        return days, now
    except Exception as e:
        print("Forecast failed:", e, file=sys.stderr)
        return _parse_weather(rows[0]["data"]) if rows else (None, None)


def get_forecast(farm_id, lat, lon, force=False):
    return get_weather(farm_id, lat, lon, force)[0]


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


def _gross(net, eff):
    return 5 * max(1, round(min(net, MAX_SINGLE_NET) / eff / 5))


def schedule_events(wb, now_dr, fut):
    """Day-by-day irrigation plan for the week: irrigate when the soil reaches the trigger, skip heavy-rain days,
    and follow a big refill with extra passes on the next days (each pass is capped at a realistic depth)."""
    raw, taw, eff, kc = wb["raw"], wb["taw"], wb["eff"], wb["kc"]
    clamp = lambda v: max(0.0, min(taw, v))
    dr, events, more = now_dr, [], 0

    def irrigate(d):
        nonlocal dr, more
        net = min(dr, MAX_SINGLE_NET)
        events.append({"date": d["date"], "mm": _gross(net, eff), "netMm": round(net)})
        dr -= net
        more = 2 if dr > 15 else 0  # still well below full: plan up to two follow-up passes

    for i, d in enumerate(fut):
        calm = d["rain"] < 10
        if more and calm and dr > 15:
            irrigate(d)
            more = max(0, more - 1) if dr > 15 else 0
        elif i == 0 and dr >= raw and calm:
            irrigate(d)
        rain = 0.8 * min(d["rain"], 25) if d["rain"] >= 2 else 0.0
        ks = 1.0 if dr <= raw or taw <= raw else max(0.1, (taw - dr) / (taw - raw))
        dr = clamp(dr - rain + kc * d["et0"] * ks)
        if dr >= raw and calm and not (events and events[-1]["date"] == d["date"]):
            irrigate(d)
    return events


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
    gross = lambda net: _gross(net, eff)  # one application, capped at a realistic depth
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
    res["applyMm"] = gross(now_dr) if now_dr >= raw else (gross(trigger["dr"]) if trigger else None)
    res["calendar"] = schedule_events(wb, now_dr, fut)
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
        spray = [wd(d["date"]) for d in days[:5] if d["wind"] < 15 and d["rain"] < 1
                 and (d["tmin"] is None or d["tmin"] > 1) and (d["tmax"] is None or d["tmax"] < 32)]
    return flags, spray


def farm_view(f, readings, days, logs=(), feedback=(), zone_rows=(), now=None, map_meta=None):
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
            "soil": f.get("soil") or "", "irrigation": f.get("irrigation") or "", "flow": _f(f.get("flow_m3h")),
            "now": now,
            "map": ({"date": map_meta["date"], "bbox": json.loads(map_meta["bbox"]),
                     "url": f"/api/index?r=map&id={int(f['id'])}&v={map_meta['date']}"} if map_meta else None),
            "geometry": json.loads(f["geometry"]), "series": readings, "status": status,
            "forecast": fut, "advice": advice, "zones": zones,
            "feedback": feedback[0] if feedback else None, "logs": list(logs)[:15],
            "risks": flags, "sprayDays": spray}


def build_plan(views):
    """Today's irrigation plan across all of a person's fields, with water volume and pump hours."""
    today, soon = [], []
    for v in views:
        a = v["advice"]
        if a["action"] not in ("Irrigate", "Plan") or not a.get("applyMm"):
            continue
        ha = v.get("areaHa") or 0
        m3 = a["applyMm"] * ha * 10  # 1 mm of water over 1 ha is 10 cubic metres
        item = {"farmId": v["id"], "name": v["name"], "crop": v["crop"], "headline": a["headline"], "mm": a["applyMm"],
                "m3": round(m3), "hours": round(m3 / v["flow"], 1) if v.get("flow") else None,
                "pct": (a.get("soil") or {}).get("depletionPct") or 0}
        (today if a["action"] == "Irrigate" else soon).append(item)
    today.sort(key=lambda i: -i["pct"])
    hrs = [i["hours"] for i in today if i["hours"] is not None]
    return {"today": today, "soon": soon, "totalM3": sum(i["m3"] for i in today),
            "totalHours": round(sum(hrs), 1) if hrs else None}


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
    farms = sql("SELECT id, name, crop, area_ha, lat, lon, geometry, soil, irrigation, flow_m3h FROM fw_farms WHERE user_id=$1 ORDER BY name", (user_id,))
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
        weather = list(pool.map(lambda f: get_weather(int(f["id"]), _f(f["lat"]), _f(f["lon"])), farms))
    maps = {int(m["farm_id"]): m for m in sql(
        "SELECT farm_id, date, bbox FROM fw_maps WHERE kind=$2 AND farm_id IN (SELECT id FROM fw_farms WHERE user_id=$1)",
        (user_id, "ndmi"))}
    views = [farm_view(f, by.get(int(f["id"]), []), w[0], logs_by.get(int(f["id"]), []), fb_by.get(int(f["id"]), []),
                       zr_by.get(int(f["id"]), []), w[1], maps.get(int(f["id"])))
             for f, w in zip(farms, weather)]
    return {"farms": views, "briefing": build_briefing(views), "plan": build_plan(views),
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


MAP_EVALSCRIPT = """
//VERSION=3
function setup() {
  return {input: [{bands: ["B8A", "B11", "SCL", "dataMask"]}], output: {bands: 4}};
}
var stops = [[-0.10, [0.55, 0.15, 0.10]], [0.05, [0.85, 0.45, 0.12]], [0.15, [0.95, 0.85, 0.25]],
             [0.28, [0.45, 0.75, 0.35]], [0.45, [0.12, 0.40, 0.80]]];
function ramp(v) {
  if (v <= stops[0][0]) return stops[0][1];
  for (var i = 1; i < stops.length; i++) {
    if (v <= stops[i][0]) {
      var t = (v - stops[i - 1][0]) / (stops[i][0] - stops[i - 1][0]);
      return [0, 1, 2].map(function (k) { return stops[i - 1][1][k] + t * (stops[i][1][k] - stops[i - 1][1][k]); });
    }
  }
  return stops[stops.length - 1][1];
}
function evaluatePixel(s) {
  var bad = [0, 1, 3, 8, 9, 10, 11].indexOf(s.SCL) !== -1;
  var c = ramp((s.B8A - s.B11) / (s.B8A + s.B11));
  return [c[0], c[1], c[2], (s.dataMask === 1 && !bad) ? 0.85 : 0];
}
"""


def request_map_png(token, payload):
    req = Request("https://sh.dataspace.copernicus.eu/api/v1/process", data=json.dumps(payload).encode(), method="POST",
                  headers={"Content-Type": "application/json", "Accept": "image/png", "Authorization": f"Bearer {token}"})
    try:
        with urlopen(req, timeout=120) as r:
            return r.read()
    except HTTPError as e:
        raise RuntimeError(f"Copernicus map error {e.code}: " + e.read().decode("utf-8", "replace")[:150])


def fetch_map(token, farm, d):
    """Store a colour moisture map (NDMI) of the field for one image date. Returns True if saved."""
    geom = json.loads(farm["geometry"])
    ring = geom["coordinates"][0]
    xs, ys = [p[0] for p in ring], [p[1] for p in ring]
    xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
    res = max(RES_DEG, max(xmax - xmin, ymax - ymin) / 400)
    w, h = max(8, math.ceil((xmax - xmin) / res)), max(8, math.ceil((ymax - ymin) / res))
    day = date.fromisoformat(d)
    payload = {
        "input": {"bounds": {"bbox": [xmin, ymin, xmax, ymax], "geometry": geom,
                             "properties": {"crs": "http://www.opengis.net/def/crs/EPSG/0/4326"}},
                  "data": [{"type": "sentinel-2-l2a", "dataFilter": {
                      "timeRange": {"from": f"{d}T00:00:00Z", "to": f"{day + timedelta(days=1)}T00:00:00Z"},
                      "mosaickingOrder": "leastCC"}}]},
        "output": {"width": w, "height": h, "responses": [{"identifier": "default", "format": {"type": "image/png"}}]},
        "evalscript": MAP_EVALSCRIPT,
    }
    png = request_map_png(token, payload)
    if not png or png[:4] != b"\x89PNG":
        return False
    sql("INSERT INTO fw_maps (farm_id, kind, date, bbox, png) VALUES ($1,$2,$3,$4,$5) "
        "ON CONFLICT (farm_id, kind) DO UPDATE SET date = EXCLUDED.date, bbox = EXCLUDED.bbox, png = EXCLUDED.png",
        (int(farm["id"]), "ndmi", d, json.dumps([xmin, ymin, xmax, ymax]), base64.b64encode(png).decode()))
    return True


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

    map_have = {int(r["farm_id"]): r["date"] for r in sql(
        f"SELECT farm_id, date FROM fw_maps WHERE kind='ndmi' AND farm_id IN ({ids})")}

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
            if latest and latest > map_have.get(fid, ""):
                try:
                    if fetch_map(token, farm, latest):
                        msgs.append("updated the moisture map")
                except Exception as e:
                    msgs.append(f"map failed ({e})")
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
    aqas_log_daily(result)
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


# ---------- almanac: sun, moon, frost dates, planting windows, climate normals ----------

CLIMATE_YEARS = 10
CLIMATE_TTL_DAYS = 180
SYNODIC = 29.530588853
NEW_MOON_EPOCH = datetime(2000, 1, 6, 18, 14, tzinfo=timezone.utc)
MOON_NAMES = ["New moon", "Waxing crescent", "First quarter", "Waxing gibbous", "Full moon", "Waning gibbous",
              "Last quarter", "Waning crescent"]
MONTH_NAMES = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

# crop keyword, display name, spring window (days from the typical last frost), autumn window (days from the typical
# first frost), note. These are common rule-of-thumb guidelines, not local advice.
PLANTING = [
    ("wheat", "Wheat", (-35, -10), (-60, -35), "Winter wheat is sown in autumn, spring wheat as soon as the soil can be worked."),
    ("barley", "Barley", (-35, -10), (-55, -35), "Sow spring barley as soon as the soil can be worked."),
    ("maize", "Maize", (0, 14), None, "Wait until the soil is at least 10°C."),
    ("corn", "Maize", (0, 14), None, "Wait until the soil is at least 10°C."),
    ("soy", "Soybean", (7, 28), None, "Soil should be at least 12°C."),
    ("bean", "Beans", (7, 28), None, "Soil should be at least 15°C. Beans do not tolerate frost."),
    ("pumpkin", "Pumpkin and squash", (7, 21), None, "Soil should be at least 15°C. Allow 90 to 120 days to mature before the first frost."),
    ("squash", "Squash", (7, 21), None, "Soil should be at least 15°C."),
    ("cucumber", "Cucumber", (7, 21), None, "Frost-tender. Soil should be at least 16°C."),
    ("tomato", "Tomato (transplants)", (7, 21), None, "Frost-tender. Harden off seedlings first."),
    ("potato", "Potato", (-28, -7), None, "Plant when the soil is workable and at least 7°C."),
    ("lettuce", "Lettuce", (-42, 7), (-75, -40), "A cool-season crop. Heat makes it bolt."),
    ("pea", "Peas", (-42, -14), None, "Tolerates light frost."),
    ("carrot", "Carrot", (-21, 7), (-85, -60), "Needs a fine, moist seedbed."),
    ("onion", "Onion", (-42, -14), None, "Sets and transplants go in early."),
    ("cotton", "Cotton", (14, 35), None, "Soil should be at least 18°C."),
    ("rice", "Rice", (7, 28), None, "Needs warm water and soil."),
    ("sunflower", "Sunflower", (0, 21), None, "Soil should be at least 8 to 10°C."),
    ("alfalfa", "Alfalfa", (-21, 7), (-60, -35), "Late-summer sowings need time to establish before winter."),
]
PERENNIAL_WORDS = ("grape", "vine", "olive", "almond", "citrus", "orange", "lemon", "apple", "berry", "orchard")


def moon_info(now=None):
    now = now or datetime.now(timezone.utc)
    p = (((now - NEW_MOON_EPOCH).total_seconds() / 86400) / SYNODIC) % 1
    return {"phase": MOON_NAMES[int(p * 8 + 0.5) % 8], "illumination": round((1 - math.cos(2 * math.pi * p)) / 2 * 100),
            "waxing": p < 0.5,
            "nextFull": (now + timedelta(days=((0.5 - p) % 1) * SYNODIC)).date().isoformat(),
            "nextNew": (now + timedelta(days=((1 - p) % 1) * SYNODIC)).date().isoformat()}


def sun_times(d, lat, lon, utc_offset_s=None):
    """Sunrise, sunset and day length from the standard NOAA solar equations."""
    g = 2 * math.pi / 365 * (d.timetuple().tm_yday - 1 + 0.5)
    eqt = 229.18 * (0.000075 + 0.001868 * math.cos(g) - 0.032077 * math.sin(g)
                    - 0.014615 * math.cos(2 * g) - 0.040849 * math.sin(2 * g))
    decl = (0.006918 - 0.399912 * math.cos(g) + 0.070257 * math.sin(g) - 0.006758 * math.cos(2 * g)
            + 0.000907 * math.sin(2 * g) - 0.002697 * math.cos(3 * g) + 0.00148 * math.sin(3 * g))
    la = math.radians(max(-89.5, min(89.5, lat)))
    c = math.cos(math.radians(90.833)) / (math.cos(la) * math.cos(decl)) - math.tan(la) * math.tan(decl)
    if c >= 1:
        return {"dayLengthMin": 0, "sunrise": None, "sunset": None, "polar": "polar night"}
    if c <= -1:
        return {"dayLengthMin": 1440, "sunrise": None, "sunset": None, "polar": "midnight sun"}
    ha = math.degrees(math.acos(c))
    rise, sset = 720 - 4 * (lon + ha) - eqt, 720 - 4 * (lon - ha) - eqt
    fmt = lambda mins: None if utc_offset_s is None else "%02d:%02d" % divmod(int(round(mins + utc_offset_s / 60)) % 1440, 60)
    return {"dayLengthMin": round(8 * ha), "sunrise": fmt(rise), "sunset": fmt(sset), "polar": None}


def _doy_date(year, doy):
    d = date(2001, 1, 1) + timedelta(days=int(doy) - 1)
    return date(year, d.month, d.day)


def _pct(vals, p):
    s = sorted(vals)
    return s[min(len(s) - 1, max(0, math.ceil(p * len(s)) - 1))]


def climate_stats(daily, lat):
    """Frost dates and monthly normals from several years of daily weather history."""
    by_year, month_rain = {}, {}
    month_tmax, month_tmin = {m: [] for m in range(1, 13)}, {m: [] for m in range(1, 13)}
    for i, ts in enumerate(daily["time"]):
        y, mo, dd = int(ts[:4]), int(ts[5:7]), int(ts[8:10])
        if mo == 2 and dd == 29:
            dd = 28
        doy = (date(2001, mo, dd) - date(2001, 1, 1)).days + 1
        tn, tx, rn = daily["temperature_2m_min"][i], daily["temperature_2m_max"][i], daily["precipitation_sum"][i]
        by_year.setdefault(y, []).append((mo, doy, tn))
        if tn is not None:
            month_tmin[mo].append(tn)
        if tx is not None:
            month_tmax[mo].append(tx)
        if rn is not None:
            month_rain.setdefault((y, mo), []).append(rn)
    last, first = [], []
    for y, rows in by_year.items():
        if len(rows) < 330:
            continue
        frost = [(mo, doy) for mo, doy, tn in rows if tn is not None and tn <= 0]
        if not frost:
            continue
        if lat >= 0:
            sp = [doy for mo, doy in frost if mo <= 7]
            au = [doy for mo, doy in frost if mo >= 8]
            if sp:
                last.append(max(sp))
            if au:
                first.append(min(au))
        else:
            last.append(max(doy for mo, doy in frost))
            first.append(min(doy for mo, doy in frost))
    frost_info = None
    if len(last) >= 3 and len(first) >= 3:
        both = min(len(last), len(first))
        span = ([f - l for l, f in zip(sorted(last), sorted(first))] if lat >= 0
                else [365 - l + f for l, f in zip(sorted(last), sorted(first))])
        frost_info = {"last": int(statistics.median(last)), "lastSafe90": int(_pct(last, 0.9)),
                      "first": int(statistics.median(first)), "firstEarly10": int(_pct(first, 0.1)),
                      "frostFreeDays": int(statistics.median(span)) if both else None}
    normals = {}
    for m in range(1, 13):
        totals = [sum(v) for (y, mm), v in month_rain.items() if mm == m and len(v) >= 25]
        if month_tmax[m] and month_tmin[m]:
            normals[m] = {"tmax": round(statistics.mean(month_tmax[m]), 1), "tmin": round(statistics.mean(month_tmin[m]), 1),
                          "rain": round(statistics.mean(totals)) if totals else None}
    return {"frost": frost_info, "normals": normals, "years": len([1 for r in by_year.values() if len(r) >= 330])}


def fetch_climate_remote(lat, lon):
    key = os.environ.get("OPEN_METEO_API_KEY", "")
    base = ("https://customer-archive-api.open-meteo.com" if key else "https://archive-api.open-meteo.com") + "/v1/archive"
    y = date.today().year
    q = {"latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}", "start_date": f"{y - CLIMATE_YEARS}-01-01",
         "end_date": f"{y - 1}-12-31", "daily": "temperature_2m_max,temperature_2m_min,precipitation_sum", "timezone": "auto"}
    if key:
        q["apikey"] = key
    with urlopen(Request(base + "?" + urlencode(q), headers={"User-Agent": "FarmWatch/1.0"}), timeout=45) as r:
        return json.loads(r.read())["daily"]


def get_climate(farm_id, lat, lon):
    rows = sql("SELECT fetched, data FROM fw_climate WHERE farm_id=$1", (farm_id,))
    if rows:
        try:
            if time.time() - datetime.fromisoformat(rows[0]["fetched"]).timestamp() < CLIMATE_TTL_DAYS * 86400:
                return json.loads(rows[0]["data"])
        except ValueError:
            pass
    try:
        stats = climate_stats(fetch_climate_remote(lat, lon), lat)
        sql("INSERT INTO fw_climate (farm_id, fetched, data) VALUES ($1,$2,$3) "
            "ON CONFLICT (farm_id) DO UPDATE SET fetched = EXCLUDED.fetched, data = EXCLUDED.data",
            (farm_id, datetime.now(timezone.utc).isoformat(timespec="seconds"), json.dumps(stats)))
        return stats
    except Exception as e:
        print("Climate history failed:", e, file=sys.stderr)
        return json.loads(rows[0]["data"]) if rows else None


def _next_window(today, doy, offs):
    for y in (today.year - 1, today.year, today.year + 1):
        a = _doy_date(y, doy)
        s, e = a + timedelta(days=offs[0]), a + timedelta(days=offs[1])
        if e >= today:
            return s, e
    return None, None


def planting_calendar(frost, today, crop):
    out = []
    c = (crop or "").lower()
    for kw, name, spring, autumn, note in PLANTING:
        for label, doy, offs in (("Spring", frost["last"], spring), ("Autumn", frost["first"], autumn)):
            if not offs:
                continue
            s, e = _next_window(today, doy, offs)
            if not s:
                continue
            if s <= today <= e:
                status, days = "open", (e - today).days
            else:
                status, days = ("soon" if (s - today).days <= 45 else "later"), (s - today).days
            out.append({"crop": name, "season": label, "start": s.isoformat(), "end": e.isoformat(),
                        "status": status, "days": days, "note": note, "mine": bool(kw in c and c)})
    return out


def almanac_payload(user_id, farm_id):
    rows = sql("SELECT id, crop, lat, lon FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id))
    if not rows:
        raise ValueError("Farm not found.")
    f = rows[0]
    lat, lon = _f(f["lat"]), _f(f["lon"])
    _, now = get_weather(farm_id, lat, lon)
    off = (now or {}).get("utc")
    today = (datetime.now(timezone.utc) + timedelta(seconds=off or 0)).date()
    sun, prev = sun_times(today, lat, lon, off), sun_times(today - timedelta(days=1), lat, lon, off)
    sun["deltaMin"] = round(sun["dayLengthMin"] - prev["dayLengthMin"], 1)
    moon = moon_info()
    cl = get_climate(farm_id, lat, lon)
    frost, calendar, normals, years = None, [], [], 0
    if cl:
        years = cl.get("years", 0)
        fi = cl.get("frost")
        if fi:
            doy = (today - date(today.year, 1, 1)).days + 1
            md = lambda d: "%02d-%02d" % (_doy_date(2001, d).month, _doy_date(2001, d).day)
            if lat >= 0:
                phase = ("Before the typical last frost. Frost-tender crops stay at risk until about " + MONTH_NAMES[_doy_date(2001, fi["lastSafe90"]).month - 1] + " " + str(_doy_date(2001, fi["lastSafe90"]).day) + "."
                         if doy < fi["last"] else
                         "Inside the typical frost-free season." if doy < fi["first"] else
                         "After the typical first frost. The frost-free season has usually ended.")
            else:
                phase = ("Inside the typical frost season." if fi["first"] <= doy <= fi["last"]
                         else "Inside the typical frost-free season.")
            frost = {"lastSpring": md(fi["last"]), "safe90": md(fi["lastSafe90"]), "firstAutumn": md(fi["first"]),
                     "earlyFirst10": md(fi["firstEarly10"]), "frostFreeDays": fi["frostFreeDays"], "phase": phase}
            calendar = planting_calendar(fi, today, f["crop"])
        for i in range(3):
            m = (today.month + i - 1) % 12 + 1
            n = cl["normals"].get(str(m)) or cl["normals"].get(m)
            if n:
                normals.append({"month": MONTH_NAMES[m - 1], **n})
    perennial = any(w in (f["crop"] or "").lower() for w in PERENNIAL_WORDS)
    tip = ("Tradition says to sow leafy and above-ground crops while the moon is waxing, and to plant root crops, prune and "
           "transplant while it is waning." if moon["waxing"] else
           "Tradition says to plant root crops, prune and transplant while the moon is waning, and to sow leafy and "
           "above-ground crops while it is waxing.")
    return {"today": {"date": today.isoformat(), "sun": sun, "moon": moon, "soilTemp": (now or {}).get("soil")},
            "frost": frost, "calendar": calendar, "normals": normals, "years": years, "perennial": perennial,
            "moonTip": tip + " Studies have not found a reliable effect on yields, so treat it as optional and let soil "
                             "temperature, frost dates and moisture decide."}


# ---------- AI crop advisor (text, photos, voice transcripts) ----------

AI_DAILY_LIMIT = int(_envf("AI_DAILY_LIMIT", 20))
AI_MEDIA = ("image/jpeg", "image/png", "image/webp")
AI_SYSTEM = (
    "You are the crop advisor inside Farm Watch, an irrigation and crop monitoring app. Use only the farm data provided "
    "below. Never invent readings, weather or field history, and say so when something is unknown. Keep answers under "
    "200 words, in plain, practical language, in the same language as the question. Lead with the answer, then the reason. "
    "Irrigation advice in the data comes from a soil-water model and is indicative. If a photo is included: describe what "
    "you can see, list up to three possible causes with low, medium or high confidence and what would confirm each, say "
    "clearly that this is not a diagnosis, and suggest scouting steps. Do not name pesticide products or give doses; "
    "recommend confirming with a local agronomist or extension service before any spraying. If the question is not about "
    "farming, politely say you can only help with the farm."
)


AI_KEYS = {"anthropic": "ANTHROPIC_API_KEY", "openai": "OPENAI_API_KEY", "gemini": "GEMINI_API_KEY"}


def ai_provider():
    want = os.environ.get("AI_PROVIDER", "").strip().lower()
    if want in AI_KEYS and os.environ.get(AI_KEYS[want]):
        return want
    for name, key in AI_KEYS.items():
        if os.environ.get(key):
            return name
    return None


def farm_context(v):
    a, l = v["advice"], (v["series"][-1] if v["series"] else None)
    lines = [f"Farm: {v['name']}; crop: {v['crop'] or 'not set'}; area: {v['areaHa']} ha; soil: {v['soil'] or 'loam (default)'}; "
             f"irrigation method: {v['irrigation'] or 'not set'}."]
    if l:
        lines.append(f"Latest satellite reading ({l['date']}): moisture index NDMI {l['ndmi']:.2f}, greenness NDVI "
                     f"{'n/a' if l['ndvi'] is None else format(l['ndvi'], '.2f')}. Moisture status: {v['status']}.")
    else:
        lines.append("No satellite reading yet.")
    lines.append(f"Irrigation advice: {a['headline']}. {a['detail']}")
    if a.get("soil"):
        lines.append(f"Estimated soil water used: {a['soil']['depletionPct']}% of the way to the irrigation trigger.")
    n = v.get("now")
    if n and n.get("temp") is not None:
        lines.append(f"Weather now: {n['temp']:.0f}°C, humidity {n.get('humidity')}%, rain {n.get('rain')} mm, wind {n.get('wind')} km/h.")
    if v.get("forecast"):
        lines.append("7-day forecast (day: rain mm, max/min °C): " + "; ".join(
            f"{wd(d['date'])}: {d['rain']:.0f} mm, {d['tmax']:.0f}/{d['tmin']:.0f}" for d in v["forecast"]))
    if v.get("risks"):
        lines.append("Warnings: " + " | ".join(f"{r['kind']} ({r['level']}): {r['text']}" for r in v["risks"]))
    if v.get("zones"):
        lines.append("Zones: " + "; ".join(f"{z['name']} {z['status']} NDMI {z['ndmi']:.2f}" for z in v["zones"]))
    if v.get("logs"):
        lines.append("Recent activity: " + "; ".join(
            f"{g['date']} {g['kind']}" + (f" {g['amount']:.0f} mm" if g.get("amount") else "") + (f" ({g['note']})" if g.get("note") else "")
            for g in v["logs"][:6]))
    return "\n".join(lines)


def _post_ai(url, headers, body):
    req = Request(url, data=json.dumps(body).encode(), method="POST", headers={"Content-Type": "application/json", **headers})
    try:
        with urlopen(req, timeout=60) as r:
            return json.loads(r.read())
    except HTTPError as e:
        if e.code in (401, 403):
            raise ConfigError("The AI key was rejected. Check the key in the hosting settings.")
        if e.code == 429:
            raise ValueError("The AI service is busy or over its limit. Try again in a minute.")
        raise RuntimeError(f"AI service error {e.code}: " + e.read().decode("utf-8", "replace")[:200])
    except URLError as e:
        raise RuntimeError(f"Could not reach the AI service: {e.reason}")


def call_ai(system, text, image=None, media="image/jpeg", history=()):
    prov = ai_provider()
    if prov == "anthropic":
        msgs = []
        for q, a in history:
            msgs += [{"role": "user", "content": q}, {"role": "assistant", "content": a}]
        content = ([{"type": "image", "source": {"type": "base64", "media_type": media, "data": image}}] if image else []) + [{"type": "text", "text": text}]
        msgs.append({"role": "user", "content": content})
        data = _post_ai("https://api.anthropic.com/v1/messages",
                        {"x-api-key": os.environ["ANTHROPIC_API_KEY"], "anthropic-version": "2023-06-01"},
                        {"model": os.environ.get("ANTHROPIC_MODEL", "claude-sonnet-5-5"), "max_tokens": 700,
                         "system": system, "messages": msgs})
        return "".join(b.get("text", "") for b in data.get("content", []) if b.get("type") == "text").strip()
    if prov == "openai":
        msgs = [{"role": "system", "content": system}]
        for q, a in history:
            msgs += [{"role": "user", "content": q}, {"role": "assistant", "content": a}]
        content = [{"type": "text", "text": text}] + (
            [{"type": "image_url", "image_url": {"url": f"data:{media};base64,{image}"}}] if image else [])
        msgs.append({"role": "user", "content": content})
        data = _post_ai("https://api.openai.com/v1/chat/completions",
                        {"Authorization": "Bearer " + os.environ["OPENAI_API_KEY"]},
                        {"model": os.environ.get("OPENAI_MODEL") or os.environ.get("AQAS_OPENAI_MODEL") or "gpt-4.1-mini",
                         "messages": msgs, "max_completion_tokens": 700})
        try:
            return (data["choices"][0]["message"]["content"] or "").strip()
        except (KeyError, IndexError, TypeError):
            return ""
    if prov == "gemini":
        contents = []
        for q, a in history:
            contents += [{"role": "user", "parts": [{"text": q}]}, {"role": "model", "parts": [{"text": a}]}]
        parts = [{"text": text}] + ([{"inlineData": {"mimeType": media, "data": image}}] if image else [])
        contents.append({"role": "user", "parts": parts})
        model = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
        data = _post_ai(f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent",
                        {"x-goog-api-key": os.environ["GEMINI_API_KEY"]},
                        {"systemInstruction": {"parts": [{"text": system}]}, "contents": contents,
                         "generationConfig": {"maxOutputTokens": 700}})
        try:
            return "".join(p.get("text", "") for p in data["candidates"][0]["content"]["parts"]).strip()
        except (KeyError, IndexError):
            return ""
    raise ConfigError("The AI advisor is not switched on yet. Add ANTHROPIC_API_KEY, OPENAI_API_KEY or GEMINI_API_KEY in the hosting settings.")


def ask_advisor(user, farm_id, question, image_b64, media):
    if not ai_provider():
        raise ConfigError("The AI advisor is not switched on yet. Add ANTHROPIC_API_KEY, OPENAI_API_KEY or GEMINI_API_KEY in the hosting settings.")
    question = (question or "").strip()
    if not question and not image_b64:
        raise ValueError("Type or say a question, or add a photo.")
    if len(question) > 1000:
        raise ValueError("Please keep the question under 1000 characters.")
    if image_b64:
        if media not in AI_MEDIA:
            raise ValueError("Use a JPEG, PNG or WebP photo.")
        if len(image_b64) > 1_200_000:
            raise ValueError("That photo is too large. Try a smaller one.")
        try:
            base64.b64decode(image_b64, validate=True)
        except Exception:
            raise ValueError("That photo could not be read.")
    used = int(sql("SELECT COUNT(*) AS n FROM fw_chats WHERE user_id=$1 AND created >= $2",
                   (user["id"], date.today().isoformat()))[0]["n"])
    if used >= AI_DAILY_LIMIT:
        raise ValueError(f"You have used your {AI_DAILY_LIMIT} advisor questions for today. Try again tomorrow.")
    farms = farms_payload(user["id"])["farms"]
    if farm_id:
        v = next((x for x in farms if x["id"] == farm_id), None)
        if not v:
            raise ValueError("Farm not found.")
        context = farm_context(v)
        hist = sql("SELECT question, answer FROM fw_chats WHERE user_id=$1 AND farm_id=$2 ORDER BY id DESC LIMIT 4", (user["id"], farm_id))
    else:
        context = "\n\n".join(farm_context(x) for x in farms[:8]) or "No farms have been added yet."
        hist = sql("SELECT question, answer FROM fw_chats WHERE user_id=$1 AND farm_id IS NULL ORDER BY id DESC LIMIT 4", (user["id"],))
    history = [(h["question"], h["answer"]) for h in reversed(hist)]
    text = f"Farm data:\n{context}\n\nQuestion: {question or 'Please look at this photo.'}"
    try:
        answer = call_ai(AI_SYSTEM, text, image_b64, media, history)
    except ConfigError:
        raise
    except RuntimeError as e:  # show the AI provider's own message, such as a low credit balance
        raise ValueError(str(e))
    if not answer:
        raise RuntimeError("The AI returned an empty answer. Please try again.")
    sql("INSERT INTO fw_chats (user_id, farm_id, question, answer, had_image, created) VALUES ($1,$2,$3,$4,$5,$6)",
        (user["id"], farm_id or None, (question or "(photo)")[:1000], answer[:4000], 1 if image_b64 else 0,
         datetime.now(timezone.utc).isoformat(timespec="seconds")))
    return {"answer": answer, "remaining": AI_DAILY_LIMIT - used - 1}


def list_chats(user_id, farm_id):
    rows = (sql("SELECT id, question, answer, had_image, created FROM fw_chats WHERE user_id=$1 AND farm_id=$2 ORDER BY id DESC LIMIT 10", (user_id, farm_id))
            if farm_id else
            sql("SELECT id, question, answer, had_image, created FROM fw_chats WHERE user_id=$1 AND farm_id IS NULL ORDER BY id DESC LIMIT 10", (user_id,)))
    return [{"id": int(r["id"]), "question": r["question"], "answer": r["answer"], "image": str(r["had_image"]) == "1",
             "created": r["created"]} for r in reversed(rows)]


# ---------- labor tracking ----------

def _own_farm(user_id, farm_id):
    if farm_id and not sql("SELECT id FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id)):
        raise ValueError("Farm not found.")


def _own_worker(user_id, worker_id):
    rows = sql("SELECT id, name, rate FROM fw_workers WHERE id=$1 AND user_id=$2 AND active=1", (worker_id, user_id))
    if not rows:
        raise ValueError("Worker not found.")
    return rows[0]


def _num(x, lo, hi, what):
    if x in (None, ""):
        return None
    try:
        v = float(x)
    except (TypeError, ValueError):
        raise ValueError(f"{what} must be a number.")
    if not lo <= v <= hi:
        raise ValueError(f"{what} must be between {lo:g} and {hi:g}.")
    return v


def add_worker(user_id, name, role, rate):
    name = (name or "").strip()
    if not name:
        raise ValueError("Give the worker a name.")
    if int(sql("SELECT COUNT(*) AS n FROM fw_workers WHERE user_id=$1 AND active=1", (user_id,))[0]["n"]) >= 100:
        raise ValueError("You can have up to 100 workers on one account.")
    rows = sql("INSERT INTO fw_workers (user_id, name, role, rate, active) VALUES ($1,$2,$3,$4,1) RETURNING id",
               (user_id, name[:80], (role or "").strip()[:60], _num(rate, 0, 10000, "The hourly rate")))
    return int(rows[0]["id"])


def clock_in(user_id, worker_id, farm_id, task):
    _own_worker(user_id, worker_id)
    _own_farm(user_id, farm_id)
    if sql("SELECT id FROM fw_labor WHERE worker_id=$1 AND end_ts IS NULL", (worker_id,)):
        raise ValueError("That worker is already clocked in.")
    rows = sql("INSERT INTO fw_labor (worker_id, farm_id, task, start_ts) VALUES ($1,$2,$3,$4) RETURNING id",
               (worker_id, farm_id or None, (task or "").strip()[:60], datetime.now(timezone.utc).isoformat(timespec="seconds")))
    return int(rows[0]["id"])


def clock_out(user_id, worker_id):
    _own_worker(user_id, worker_id)
    rows = sql("SELECT id, start_ts FROM fw_labor WHERE worker_id=$1 AND end_ts IS NULL", (worker_id,))
    if not rows:
        raise ValueError("That worker is not clocked in.")
    now = datetime.now(timezone.utc)
    hours = min(24.0, max(0.0, (now - datetime.fromisoformat(rows[0]["start_ts"])).total_seconds() / 3600))
    sql("UPDATE fw_labor SET end_ts=$1, hours=$2 WHERE id=$3", (now.isoformat(timespec="seconds"), round(hours, 2), int(rows[0]["id"])))
    return round(hours, 2)


def add_labor(user_id, worker_id, farm_id, task, d, hours, units, piece_rate, note):
    _own_worker(user_id, worker_id)
    _own_farm(user_id, farm_id)
    try:
        date.fromisoformat(d or "")
    except ValueError:
        raise ValueError("Enter a valid date.")
    h, u, pr = _num(hours, 0, 24, "Hours"), _num(units, 0, 1000000, "Units"), _num(piece_rate, 0, 100000, "The piece rate")
    if not h and not u:
        raise ValueError("Enter the hours worked, or the units picked or planted.")
    rows = sql("INSERT INTO fw_labor (worker_id, farm_id, task, start_ts, end_ts, hours, units, piece_rate, note) "
               "VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9) RETURNING id",
               (worker_id, farm_id or None, (task or "").strip()[:60], d + "T12:00:00+00:00", d + "T12:00:00+00:00",
                h or 0, u, pr, (note or "").strip()[:200]))
    return int(rows[0]["id"])


def delete_labor(user_id, labor_id):
    sql("DELETE FROM fw_labor WHERE id=$1 AND worker_id IN (SELECT id FROM fw_workers WHERE user_id=$2)", (labor_id, user_id))


def labor_report(user_id, days):
    days = max(1, min(366, days))
    since = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat(timespec="seconds")
    workers = sql("SELECT id, name, role, rate FROM fw_workers WHERE user_id=$1 AND active=1 ORDER BY name", (user_id,))
    open_rows = {int(r["worker_id"]): r for r in sql(
        "SELECT l.worker_id, l.start_ts, l.farm_id, l.task FROM fw_labor l JOIN fw_workers w ON w.id = l.worker_id "
        "WHERE w.user_id=$1 AND l.end_ts IS NULL", (user_id,))}
    rows = sql("SELECT l.id, l.worker_id, w.name AS worker, w.rate, l.farm_id, f.name AS farm, f.area_ha, l.task, l.start_ts, "
               "l.end_ts, l.hours, l.units, l.piece_rate, l.note FROM fw_labor l JOIN fw_workers w ON w.id = l.worker_id "
               "LEFT JOIN fw_farms f ON f.id = l.farm_id WHERE w.user_id=$1 AND l.start_ts >= $2 ORDER BY l.start_ts DESC LIMIT 500",
               (user_id, since))
    entries, by_farm, by_worker = [], {}, {}
    for r in rows:
        if r["end_ts"] is None:
            continue
        hrs, rate = _f(r["hours"]) or 0.0, _f(r["rate"]) or 0.0
        units, pr = _f(r["units"]) or 0.0, _f(r["piece_rate"]) or 0.0
        cost = round(hrs * rate + units * pr, 2)
        entries.append({"id": int(r["id"]), "worker": r["worker"], "farm": r["farm"], "task": r["task"] or "", "start": r["start_ts"],
                        "hours": hrs, "units": units or None, "cost": cost, "note": r["note"] or ""})
        fk = r["farm"] or "No farm"
        b = by_farm.setdefault(fk, {"farm": fk, "hours": 0.0, "cost": 0.0, "areaHa": _f(r["area_ha"])})
        b["hours"] += hrs
        b["cost"] += cost
        w = by_worker.setdefault(r["worker"], {"worker": r["worker"], "hours": 0.0, "cost": 0.0})
        w["hours"] += hrs
        w["cost"] += cost
    farms_out = []
    for b in sorted(by_farm.values(), key=lambda x: -x["cost"]):
        farms_out.append({"farm": b["farm"], "hours": round(b["hours"], 1), "cost": round(b["cost"], 2),
                          "costPerHa": round(b["cost"] / b["areaHa"], 2) if b["areaHa"] else None})
    return {"days": days,
            "workers": [{"id": int(w["id"]), "name": w["name"], "role": w["role"] or "", "rate": _f(w["rate"]),
                         "clockedIn": ({"since": open_rows[int(w["id"])]["start_ts"], "task": open_rows[int(w["id"])]["task"] or ""}
                                       if int(w["id"]) in open_rows else None)} for w in workers],
            "entries": entries[:200],
            "byFarm": farms_out,
            "byWorker": [{"worker": w["worker"], "hours": round(w["hours"], 1), "cost": round(w["cost"], 2)}
                         for w in sorted(by_worker.values(), key=lambda x: -x["hours"])],
            "totalHours": round(sum(e["hours"] for e in entries), 1), "totalCost": round(sum(e["cost"] for e in entries), 2)}


def labor_csv(user_id, days):
    rep = labor_report(user_id, days)
    esc = lambda s: '"' + str(s if s is not None else "").replace('"', '""') + '"'
    lines = ["date,worker,farm,task,hours,units,cost,note"]
    for e in rep["entries"]:
        lines.append(",".join([e["start"][:10], esc(e["worker"]), esc(e["farm"]), esc(e["task"]), str(e["hours"]),
                               str(e["units"] or ""), str(e["cost"]), esc(e["note"])]))
    return "\n".join(lines) + "\n"


# ---------- AQAS Pro foundation (phase 1: simulated agents, approval-only) ----------

def _aqas_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")

def ensure_aqas_schema():
    global _AQAS_READY
    if _AQAS_READY: return
    sql("""CREATE TABLE IF NOT EXISTS aqas_events (id SERIAL PRIMARY KEY, occurred_at TEXT NOT NULL, actor TEXT NOT NULL, event_type TEXT NOT NULL, agent TEXT, summary TEXT NOT NULL, details TEXT NOT NULL DEFAULT '{}')""")
    sql("""CREATE TABLE IF NOT EXISTS aqas_agents (agent TEXT PRIMARY KEY, status TEXT NOT NULL DEFAULT 'paused', mode TEXT NOT NULL DEFAULT 'simulated', daily_cap INTEGER NOT NULL DEFAULT 10, metrics TEXT NOT NULL DEFAULT '{}', updated_at TEXT NOT NULL)""")
    sql("""CREATE TABLE IF NOT EXISTS aqas_proposals (id SERIAL PRIMARY KEY, created_at TEXT NOT NULL, created_by TEXT NOT NULL, agent TEXT NOT NULL, title TEXT NOT NULL, rationale TEXT NOT NULL, expected_effect TEXT NOT NULL, risk TEXT NOT NULL, proposed_change TEXT NOT NULL DEFAULT '{}', status TEXT NOT NULL DEFAULT 'pending', reviewed_at TEXT, reviewed_by TEXT, review_note TEXT)""")
    for name, description in [("ARAIAH", "Sales automation; prospecting and pipeline workflows"), ("Pluto", "Customer onboarding and operational task workflows"), ("Orion", "Software, tests, dependencies, and deployment proposals")]:
        if not sql("SELECT agent FROM aqas_agents WHERE agent=$1", (name,)):
            sql("INSERT INTO aqas_agents (agent,status,mode,daily_cap,metrics,updated_at) VALUES ($1,'paused','simulated',10,$2,$3)", (name, json.dumps({"description": description, "actions_today": 0}), _aqas_now()))
    _AQAS_READY = True

def aqas_event(actor, event_type, summary, agent=None, details=None):
    sql("INSERT INTO aqas_events (occurred_at,actor,event_type,agent,summary,details) VALUES ($1,$2,$3,$4,$5,$6)", (_aqas_now(), actor[:100], event_type[:80], agent, summary[:500], json.dumps(details or {}, ensure_ascii=False)))

def aqas_snapshot():
    ensure_aqas_schema()
    agents = sql("SELECT agent,status,mode,daily_cap,metrics,updated_at FROM aqas_agents ORDER BY agent")
    proposals = sql("SELECT id,created_at,created_by,agent,title,rationale,expected_effect,risk,proposed_change,status,reviewed_at,reviewed_by,review_note FROM aqas_proposals WHERE status='pending' ORDER BY id DESC LIMIT 100")
    events = sql("SELECT id,occurred_at,actor,event_type,agent,summary,details FROM aqas_events ORDER BY id DESC LIMIT 50")
    for row in agents:
        try: row["metrics"] = json.loads(row.get("metrics") or "{}")
        except Exception: row["metrics"] = {}
    for row in proposals:
        try: row["proposed_change"] = json.loads(row.get("proposed_change") or "{}")
        except Exception: row["proposed_change"] = {}
    for row in events:
        try: row["details"] = json.loads(row.get("details") or "{}")
        except Exception: row["details"] = {}
    return {"mode":"simulated", "liveAgentActionsEnabled":False, "openaiConfigured":bool(os.environ.get("OPENAI_API_KEY")), "agents":agents, "pendingProposals":proposals, "events":events}

def aqas_health():
    """Plain counts that let the supervisor see whether the whole system is working."""
    ensure_schema()
    n = lambda q, p=(): int(sql(q, p)[0]["n"])
    today = date.today()
    week, stale = (today - timedelta(days=7)).isoformat(), (today - timedelta(days=14)).isoformat()
    last = get_meta("last_fetch")
    hrs = None
    if last:
        try:
            hrs = round((datetime.now(timezone.utc) - datetime.fromisoformat(last)).total_seconds() / 3600, 1)
        except ValueError:
            pass
    sat_ok = bool(os.environ.get("CDSE_CLIENT_ID") and os.environ.get("CDSE_CLIENT_SECRET"))
    cards = [
        {"label": "Users", "value": n("SELECT COUNT(*) AS n FROM fw_users"),
         "note": f"{n('SELECT COUNT(*) AS n FROM fw_users WHERE created >= $1', (week,))} new in 7 days"},
        {"label": "Farms", "value": n("SELECT COUNT(*) AS n FROM fw_farms"), "note": "across all accounts"},
        {"label": "Satellite readings, 7 days", "value": n("SELECT COUNT(*) AS n FROM fw_readings WHERE date >= $1", (week,)),
         "note": "satellite keys " + ("set" if sat_ok else "missing")},
        {"label": "Last satellite check", "value": (f"{hrs} h ago" if hrs is not None else "never"),
         "note": "the daily timer should run every 24 hours"},
        {"label": "Farms without a recent image",
         "value": n("SELECT COUNT(*) AS n FROM fw_farms f WHERE NOT EXISTS (SELECT 1 FROM fw_readings r WHERE r.farm_id = f.id AND r.date >= $1)", (stale,)),
         "note": "no clear image in 14 days"},
        {"label": "Advisor questions today", "value": n("SELECT COUNT(*) AS n FROM fw_chats WHERE created >= $1", (today.isoformat(),)),
         "note": "AI provider: " + (ai_provider() or "not set")},
        {"label": "Workers on the clock", "value": n("SELECT COUNT(*) AS n FROM fw_labor WHERE end_ts IS NULL"), "note": "labor tracking"},
        {"label": "Email", "value": "on" if os.environ.get("SMTP_HOST") else "off", "note": "briefings, alerts and password resets"},
    ]
    return {"cards": cards, "lastFetch": last, "hoursSinceFetch": hrs}


def aqas_log_daily(result):
    """Record each daily run in the audit trail, and raise a proposal if farms failed."""
    try:
        ensure_aqas_schema()
        fails = [x for x in result.get("messages", []) if "failed" in x]
        aqas_event("system-monitor", "daily_run",
                   f"Daily run finished: {result.get('stored', 0)} new readings, {result.get('alerts', 0)} alerts, "
                   f"{result.get('briefings', 0)} briefings, {len(fails)} problem(s).", "AQAS", {"failures": fails[:5]})
        if fails:
            title = "Investigate failed satellite or map fetches"
            if not sql("SELECT id FROM aqas_proposals WHERE status='pending' AND title=$1", (title,)):
                sql("INSERT INTO aqas_proposals (created_at,created_by,agent,title,rationale,expected_effect,risk,proposed_change,status) "
                    "VALUES ($1,$2,$3,$4,$5,$6,$7,$8,'pending')",
                    (_aqas_now(), "system-monitor", "Orion", title, ("The latest daily run reported: " + "; ".join(fails[:3]))[:1900],
                     "Fewer missing readings and fewer stale fields.", "low",
                     json.dumps({"description": "Review the failing farms and the Copernicus responses, then fix credentials, field boundaries or limits."})))
                aqas_event("system-monitor", "proposal_created", title, "Orion", {"risk": "low"})
    except Exception as e:
        print("AQAS log failed:", e, file=sys.stderr)


AQAS_HTML = r"""<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>AQAS Pro Control Room</title><style>:root{color-scheme:dark;--line:#26364f;--muted:#a8b7cc;--text:#f4f7fb;--accent:#7dd3fc;--amber:#fcd34d}*{box-sizing:border-box}body{margin:0;background:radial-gradient(ellipse at top,#162846,#0a1020 60%);color:var(--text);font:15px system-ui,sans-serif}.wrap{max-width:1150px;margin:auto;padding:28px 18px 60px}.top,.sectionhead{display:flex;justify-content:space-between;align-items:center;gap:16px;flex-wrap:wrap}.brand{font-size:12px;letter-spacing:.2em;color:var(--accent);font-weight:800}.subtitle,.muted{color:var(--muted);font-size:13px}.badge,.status{border:1px solid #806b2e;color:var(--amber);border-radius:99px;padding:7px 11px;font-size:12px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:14px;margin:24px 0}.card,section{background:rgba(17,27,46,.94);border:1px solid var(--line);border-radius:16px;padding:18px}.notice{background:#172a40;border:1px solid #31506c;padding:12px;border-radius:10px;margin:14px 0}.tokenbox,.row{display:flex;gap:8px;flex-wrap:wrap;margin:12px 0}.tokenbox input{flex:1;min-width:220px}.proposal,.event{border-top:1px solid var(--line);padding:14px 0}.risk{font-size:11px;text-transform:uppercase;color:var(--amber)}.risk.high{color:#fca5a5}.risk.low{color:#86efac}button,input,textarea,select{font:inherit;border-radius:9px;border:1px solid #344761;padding:10px;background:#0b1425;color:var(--text)}button{cursor:pointer;background:#173c59;border-color:#2b6c91}button.secondary{background:#1c293d}button.danger{background:#51272c}input,select,textarea{width:100%}textarea{min-height:70px}label{display:block;font-size:12px;color:var(--muted);margin-bottom:5px}.formgrid{display:grid;grid-template-columns:1fr 1fr;gap:10px}.wide{grid-column:1/-1}.empty{color:var(--muted);padding:16px 0}@media(max-width:600px){.formgrid{grid-template-columns:1fr}.wide{grid-column:auto}}</style></head><body><div class="wrap"><div class="top"><div><div class="brand">AQAS PRO / CONTROL ROOM</div><h1 style="margin:7px 0 0">FarmWatch Operations</h1><div class="subtitle">Supervisor foundation · auditable · human-approved</div></div><span class="badge">SIMULATION MODE · NO LIVE AGENT ACTIONS</span></div><div class="notice">Phase 1 is intentionally safe: agents are paused and simulated. Approving a proposal records the decision only; it does not change production systems or send outreach.</div><div class="tokenbox"><input id="token" type="password" autocomplete="off" placeholder="AQAS_ADMIN_TOKEN (not your OpenAI key)"><button onclick="saveToken()">Connect control room</button><button class="secondary" onclick="refresh()">Refresh</button></div><div id="message" class="muted">Set AQAS_ADMIN_TOKEN in Render, then enter the same value here.</div><div id="agents" class="grid"></div><section><div class="sectionhead"><h2>Farm Watch health</h2><span class="muted">Live counts from the running system</span></div><div id="health" class="grid"></div></section><section><div class="sectionhead"><h2>Proposal queue</h2><span class="muted">All behavior changes require approval</span></div><div id="proposals" class="empty">Connect to load proposals.</div></section><section style="margin-top:16px"><div class="sectionhead"><h2>Create a proposal</h2><span class="muted">No direct execution</span></div><form id="proposalForm"><div class="formgrid"><div><label>Agent</label><select id="agent"><option>ARAIAH</option><option>Pluto</option><option>Orion</option><option>AQAS</option></select></div><div><label>Risk level</label><select id="risk"><option>low</option><option>medium</option><option>high</option></select></div><div class="wide"><label>Proposal title</label><input id="title" required maxlength="180"></div><div class="wide"><label>Reason / evidence</label><textarea id="rationale" required maxlength="2000"></textarea></div><div class="wide"><label>Expected effect</label><textarea id="effect" required maxlength="1000"></textarea></div><div class="wide"><label>Proposed change (plain-language description)</label><textarea id="change" maxlength="2000"></textarea></div></div><div class="row"><button type="submit">Submit for review</button></div></form></section><section style="margin-top:16px"><div class="sectionhead"><h2>Audit trail</h2><span class="muted">Most recent 50 events</span></div><div id="events" class="empty">Connect to load events.</div></section></div><script>const $=id=>document.getElementById(id);function token(){return sessionStorage.getItem('aqas_admin_token')||''}function saveToken(){sessionStorage.setItem('aqas_admin_token',$('token').value.trim());refresh()}function esc(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}async function api(r,method='GET',body){const res=await fetch('?r='+encodeURIComponent(r),{method,headers:{'Authorization':'Bearer '+token(),'Content-Type':'application/json'},body:body?JSON.stringify(body):undefined,cache:'no-store'});let d={};try{d=await res.json()}catch{}if(!res.ok)throw Error(d.error||'Request failed ('+res.status+')');return d}async function refresh(){if($('token').value)sessionStorage.setItem('aqas_admin_token',$('token').value.trim());$('message').textContent='Connecting…';try{const d=await api('aqas-status');try{const h=await api('aqas-health');$('health').innerHTML=h.cards.map(c=>`<div class="card"><div class="muted">${esc(c.label)}</div><h2 style="margin:6px 0 0">${esc(c.value)}</h2><div class="muted">${esc(c.note||'')}</div></div>`).join('')}catch(e){$('health').innerHTML=''}$('message').textContent='Connected · OpenAI key '+(d.openaiConfigured?'configured':'not configured')+' · live agent actions disabled';$('agents').innerHTML=d.agents.map(a=>`<div class="card"><div class="sectionhead"><h3>${esc(a.agent)}</h3><span class="status">${esc(a.status)}</span></div><div class="muted">${esc((a.metrics||{}).description||'Specialist agent')}</div><p>Mode: <b>${esc(a.mode)}</b></p><p>Daily contact cap: <b>${esc(a.daily_cap)}</b></p><div class="row"><button class="secondary" onclick="pauseAgent('${esc(a.agent)}','paused')">Pause</button><button class="secondary" onclick="pauseAgent('${esc(a.agent)}','simulated')">Set simulated</button></div></div>`).join('');$('proposals').innerHTML=d.pendingProposals.length?d.pendingProposals.map(p=>`<div class="proposal"><div class="sectionhead"><h3>${esc(p.title)}</h3><span class="risk ${esc(p.risk)}">${esc(p.risk)} risk</span></div><div class="muted">${esc(p.agent)} · ${esc(p.created_at)}</div><p>${esc(p.rationale)}</p><p><b>Expected effect:</b> ${esc(p.expected_effect)}</p><p class="muted">Proposed change: ${esc(JSON.stringify(p.proposed_change))}</p><div class="row"><button onclick="decide(${p.id},'approved')">Approve record</button><button class="danger" onclick="decide(${p.id},'rejected')">Reject</button></div></div>`).join(''):'<div class="empty">No pending proposals.</div>';$('events').innerHTML=d.events.length?d.events.map(e=>`<div class="event"><div class="muted">${esc(e.occurred_at)} · ${esc(e.actor)} · ${esc(e.event_type)} ${e.agent?'· '+esc(e.agent):''}</div><div>${esc(e.summary)}</div></div>`).join(''):'<div class="empty">No events yet.</div>'}catch(e){$('message').textContent=e.message;$('agents').innerHTML='';$('proposals').innerHTML='<div class="empty">Not connected.</div>'}}async function pauseAgent(agent,status){try{await api('aqas-agent-control','POST',{agent,status});await refresh()}catch(e){alert(e.message)}}async function decide(id,status){const note=prompt('Review note (required for audit):');if(note===null)return;try{await api('aqas-decision','POST',{id,status,note});await refresh()}catch(e){alert(e.message)}}$('proposalForm').addEventListener('submit',async e=>{e.preventDefault();try{await api('aqas-propose','POST',{agent:$('agent').value,risk:$('risk').value,title:$('title').value,rationale:$('rationale').value,expectedEffect:$('effect').value,change:$('change').value});e.target.reset();await refresh()}catch(err){alert(err.message)}});$('token').value=token();if(token())refresh();</script></body></html>
"""


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

.tabs{display:flex;gap:6px;margin-bottom:12px}
.tabs button{flex:1;font:inherit;font-weight:600;padding:10px;border-radius:8px;border:1px solid var(--line);background:var(--panel);color:var(--ink);cursor:pointer;min-height:44px}
.tabs button.on{background:var(--wet);color:#fff;border-color:var(--wet)}
.chat{max-height:380px;overflow:auto;margin:8px 0}
.msg{padding:8px 10px;border-radius:10px;margin:6px 0;white-space:pre-wrap;font-size:15px}
.msg.me{background:var(--bg);margin-left:24px}.msg.ai{background:var(--panel);border:1px solid var(--line);margin-right:12px}
.alm h4{margin:10px 0 2px;font-size:14px}
textarea{resize:vertical}
.chip{font:inherit;font-size:13px;padding:6px 10px;border-radius:16px;border:1px solid var(--line);background:var(--panel);color:var(--ink);cursor:pointer}

/* ---------- A1 AI brand theme ---------- */
:root{--bg:#f3f7f4;--ink:#0f2a20;--mute:#587066;--line:#dbe6e0;--wet:#0f7b5c;--ok:#1a8f55;--g1:#06301f;--g2:#0f7b5c;--g3:#7bd88f;--sh:0 6px 22px rgba(10,60,40,.10)}
@media (prefers-color-scheme:dark){:root{--bg:#07130e;--panel:#10201a;--ink:#e9f5ee;--mute:#9db5aa;--line:#21382e;--wet:#3ec28f;--ok:#4cd08a;--sh:0 6px 22px rgba(0,0,0,.35)}}
body{background:radial-gradient(900px 380px at 80% -80px,rgba(60,190,130,.18),transparent 70%),var(--bg);font-family:Inter,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;letter-spacing:-.005em}
header{margin:-14px -16px 18px;padding:max(16px,env(safe-area-inset-top)) 18px 18px;background:linear-gradient(120deg,var(--g1),var(--g2) 70%,#2fb585);color:#fff;border-radius:0 0 26px 26px;box-shadow:0 10px 30px rgba(6,48,31,.28)}
header h1{display:flex;align-items:center;gap:10px;font-size:23px;font-weight:800;letter-spacing:-.02em;color:#fff}
header h1 small{display:block;font-size:11px;font-weight:600;letter-spacing:.16em;text-transform:uppercase;color:var(--g3);margin-top:1px}
.logo{width:40px;height:40px;border-radius:12px;background:linear-gradient(140deg,#c9f7a1,#3fcf8e);display:grid;place-items:center;font-size:22px;box-shadow:0 4px 14px rgba(0,0,0,.25)}
header .sub{color:rgba(255,255,255,.9)}header .b.alt{color:#fff;border-color:rgba(255,255,255,.45)}
.panel,.tile{border-radius:18px;box-shadow:var(--sh);border-color:transparent}
.panel{padding:18px}
h2{font-size:18px;font-weight:750}
h3{font-size:14px;text-transform:uppercase;letter-spacing:.08em;color:var(--wet);margin:20px 0 6px}
.tile{position:relative;overflow:hidden;padding:12px 14px}
.tile:before{content:"";position:absolute;left:0;top:0;bottom:0;width:5px;background:var(--wet)}
.tile:nth-child(2):before{background:#2f9bd8}.tile:nth-child(3):before{background:#f0a21b}.tile:nth-child(4):before{background:#e0533c}
.tile b{font-size:28px;font-weight:800}
.b{background:linear-gradient(135deg,var(--g2),#16a56f);border-radius:12px;box-shadow:0 4px 14px rgba(15,123,92,.30);transition:transform .12s,box-shadow .12s}
.b:active{transform:scale(.97)}.b.alt,.b.danger{background:var(--panel);box-shadow:none}
.tabs{background:var(--panel);padding:5px;border-radius:16px;box-shadow:var(--sh)}
.tabs button{border:0;border-radius:12px;background:transparent;color:var(--mute);font-weight:700}
.tabs button.on{background:linear-gradient(135deg,var(--g2),#16a56f);color:#fff;box-shadow:0 4px 12px rgba(15,123,92,.35)}
.item{padding:14px 16px}.item[aria-current=true]{background:linear-gradient(90deg,rgba(15,123,92,.14),transparent);box-shadow:inset 4px 0 0 var(--wet)}
.adv{border-radius:14px;background:linear-gradient(135deg,rgba(15,123,92,.10),rgba(47,155,216,.08));border-left-width:5px}
.alm{background:linear-gradient(160deg,rgba(255,196,60,.10),rgba(47,155,216,.07));border-radius:14px;padding:4px 14px 12px}
.alm h4{color:var(--wet);text-transform:uppercase;letter-spacing:.07em;font-size:12px;margin:14px 0 4px}
.auth{max-width:440px;padding:26px;background:linear-gradient(180deg,var(--panel),var(--panel));border:1px solid var(--line)}
.hero{margin:0 0 14px;padding:16px;border-radius:14px;background:linear-gradient(135deg,var(--g1),var(--g2));color:#fff}
.hero b{display:block;font-size:19px;line-height:1.25;margin-bottom:8px}.hero span{display:block;font-size:14px;opacity:.92;margin-top:3px}
input:not([type=checkbox]),select,textarea{border-radius:12px;background:var(--panel)}
input:focus,select:focus,textarea:focus{border-color:var(--wet);box-shadow:0 0 0 3px rgba(15,123,92,.18);outline:0}
.msg.ai{border-radius:16px;box-shadow:var(--sh);border-color:transparent}.msg.me{background:linear-gradient(135deg,var(--g2),#16a56f);color:#fff;border-radius:16px}
.wrap{padding-bottom:max(36px,env(safe-area-inset-bottom))}
</style>
</head>
<body>
<div class="wrap">
  <header><h1><span class="logo" aria-hidden="true">🛰️</span><span>Farm Watch<small>by A1 AI</small></span></h1><div id="who" class="sub" hidden><span id="whoName"></span> <button id="logout" class="b alt" type="button" style="min-height:36px;margin:0 0 0 8px;padding:4px 12px">Log out</button></div></header>
  <p id="status" role="status" aria-live="polite"></p>

  <section id="auth" class="panel auth" hidden>
    <h2 id="authTitle">Log in</h2>
    <div class="hero"><b>Know exactly when, where and how much to irrigate.</b><span>🛰️ Satellite moisture for every field</span><span>💧 Daily irrigation plan in mm, m³ and pump hours</span><span>🌦️ 7-day forecast, frost and spray windows</span><span>🌙 Almanac: sun, moon, frost dates, planting windows</span></div>
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
    <div class="tabs" id="tabs" role="tablist"><button type="button" data-view="Farms" class="on">🌾 Farms</button><button type="button" data-view="Advisor">🤖 Advisor</button><button type="button" data-view="Labor">👷 Labor</button></div>
    <div id="viewFarms">
    <div class="panel" id="planCard"></div>
    <div class="panel"><h2>Morning briefing</h2><div id="brief"></div><button id="briefSpeak" class="b alt sm" type="button">🔊 Read aloud</button></div>
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
    </div>
    <div id="viewAdvisor" hidden>
      <div class="panel">
        <h2>Crop advisor</h2>
        <p class="sub" id="aiNote"></p>
        <label for="aFarm">About</label><select id="aFarm"></select>
        <div id="chat" class="chat" aria-live="polite"></div>
        <label for="aq">Your question</label>
        <textarea id="aq" rows="3" maxlength="1000" placeholder="For example: should I irrigate tomorrow? What is wrong with these leaves?"></textarea>
        <div id="aPrev" class="sub"></div>
        <div class="bar" style="margin-top:6px"><button id="aMic" class="b alt sm" type="button" style="margin:0">🎤 Talk</button><label class="b alt sm" style="margin:0;display:inline-flex;align-items:center;cursor:pointer">📷 Photo<input id="aImg" type="file" accept="image/*" hidden></label><button id="aSend" class="b sm" type="button" style="margin:0">Ask</button></div>
        <div class="bar" style="margin-top:8px"><button class="chip" type="button" data-q="What should I do on this farm today?">What should I do today?</button><button class="chip" type="button" data-q="Explain my irrigation advice in simple words.">Explain my irrigation advice</button><button class="chip" type="button" data-q="Is this a pest, a disease or a water problem? What should I check first?">What is wrong with this plant? (add a photo)</button></div>
        <p id="aLeft" class="help"></p>
        <p class="help">The advisor is an AI. It can be wrong, and a photo is not a diagnosis. Confirm with a local agronomist before spraying anything.</p>
      </div>
    </div>
    <div id="viewLabor" hidden>
      <div class="panel">
        <h2>Workers</h2>
        <p class="help" style="margin:0 0 6px">Record hours with each worker’s agreement and follow your local labor and privacy rules. Farm Watch does not track anyone’s location.</p>
        <div class="two"><div><label for="lFarmIn">Clock in to</label><select id="lFarmIn"></select></div><div><label for="lTaskIn">Task</label><select id="lTaskIn"></select></div></div>
        <div id="lWorkers" style="margin-top:8px"></div>
        <h3>Add a worker</h3>
        <div class="two"><div><label for="wName">Name</label><input id="wName" maxlength="80"></div><div><label for="wRole">Role</label><input id="wRole" maxlength="60" placeholder="Picker, tractor driver…"></div></div>
        <label for="wRate">Hourly rate (optional)</label><input id="wRate" type="number" min="0" step="0.01" inputmode="decimal">
        <button id="wAdd" class="b sm" type="button">Add worker</button>
      </div>
      <div class="panel">
        <h2>Add hours or piece work</h2>
        <div class="two"><div><label for="mWorker">Worker</label><select id="mWorker"></select></div><div><label for="mFarm">Farm</label><select id="mFarm"></select></div></div>
        <div class="two"><div><label for="mTask">Task</label><select id="mTask"></select></div><div><label for="mDate">Date</label><input id="mDate" type="date"></div></div>
        <div class="two"><div><label for="mHours">Hours</label><input id="mHours" type="number" min="0" max="24" step="0.25" inputmode="decimal"></div><div><label for="mUnits">Units picked or planted (optional)</label><input id="mUnits" type="number" min="0" step="1" inputmode="decimal"></div></div>
        <div class="two"><div><label for="mPiece">Pay per unit (optional)</label><input id="mPiece" type="number" min="0" step="0.01" inputmode="decimal"></div><div><label for="mNote">Note</label><input id="mNote" maxlength="200"></div></div>
        <button id="mSave" class="b sm" type="button">Save</button>
      </div>
      <div class="panel">
        <div class="row"><h2 style="margin:0">Labor summary</h2><select id="lDays" style="width:auto"><option value="7">Last 7 days</option><option value="30">Last 30 days</option><option value="90">Last 90 days</option></select></div>
        <div id="lSummary" style="margin-top:8px"></div>
        <p class="help" style="margin:8px 0 0"><a id="lCsv" href="#">Download as a spreadsheet (CSV)</a></p>
      </div>
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
var moist=null;
function drawDetailMap(f){
  moist=null;
  if(dmap){dmap.remove();dmap=null}
  var el=$("dmap");if(!el)return;
  if(typeof L==="undefined"||!f.geometry){el.textContent="Map unavailable.";return}
  dmap=L.map(el,{scrollWheelZoom:false});
  L.tileLayer(SAT,{maxZoom:19,attribution:"Tiles &copy; Esri"}).addTo(dmap);
  var ring=f.geometry.coordinates[0].map(function(p){return [p[1],p[0]]});
  dmap.fitBounds(L.latLngBounds(ring),{padding:[24,24]});
  var pl=L.polygon(ring,{color:HEX[lab(f)],weight:3,fillOpacity:(f.map||(f.zones&&f.zones.length))?0:0.15}).addTo(dmap);
  if(f.map){var b=f.map.bbox;moist=L.imageOverlay(f.map.url,[[b[1],b[0]],[b[3],b[2]]],{opacity:1}).addTo(dmap);try{pl.bringToFront()}catch(e){}}
  (f.zones||[]).forEach(function(z){
    var zr=z.geometry.coordinates[0].map(function(p){return [p[1],p[0]]});
    L.polygon(zr,{color:HEX[z.status],weight:f.map?2:1,fillColor:HEX[z.status],fillOpacity:f.map?0:0.4}).bindTooltip(z.name+": "+z.ndmi.toFixed(2)+" ("+z.status+")").addTo(dmap);
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
  if(f.map)h+='<div style="margin-top:6px"><label style="display:inline;margin:0"><input type="checkbox" id="mapOn" checked> Moisture map from '+esc(f.map.date)+'</label><div style="height:8px;border-radius:4px;margin-top:6px;background:linear-gradient(90deg,#8c261a,#d9731f,#f2d940,#73bf59,#1f66cc)"></div><div class="row sub" style="font-size:12px"><span>Dry</span><span>Wet</span></div></div>';
  h+='<div class="adv" style="border-color:'+(ACOL[a.action]||"var(--mute)")+'"><b>'+esc(a.headline)+'</b>'+esc(a.detail)+(a.weekRainMm!=null?'<div class="sub" style="margin-top:4px">Next 7 days: rain about '+Math.round(a.weekRainMm)+' mm, crop water use about '+Math.round(a.weekEtMm)+' mm</div>':'')+'</div>';
  if(a.soil){var pc=a.soil.depletionPct;
    h+='<div class="sub" style="margin:10px 0 2px">Soil water used: <b>'+pc+'%</b> of the way to the irrigation trigger (about '+a.soil.rawMm+' mm usable before you irrigate)</div><div class="bar"><i style="width:'+Math.min(100,pc)+'%;background:'+(pc>=100?"var(--dry)":pc>=70?"var(--watch)":"var(--ok)")+'"></i></div>'+soilChart(a.soil.trajectory);
    var VL={ok:"matched your field",wetter:"said the field is wetter",drier:"said the field is drier"};
    h+='<div class="sub" style="margin-top:8px">Does this match your field?'+(f.feedback?' <i>You '+esc(VL[f.feedback.verdict]||"")+' on '+esc(f.feedback.date)+'.</i>':'')+'</div><button class="b alt sm" type="button" data-fb="ok">Yes</button><button class="b alt sm" type="button" data-fb="wetter">Wetter than this</button><button class="b alt sm" type="button" data-fb="drier">Drier than this</button>';
  }
  h+='<details class="why"><summary>Why this advice?</summary><p class="help" style="margin:6px 0 0">'+esc(a.why||"")+'</p></details>';
  if(a.calendar&&a.calendar.length){
    h+='<h3>This week&#39;s irrigation calendar</h3>'+a.calendar.map(function(e){var m3=f.areaHa?Math.round(e.mm*f.areaHa*10):null;return '<div class="logrow"><span><b>'+wd(e.date)+'</b> '+e.mm+' mm'+(m3!=null?' ('+m3+' m&sup3;'+(f.flow?', about '+(m3/f.flow).toFixed(1)+' h':'')+')':'')+'</span></div>'}).join("");
  }else if(a.soil)h+='<p class="help" style="margin:8px 0 0">No irrigation is needed in the next 7 days.</p>';
  if(f.now&&f.now.temp!=null)h+='<p class="help" style="margin:10px 0 0">Right now: '+Math.round(f.now.temp)+'&deg;C, '+Math.round(f.now.humidity)+'% humidity, '+(f.now.rain||0)+' mm rain, wind '+Math.round(f.now.wind)+' km/h (gusts '+Math.round(f.now.gusts)+' km/h)</p>';
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
  h+='<h3>🌙 Almanac</h3><div id="alm" class="alm help">Loading sun, moon, frost dates and planting windows…</div>';
  h+='<h3>Field settings</h3><p class="help" style="margin:0 0 4px">These make the irrigation advice fit your field.</p><div class="two"><div><label for="sc">Crop</label><input id="sc" maxlength="60" value="'+esc(f.crop)+'"></div><div><label for="ss">Soil</label><select id="ss"><option value="">Loam (default)</option><option value="sandy">Sandy (drains fast)</option><option value="loam">Loam</option><option value="clay">Clay (holds water)</option></select></div></div><label for="sm">Irrigation method</label><select id="sm"><option value="">Not sure</option><option value="drip">Drip</option><option value="sprinkler">Sprinkler or pivot</option><option value="flood">Flood or furrow</option></select><label for="sf">System flow (m&sup3; per hour, optional)</label><input id="sf" type="number" min="0" step="1" inputmode="decimal" value="'+(f.flow||"")+'"><button class="b alt sm" type="button" id="setSave">Save field settings</button>';
  var KL={irrigation:"Irrigated",spray:"Sprayed",scouting:"Scouted",other:"Other"},today=new Date().toISOString().slice(0,10);
  h+='<h3>What you did</h3><p class="help" style="margin:0 0 4px">Logging irrigation makes the advice smarter, and helps build your farm record.</p>'+
    '<div class="two"><div><label for="lk">Action</label><select id="lk"><option value="irrigation">Irrigated</option><option value="spray">Sprayed</option><option value="scouting">Scouted</option><option value="other">Other</option></select></div><div><label for="la">Amount (mm, if irrigated)</label><input id="la" type="number" step="1" min="0" inputmode="decimal"></div></div>'+
    '<div class="two"><div><label for="ld">Date</label><input id="ld" type="date" value="'+today+'"></div><div><label for="ln">Note</label><input id="ln" maxlength="200" placeholder="Optional"></div></div>'+
    '<button class="b" type="button" id="logAdd">Save to log</button>'+
    (f.logs&&f.logs.length?'<div style="margin-top:8px">'+f.logs.map(function(g){return '<div class="logrow"><span>'+esc(KL[g.kind]||g.kind)+(g.amount!=null?" "+g.amount+" mm":"")+", "+esc(g.date)+(g.note?" · "+esc(g.note):"")+'</span><button type="button" data-log="'+g.id+'" aria-label="Delete this log entry">×</button></div>'}).join("")+'</div>':'');
  h+='<button class="b danger" type="button" id="del">'+(armed===f.id?"Tap again to delete":"Delete farm")+'</button>';
  $("detail").innerHTML=h;try{drawDetailMap(f)}catch(e){var de=$("dmap");if(de)de.textContent="Map unavailable."}loadAlmanac(f);
  var mc=$("mapOn");if(mc)mc.addEventListener("change",function(){if(!moist||!dmap)return;if(this.checked)moist.addTo(dmap);else dmap.removeLayer(moist)});
  $("ss").value=f.soil||"";$("sm").value=f.irrigation||"";
  $("setSave").addEventListener("click",async function(){
    try{await api("POST","farmsettings",{farmId:f.id,crop:$("sc").value,soil:$("ss").value,method:$("sm").value,flow:$("sf").value});say("Field settings saved.");await load()}catch(e){say(e.message,1)}
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
  var pl=DATA.plan||{today:[],soon:[]},ph='<h2>Today&#39;s irrigation plan</h2>';
  if(pl.today.length){
    ph+=pl.today.map(function(i){return '<div class="logrow"><span><b>'+esc(i.name)+'</b>: '+esc(i.headline)+' &middot; about '+i.m3+' m&sup3;'+(i.hours!=null?', '+i.hours+' h of pumping':'')+'</span></div>'}).join("")+
      '<p style="margin:8px 0 0"><b>Total today: '+pl.totalM3+' m&sup3;'+(pl.totalHours!=null?', about '+pl.totalHours+' pump hours':'')+'</b></p>';
  }else ph+='<p style="margin:0">Nothing needs irrigating today.</p>';
  if(pl.soon.length)ph+='<p class="help" style="margin:8px 0 0">Coming up: '+pl.soon.map(function(i){return esc(i.name)+" ("+esc(i.headline)+")"}).join("; ")+'</p>';
  $("planCard").innerHTML=ph;
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
  DATA=await api("GET","farms");render();if(typeof fillFarmSelects==="function")fillFarmSelects();
}
async function enter(){
  var me=await api("GET","me");INVITE=!!me.inviteRequired;AI_ON=!!me.ai;
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

/* ---------- almanac ---------- */
function mdFmt(s){var p=s.split("-");return new Date(2001,parseInt(p[0],10)-1,parseInt(p[1],10)).toLocaleDateString(undefined,{month:"short",day:"numeric"})}
function dFmt(s){return new Date(s+"T00:00:00").toLocaleDateString(undefined,{month:"short",day:"numeric"})}
function almanacHtml(a){
  var t=a.today,s=t.sun,m=t.moon,h='',hm=function(min){return Math.floor(min/60)+" h "+(min%60)+" min"};
  h+='<h4>Today</h4><p class="help" style="margin:0">'+(s.polar?esc(s.polar):('Sunrise '+esc(s.sunrise||"n/a")+', sunset '+esc(s.sunset||"n/a")))+'. Day length '+hm(s.dayLengthMin)+(s.deltaMin?' ('+(s.deltaMin>0?'+':'')+s.deltaMin+' min since yesterday)':'')+'. Moon: '+esc(m.phase)+', '+m.illumination+'% lit. Next full moon about '+dFmt(m.nextFull)+', next new moon about '+dFmt(m.nextNew)+'.'+(t.soilTemp!=null?' Soil about '+Math.round(t.soilTemp)+'°C.':'')+'</p>';
  if(a.frost){
    var fr=a.frost;
    h+='<h4>Frost and season</h4><p class="help" style="margin:0">Typical last spring frost '+mdFmt(fr.lastSpring)+' (90% of years by '+mdFmt(fr.safe90)+'). Typical first autumn frost '+mdFmt(fr.firstAutumn)+(fr.frostFreeDays?'. About '+fr.frostFreeDays+' frost-free days':'')+'. '+esc(fr.phase)+' Based on '+a.years+' years of local weather history.</p>';
  }else h+='<h4>Frost and season</h4><p class="help" style="margin:0">'+(a.years?'Frost is rare at this location, so frost-based planting windows do not apply. Use soil temperature and rainy-season timing instead.':'Local weather history is not available right now.')+'</p>';
  if(a.calendar&&a.calendar.length){
    var row=function(w){return '<div class="logrow"><span><b>'+esc(w.crop)+'</b> ('+esc(w.season.toLowerCase())+'): '+dFmt(w.start)+' to '+dFmt(w.end)+' · '+(w.status==="open"?'<b style="color:var(--ok)">open now, '+w.days+' days left</b>':'opens in '+w.days+' days')+'</span></div>'};
    var mine=a.calendar.filter(function(w){return w.mine}),rest=a.calendar.filter(function(w){return !w.mine}).sort(function(x,y){return x.start<y.start?-1:1});
    h+='<h4>Planting windows</h4>';
    if(mine.length)h+=mine.map(row).join("")+'<p class="help" style="margin:2px 0 0">'+esc(mine[0].note)+'</p>';
    else if(a.perennial)h+='<p class="help" style="margin:0">For perennial crops the main risk is frost at bud break and flowering. Watch the frost dates above.</p>';
    else h+='<p class="help" style="margin:0">Set this field’s crop in Field settings to see its window first.</p>';
    h+='<details class="why"><summary>All crops</summary>'+rest.map(row).join("")+'</details>';
  }
  if(a.normals&&a.normals.length)h+='<h4>Next three months, typical</h4>'+a.normals.map(function(n){return '<div class="logrow"><span><b>'+esc(n.month)+'</b> '+Math.round(n.tmax)+'°/'+Math.round(n.tmin)+'°'+(n.rain!=null?', about '+n.rain+' mm of rain':'')+'</span></div>'}).join("")+'<p class="help" style="margin:2px 0 0">Averages from past years, not a forecast.</p>';
  h+='<details class="why"><summary>Traditional moon planting</summary><p class="help" style="margin:6px 0 0">'+esc(a.moonTip)+'</p></details>';
  h+='<p class="help" style="margin:8px 0 0">Windows come from local weather history and common rules of thumb. Check local advice and your soil temperature before planting.</p>';
  return h;
}
async function loadAlmanac(f){
  var box=$("alm");if(!box)return;
  try{var a=await api("GET","almanac&id="+f.id);if(sel!==f.id||!$("alm"))return;$("alm").className="alm";$("alm").innerHTML=almanacHtml(a)}
  catch(e){if($("alm"))$("alm").textContent="The almanac is unavailable right now. "+e.message}
}

/* ---------- tabs ---------- */
var VIEWS=["Farms","Advisor","Labor"],AI_ON=false;
function showView(v){
  VIEWS.forEach(function(n){var el=$("view"+n);if(el)el.hidden=(n!==v)});
  Array.prototype.forEach.call(document.querySelectorAll("#tabs button"),function(b){b.className=b.getAttribute("data-view")===v?"on":""});
  if(v==="Advisor")openAdvisor();
  if(v==="Labor")openLabor();
}
Array.prototype.forEach.call(document.querySelectorAll("#tabs button"),function(b){b.addEventListener("click",function(){showView(b.getAttribute("data-view"))})});

/* ---------- voice ---------- */
var SR=window.SpeechRecognition||window.webkitSpeechRecognition,rec=null;
function speak(text){
  try{if(!window.speechSynthesis)return say("Reading aloud is not supported in this browser.",1);window.speechSynthesis.cancel();var u=new SpeechSynthesisUtterance(text);u.lang=navigator.language||"en-US";window.speechSynthesis.speak(u)}catch(e){}
}
$("briefSpeak").addEventListener("click",function(){if(!DATA)return;var b=DATA.briefing;speak(b.headline+" "+b.items.map(function(i){return i.text}).join(" "))});
function toggleMic(){
  if(!SR){say("Voice input is not supported in this browser. Use the microphone key on your keyboard instead.",1);return}
  if(rec){rec.stop();return}
  var base=$("aq").value?$("aq").value+" ":"";
  rec=new SR();rec.lang=navigator.language||"en-US";rec.interimResults=true;rec.continuous=false;
  $("aMic").textContent="⏹ Listening…";
  rec.onresult=function(e){$("aq").value=base+Array.prototype.map.call(e.results,function(r){return r[0].transcript}).join(" ")};
  rec.onerror=function(){say("Could not hear you. Check microphone permission and try again.",1)};
  rec.onend=function(){rec=null;$("aMic").textContent="🎤 Talk"};
  try{rec.start()}catch(e){rec=null;$("aMic").textContent="🎤 Talk"}
}
$("aMic").addEventListener("click",toggleMic);

/* ---------- AI advisor ---------- */
var aImg=null,CHATS=[];
function fillFarmSelects(){
  var opts=(DATA?DATA.farms:[]).map(function(f){return '<option value="'+f.id+'">'+esc(f.name)+'</option>'}).join("");
  var keep=$("aFarm").value;$("aFarm").innerHTML='<option value="0">All my farms</option>'+opts;if(keep)$("aFarm").value=keep;else if(sel)$("aFarm").value=String(sel);
  ["lFarmIn","mFarm"].forEach(function(id){var k=$(id).value;$(id).innerHTML='<option value="0">No specific farm</option>'+opts;if(k)$(id).value=k});
}
function openAdvisor(){
  fillFarmSelects();
  $("aiNote").textContent=AI_ON?"Ask by typing or talking. Add a photo of a leaf, pest or field for a closer look. Answers use your own farm data.":"The advisor is not switched on yet. Add an AI key (ANTHROPIC_API_KEY or GEMINI_API_KEY) in your hosting settings to turn it on.";
  loadChats();
}
async function loadChats(){
  try{var r=await api("GET","chats&farm="+(parseInt($("aFarm").value,10)||0));CHATS=r.chats;renderChats()}catch(e){say(e.message,1)}
}
function renderChats(){
  var box=$("chat");
  box.innerHTML=CHATS.length?CHATS.map(function(c,i){return '<div class="msg me">'+(c.image?'📷 ':'')+esc(c.question)+'</div><div class="msg ai">'+esc(c.answer)+'<div><button class="b alt sm" type="button" data-speak="'+i+'">🔊 Read aloud</button>'+(parseInt($("aFarm").value,10)?'<button class="b alt sm" type="button" data-savelog="'+i+'">Save to scouting log</button>':'')+'</div></div>'}).join(""):'<p class="help">No questions yet. Try one of the suggestions below.</p>';
  box.scrollTop=box.scrollHeight;
}
$("chat").addEventListener("click",async function(e){
  var b=e.target.closest("button");if(!b)return;
  if(b.hasAttribute("data-speak"))speak(CHATS[parseInt(b.getAttribute("data-speak"),10)].answer);
  if(b.hasAttribute("data-savelog")){
    var c=CHATS[parseInt(b.getAttribute("data-savelog"),10)],fid=parseInt($("aFarm").value,10);
    try{await api("POST","addlog",{farmId:fid,kind:"scouting",date:new Date().toISOString().slice(0,10),note:("Advisor: "+c.answer).slice(0,190)});say("Saved to the scouting log.")}catch(x){say(x.message,1)}
  }
});
$("aFarm").addEventListener("change",loadChats);
Array.prototype.forEach.call(document.querySelectorAll("[data-q]"),function(b){b.addEventListener("click",function(){$("aq").value=b.getAttribute("data-q")})});
function resizeImage(file,max){
  return new Promise(function(res,rej){
    var img=new Image(),url=URL.createObjectURL(file);
    img.onload=function(){var s=Math.min(1,max/Math.max(img.width,img.height)),c=document.createElement("canvas");c.width=Math.round(img.width*s);c.height=Math.round(img.height*s);c.getContext("2d").drawImage(img,0,0,c.width,c.height);URL.revokeObjectURL(url);res(c.toDataURL("image/jpeg",0.8).split(",")[1])};
    img.onerror=function(){URL.revokeObjectURL(url);rej(new Error("That photo could not be read."))};
    img.src=url;
  });
}
$("aImg").addEventListener("change",async function(){
  var f=this.files&&this.files[0];if(!f)return;
  try{aImg=await resizeImage(f,1280);$("aPrev").textContent="📷 Photo attached ("+Math.round(aImg.length*0.75/1024)+" KB). Tap Ask to send it."}catch(e){aImg=null;say(e.message,1)}
  this.value="";
});
$("aSend").addEventListener("click",async function(){
  var q=$("aq").value.trim();if(!q&&!aImg)return say("Type or say a question, or add a photo.",1);
  var b=this;b.disabled=true;say("Thinking…");
  try{
    var r=await api("POST","ask",{farmId:parseInt($("aFarm").value,10)||0,question:q,image:aImg,mediaType:"image/jpeg"});
    $("aq").value="";aImg=null;$("aPrev").textContent="";$("aLeft").textContent=r.remaining+" questions left today.";say("");await loadChats();
  }catch(e){say(e.message,1)}
  b.disabled=false;
});

/* ---------- labor ---------- */
var LABOR=null,TASKS=["Irrigating","Planting","Spraying","Weeding","Pruning","Harvesting","Packing","Maintenance","General"];
var money=function(v){return v.toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2})};
function elapsed(since){var m=Math.max(0,Math.round((Date.now()-new Date(since).getTime())/60000));return Math.floor(m/60)+" h "+(m%60)+" min"}
function openLabor(){
  fillFarmSelects();
  var to=TASKS.map(function(t){return '<option>'+t+'</option>'}).join("");
  if(!$("lTaskIn").options.length){$("lTaskIn").innerHTML=to;$("mTask").innerHTML=to;if(!$("mDate").value)$("mDate").value=new Date().toISOString().slice(0,10)}
  loadLabor();
}
async function loadLabor(){
  var days=parseInt($("lDays").value,10)||7;
  $("lCsv").href=API+"?r=laborcsv&days="+days;
  try{LABOR=await api("GET","labor&days="+days);renderLabor()}catch(e){say(e.message,1)}
}
function renderLabor(){
  var L=LABOR;
  $("lWorkers").innerHTML=L.workers.length?L.workers.map(function(w){return '<div class="logrow"><span><b>'+esc(w.name)+'</b>'+(w.role?' ('+esc(w.role)+')':'')+(w.rate!=null?', '+money(w.rate)+'/h':'')+(w.clockedIn?' · <b style="color:var(--ok)">working '+esc(elapsed(w.clockedIn.since))+(w.clockedIn.task?', '+esc(w.clockedIn.task):'')+'</b>':'')+'</span><span>'+(w.clockedIn?'<button class="b alt sm" type="button" style="margin:0 4px 0 0" data-out="'+w.id+'">Clock out</button>':'<button class="b sm" type="button" style="margin:0 4px 0 0" data-in="'+w.id+'">Clock in</button>')+'<button class="b alt sm" type="button" style="margin:0" data-rmw="'+w.id+'" aria-label="Remove '+esc(w.name)+'">×</button></span></div>'}).join(""):'<p class="help" style="margin:0">No workers yet. Add the first one below.</p>';
  $("mWorker").innerHTML=L.workers.map(function(w){return '<option value="'+w.id+'">'+esc(w.name)+'</option>'}).join("");
  var s='<p style="margin:0"><b>'+L.totalHours+' h</b> worked, <b>'+money(L.totalCost)+'</b> labor cost in the last '+L.days+' days.</p>';
  if(L.byFarm.length)s+='<h3>By farm</h3>'+L.byFarm.map(function(f){return '<div class="logrow"><span><b>'+esc(f.farm)+'</b>: '+f.hours+' h, '+money(f.cost)+(f.costPerHa!=null?' ('+money(f.costPerHa)+' per ha)':'')+'</span></div>'}).join("");
  if(L.byWorker.length)s+='<h3>By worker</h3>'+L.byWorker.map(function(w){return '<div class="logrow"><span><b>'+esc(w.worker)+'</b>: '+w.hours+' h, '+money(w.cost)+'</span></div>'}).join("");
  if(L.entries.length)s+='<h3>Entries</h3>'+L.entries.slice(0,40).map(function(e){return '<div class="logrow"><span>'+esc(e.start.slice(0,10))+' <b>'+esc(e.worker)+'</b> '+e.hours+' h'+(e.units?', '+e.units+' units':'')+(e.farm?', '+esc(e.farm):'')+(e.task?', '+esc(e.task):'')+(e.note?' · '+esc(e.note):'')+' = '+money(e.cost)+'</span><button type="button" data-dell="'+e.id+'" aria-label="Delete this entry">×</button></div>'}).join("");
  $("lSummary").innerHTML=s;
}
$("lWorkers").addEventListener("click",async function(e){
  var b=e.target.closest("button");if(!b)return;
  try{
    if(b.hasAttribute("data-in")){await api("POST","clockin",{workerId:parseInt(b.getAttribute("data-in"),10),farmId:parseInt($("lFarmIn").value,10)||0,task:$("lTaskIn").value});say("Clocked in.")}
    if(b.hasAttribute("data-out")){var r=await api("POST","clockout",{workerId:parseInt(b.getAttribute("data-out"),10)});say("Clocked out: "+r.hours+" hours recorded.")}
    if(b.hasAttribute("data-rmw")&&confirm("Remove this worker? Their past hours stay in your records."))await api("POST","delworker&id="+b.getAttribute("data-rmw"));
    await loadLabor();
  }catch(x){say(x.message,1)}
});
$("lSummary").addEventListener("click",async function(e){var b=e.target.closest("[data-dell]");if(!b)return;try{await api("POST","dellabor&id="+b.getAttribute("data-dell"));await loadLabor()}catch(x){say(x.message,1)}});
$("lDays").addEventListener("change",loadLabor);
$("wAdd").addEventListener("click",async function(){
  try{await api("POST","addworker",{name:$("wName").value,role:$("wRole").value,rate:$("wRate").value});$("wName").value="";$("wRole").value="";$("wRate").value="";say("Worker added.");await loadLabor()}catch(e){say(e.message,1)}
});
$("mSave").addEventListener("click",async function(){
  try{
    await api("POST","addlabor",{workerId:parseInt($("mWorker").value,10)||0,farmId:parseInt($("mFarm").value,10)||0,task:$("mTask").value,date:$("mDate").value,hours:$("mHours").value,units:$("mUnits").value,pieceRate:$("mPiece").value,note:$("mNote").value});
    ["mHours","mUnits","mPiece","mNote"].forEach(function(i){$(i).value=""});say("Saved.");await loadLabor();
  }catch(e){say(e.message,1)}
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

    def _can_aqas_admin(self):
        return self._same(self._bearer(), AQAS_ADMIN_TOKEN)

    def _aqas_gate(self):
        if not AQAS_ADMIN_TOKEN:
            self._json(503, {"error": "AQAS_ADMIN_TOKEN is not configured in the hosting settings."})
            return False
        if not self._can_aqas_admin():
            self._json(401, {"error": "AQAS admin token required."})
            return False
        return True

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

    def _read_json(self, limit=200_000):
        if "application/json" not in self.headers.get("Content-Type", ""):
            raise ValueError("Unsupported request.")
        n = int(self.headers.get("Content-Length") or 0)
        if n > limit:
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
            if r == "aqas":
                return self._send(200, AQAS_HTML.encode("utf-8"), "text/html; charset=utf-8", {"Cache-Control": "no-store"})
            if r == "health":
                return self._json(200, {"ok": True, "aqas": "phase-1-simulated"})
            if r in ("aqas-status", "aqas-events", "aqas-proposals", "aqas-health"):
                if not self._aqas_gate():
                    return
                if r == "aqas-health":
                    return self._json(200, aqas_health())
                snap = aqas_snapshot()
                if r == "aqas-events":
                    return self._json(200, {"events": snap["events"]})
                if r == "aqas-proposals":
                    return self._json(200, {"proposals": snap["pendingProposals"]})
                return self._json(200, snap)
            if r == "cron":
                if not self._can_cron():
                    return self._json(401, {"error": "Not allowed."})
                return self._json(200, run_daily())
            ensure_schema()
            user = self._user()
            if r == "me":
                return self._json(200, {"user": user, "inviteRequired": bool(INVITE_CODE), "ai": bool(ai_provider())})
            if r == "map":
                fid = self._query().get("id", "")
                rows = sql("SELECT m.png FROM fw_maps m JOIN fw_farms f ON f.id = m.farm_id "
                           "WHERE m.farm_id=$1 AND m.kind=$2 AND f.user_id=$3", (int(fid) if fid.isdigit() else 0, "ndmi", user["id"] if user else 0))
                if not user or not rows:
                    return self._json(404, {"error": "No map"})
                return self._send(200, base64.b64decode(rows[0]["png"]), "image/png", {"Cache-Control": "private, max-age=3600"})
            if r == "farms":
                if not user:
                    return self._json(401, {"error": "Please log in."})
                return self._json(200, farms_payload(user["id"]))
            if r in ("almanac", "chats", "labor", "laborcsv"):
                if not user:
                    return self._json(401, {"error": "Please log in."})
                q = self._query()
                num = lambda k, d: int(q[k]) if q.get(k, "").isdigit() else d
                if r == "almanac":
                    return self._json(200, almanac_payload(user["id"], num("id", 0)))
                if r == "chats":
                    return self._json(200, {"chats": list_chats(user["id"], num("farm", 0))})
                if r == "labor":
                    return self._json(200, labor_report(user["id"], num("days", 7)))
                return self._send(200, labor_csv(user["id"], num("days", 30)).encode("utf-8"), "text/csv; charset=utf-8",
                                  {"Content-Disposition": "attachment; filename=farm-watch-labor.csv", "Cache-Control": "no-store"})
            self._json(404, {"error": "not found"})
        except ValueError as e:
            self._json(400, {"error": str(e)})
        except Exception as e:
            self._fail(e)

    def do_POST(self):
        r = self._query().get("r", "")
        try:
            if r == "ask":
                ensure_schema()
                user = self._user()
                if not user:
                    return self._json(401, {"error": "Please log in."})
                data = self._read_json(1_600_000)
                return self._json(200, ask_advisor(user, int(data.get("farmId") or 0), data.get("question"),
                                                   data.get("image"), data.get("mediaType") or "image/jpeg"))
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
            if r.startswith("aqas-"):
                if not self._aqas_gate():
                    return
                ensure_aqas_schema()
                actor = "control-room-admin"
                if r == "aqas-propose":
                    agent = str(data.get("agent") or "").strip()
                    risk = str(data.get("risk") or "").lower().strip()
                    title = str(data.get("title") or "").strip()
                    rationale = str(data.get("rationale") or "").strip()
                    effect = str(data.get("expectedEffect") or "").strip()
                    change = str(data.get("change") or "").strip()
                    if agent not in ("ARAIAH", "Pluto", "Orion", "AQAS"):
                        raise ValueError("Choose a valid AQAS agent.")
                    if risk not in ("low", "medium", "high"):
                        raise ValueError("Risk must be low, medium, or high.")
                    if not title or not rationale or not effect:
                        raise ValueError("Title, rationale, and expected effect are required.")
                    sql("INSERT INTO aqas_proposals (created_at,created_by,agent,title,rationale,expected_effect,risk,proposed_change,status) "
                        "VALUES ($1,$2,$3,$4,$5,$6,$7,$8,'pending')",
                        (_aqas_now(), actor, agent, title[:180], rationale[:2000], effect[:1000], risk,
                         json.dumps({"description": change[:2000]}, ensure_ascii=False)))
                    aqas_event(actor, "proposal_created", title, agent, {"risk": risk})
                    return self._json(201, {"ok": True})
                if r == "aqas-decision":
                    try:
                        pid = int(data.get("id"))
                    except (TypeError, ValueError):
                        raise ValueError("Proposal id is required.")
                    decision = str(data.get("status") or "")
                    note = str(data.get("note") or "").strip()
                    if decision not in ("approved", "rejected"):
                        raise ValueError("Decision must be approved or rejected.")
                    if not note:
                        raise ValueError("A review note is required.")
                    rows = sql("SELECT id,agent,title,status,risk FROM aqas_proposals WHERE id=$1", (pid,))
                    if not rows:
                        raise ValueError("Proposal not found.")
                    if rows[0]["status"] != "pending":
                        raise ValueError("This proposal has already been reviewed.")
                    if decision == "approved" and rows[0]["risk"] == "high":
                        return self._json(409, {"error": "High-risk proposals require a second reviewer; that workflow is not enabled yet. Leave this proposal pending."})
                    sql("UPDATE aqas_proposals SET status=$1,reviewed_at=$2,reviewed_by=$3,review_note=$4 WHERE id=$5 AND status='pending'",
                        (decision, _aqas_now(), actor, note[:2000], pid))
                    aqas_event(actor, "proposal_" + decision, rows[0]["title"], rows[0]["agent"],
                               {"proposal_id": pid, "risk": rows[0]["risk"], "note": note[:500], "applied": False})
                    return self._json(200, {"ok": True, "decisionRecorded": True, "applied": False})
                if r == "aqas-agent-control":
                    agent = str(data.get("agent") or "").strip()
                    status = str(data.get("status") or "").strip()
                    if agent not in ("ARAIAH", "Pluto", "Orion"):
                        raise ValueError("Choose a valid agent.")
                    if status not in ("paused", "simulated"):
                        raise ValueError("Phase 1 agents can only be paused or simulated.")
                    sql("UPDATE aqas_agents SET status=$1,mode='simulated',updated_at=$2 WHERE agent=$3", (status, _aqas_now(), agent))
                    aqas_event(actor, "agent_control", f"Set {agent} to {status}; simulated mode only.", agent,
                               {"status": status, "mode": "simulated"})
                    return self._json(200, {"ok": True, "status": status, "mode": "simulated"})
                return self._json(404, {"error": "Unknown AQAS endpoint."})
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
                update_settings(user["id"], int(data.get("farmId") or 0), data.get("crop"), data.get("soil"), data.get("method"), data.get("flow"))
                return self._json(200, {"ok": True})
            if r == "feedback":
                add_feedback(user["id"], int(data.get("farmId") or 0), data.get("verdict"), data.get("note"))
                return self._json(201, {"ok": True})
            if r == "addworker":
                return self._json(201, {"id": add_worker(user["id"], data.get("name"), data.get("role"), data.get("rate"))})
            if r == "delworker":
                wid = self._query().get("id", "")
                if not wid.isdigit():
                    raise ValueError("Missing worker id.")
                sql("UPDATE fw_workers SET active=0 WHERE id=$1 AND user_id=$2", (int(wid), user["id"]))
                return self._json(200, {"deleted": True})
            if r == "clockin":
                return self._json(201, {"id": clock_in(user["id"], int(data.get("workerId") or 0), int(data.get("farmId") or 0), data.get("task"))})
            if r == "clockout":
                return self._json(200, {"hours": clock_out(user["id"], int(data.get("workerId") or 0))})
            if r == "addlabor":
                return self._json(201, {"id": add_labor(user["id"], int(data.get("workerId") or 0), int(data.get("farmId") or 0), data.get("task"),
                                                        data.get("date"), data.get("hours"), data.get("units"), data.get("pieceRate"), data.get("note"))})
            if r == "dellabor":
                lid = self._query().get("id", "")
                if not lid.isdigit():
                    raise ValueError("Missing entry id.")
                delete_labor(user["id"], int(lid))
                return self._json(200, {"deleted": True})
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
