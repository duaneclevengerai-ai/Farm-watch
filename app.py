"""
Farm Watch: a complete farm monitoring website in one file (Python, no extra packages).
Runs on Render (python app.py) or Vercel (api/index.py).

What it does
  - People create accounts and log in. Each person sees only their own farms.
  - Farmers add a farm by tapping its corners on a satellite map.
  - Every day it fetches Copernicus Sentinel-2 readings (moisture index NDMI, vegetation index NDVI),
    skipping cloudy passes, and fetches a 7-day weather forecast for each farm.
  - It turns that into irrigation advice, stress and disease-risk flags, good spraying days,
    and a morning briefing (shown on the page and, if email is set up, emailed).

Settings (Render: Environment tab. Vercel: Project > Settings > Environment Variables)
  DATABASE_URL         Neon Postgres connection string                       (required)
  CDSE_CLIENT_ID       Copernicus Data Space OAuth client ID                 (required for satellite data)
  CDSE_CLIENT_SECRET   Copernicus Data Space OAuth client secret             (required for satellite data)
  ADMIN_TOKEN          password the daily timer uses to call /?r=cron        (required for automation)
  INVITE_CODE          optional; if set, people need this code to sign up
  SESSION_SECRET       optional; random text used to sign login cookies
  OPEN_METEO_API_KEY   optional; Open-Meteo's free service is for non-commercial use, set this for paid use
  SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASS, ALERT_FROM   optional, enables emailed alerts and briefings
  NDMI_WATCH, NDMI_DRY optional moisture thresholds, default 0.15 and 0.05
"""
import base64
import hashlib
import hmac
import json
import math
import os
import re
import smtplib
import sys
import time
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


def insert_farm(user_id, name, crop, raw_geometry):
    if int(sql("SELECT COUNT(*) AS n FROM fw_farms WHERE user_id=$1", (user_id,))[0]["n"]) >= MAX_FARMS_PER_USER:
        raise ValueError(f"You can have up to {MAX_FARMS_PER_USER} farms on one account.")
    geom = parse_polygon(raw_geometry)
    ha, (lat, lon) = area_ha(geom), centroid(geom)
    rows = sql("INSERT INTO fw_farms (user_id, name, crop, area_ha, lat, lon, geometry) "
               "VALUES ($1,$2,$3,$4,$5,$6,$7) RETURNING id",
               (user_id, name.strip()[:80], (crop or "").strip()[:60], ha, lat, lon, json.dumps(geom)))
    return int(rows[0]["id"]), ha


def delete_farm(user_id, farm_id):
    sql("DELETE FROM fw_farms WHERE id=$1 AND user_id=$2", (farm_id, user_id))  # cascades to readings


# ---------- weather forecast (Open-Meteo) ----------

def fetch_forecast_remote(lat, lon):
    key = os.environ.get("OPEN_METEO_API_KEY", "")
    base = ("https://customer-api.open-meteo.com" if key else "https://api.open-meteo.com") + "/v1/forecast"
    q = {"latitude": f"{lat:.4f}", "longitude": f"{lon:.4f}", "timezone": "auto", "forecast_days": "7",
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
      ("lemon", 0.65)]
DEFAULT_KC = 0.85  # typical mid-season crop coefficients; tune per crop and growth stage


def kc_for(crop):
    c = (crop or "").lower()
    for word, k in KC:
        if word in c:
            return k
    return DEFAULT_KC


def wd(iso):
    return datetime.strptime(iso, "%Y-%m-%d").strftime("%a")


def irrigation_advice(crop, status, days):
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


def farm_view(f, readings, days):
    last = readings[-1] if readings else None
    status = status_of(last["ndmi"]) if last else None
    flags, spray = risk_flags(readings, days)
    return {"id": int(f["id"]), "name": f["name"], "crop": f["crop"] or "", "areaHa": _f(f["area_ha"]),
            "geometry": json.loads(f["geometry"]), "series": readings, "status": status,
            "forecast": days, "advice": irrigation_advice(f["crop"], status, days),
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
    need = sum(1 for f in farms if f["advice"]["action"] in ("Irrigate", "Plan") or any(r["level"] in ("High", "Check") for r in f["risks"]))
    head = (f"{need} of {len(farms)} farm{'s' if len(farms) != 1 else ''} need attention today." if need
            else f"All {len(farms)} farm{'s' if len(farms) != 1 else ''} look fine today.") if farms else "Add a farm to get your daily briefing."
    return {"headline": head, "items": items}


def farms_payload(user_id):
    ensure_schema()
    farms = sql("SELECT id, name, crop, area_ha, lat, lon, geometry FROM fw_farms WHERE user_id=$1 ORDER BY name", (user_id,))
    rows = sql("SELECT r.farm_id, r.date, r.ndmi, r.ndvi FROM ("
               "SELECT farm_id, date, ndmi, ndvi, ROW_NUMBER() OVER (PARTITION BY farm_id ORDER BY date DESC) AS rn "
               "FROM fw_readings WHERE farm_id IN (SELECT id FROM fw_farms WHERE user_id=$1)) r "
               "WHERE r.rn <= $2 ORDER BY r.farm_id, r.date", (user_id, SERIES_LEN))
    by = {}
    for r in rows:
        by.setdefault(int(r["farm_id"]), []).append({"date": r["date"], "ndmi": _f(r["ndmi"]), "ndvi": _f(r["ndvi"])})
    with ThreadPoolExecutor(max_workers=5) as pool:
        forecasts = list(pool.map(lambda f: get_forecast(int(f["id"]), _f(f["lat"]), _f(f["lon"])), farms))
    views = [farm_view(f, by.get(int(f["id"]), []), fc) for f, fc in zip(farms, forecasts)]
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


def fetch_all(user_id=None):
    """Fetch new satellite readings for one person's farms (or everyone's), in parallel."""
    t0 = time.time()
    token = get_token()
    cols = "f.id, f.name, f.crop, f.geometry, u.email, u.email_briefing"
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

    def work(farm):
        name, fid = farm["name"], int(farm["id"])
        try:
            if time.time() - t0 > FETCH_BUDGET_S:
                return f"{name}: skipped, out of time (it will continue on the next run)", 0, None
            prev = last.get(fid)
            start = date.fromisoformat(prev["date"]) + timedelta(days=1) if prev \
                else today - timedelta(days=FIRST_LOOKBACK_DAYS)
            if start > today:
                return f"{name}: already up to date", 0, None
            readings = parse_stats(request_stats(token, json.loads(farm["geometry"]), start, today))
            if not readings:
                return f"{name}: no new clear pass yet", 0, None
            marks, params = [], []
            for i, r in enumerate(readings):
                marks.append("(" + ",".join(f"${i * 5 + k}" for k in range(1, 6)) + ")")
                params += [fid, r["date"], r["ndmi"], r["ndvi"], r["clear"]]
            stored = sql("INSERT INTO fw_readings (farm_id, date, ndmi, ndvi, clear_fraction) VALUES "
                         + ",".join(marks) + " ON CONFLICT DO NOTHING RETURNING farm_id", params)
            alert = None
            newest = max(readings, key=lambda r: r["date"])
            if prev and _f(prev["ndmi"]) is not None:
                before, now = status_of(_f(prev["ndmi"])), status_of(newest["ndmi"])
                if STATUS_RANK[now] > STATUS_RANK[before]:
                    alert = (farm["email"], name, farm["crop"], before, now, newest)
            return f"{name}: stored {len(stored)} new reading(s)", len(stored), alert
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
input[type=text],input[type=email],input[type=password],input:not([type]){width:100%;padding:11px;border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--ink);font:inherit}
.b{font:inherit;font-weight:600;padding:10px 14px;border-radius:8px;border:0;background:var(--wet);color:#fff;cursor:pointer;min-height:44px;margin:8px 8px 0 0}
.b.alt{background:transparent;color:var(--ink);border:1px solid var(--line)}
.b.danger{background:transparent;color:var(--dry);border:1px solid var(--line)}
.b:disabled{opacity:.55;cursor:default}
button:focus-visible,input:focus-visible,.item:focus-visible{outline:2px solid var(--wet);outline-offset:2px}
.auth{max-width:400px;margin:24px auto}
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
    <label for="em">Email</label><input id="em" type="email" autocomplete="email">
    <label for="pw">Password</label><input id="pw" type="password" autocomplete="current-password">
    <div id="invRow" hidden><label for="inv">Invite code</label><input id="inv" autocomplete="off"></div>
    <button id="authGo" class="b" type="button">Log in</button>
    <button id="authSwap" class="b alt" type="button">Create an account</button>
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
    <p class="note"><label style="display:inline;margin:0"><input id="emailPref" type="checkbox"> Email me the morning briefing and moisture alerts</label></p>
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
var INVITE=false;
function showAuth(){
  $("app").hidden=true;$("who").hidden=true;$("auth").hidden=false;
  var su=mode==="signup";
  $("authTitle").textContent=su?"Create your account":"Log in";$("authGo").textContent=su?"Create account":"Log in";
  $("authSwap").textContent=su?"I already have an account":"Create an account";
  $("nameRow").hidden=!su;$("invRow").hidden=!(su&&INVITE);
  $("pw").setAttribute("autocomplete",su?"new-password":"current-password");
}
$("authSwap").addEventListener("click",function(){mode=mode==="login"?"signup":"login";$("authErr").textContent="";showAuth()});
$("authGo").addEventListener("click",async function(){
  $("authErr").textContent="";$("authGo").disabled=true;
  try{
    await api("POST",mode,{email:$("em").value,password:$("pw").value,name:$("nm").value,invite:$("inv").value});
    $("pw").value="";await enter();
  }catch(e){$("authErr").textContent=e.message}
  $("authGo").disabled=false;
});
$("pw").addEventListener("keydown",function(e){if(e.key==="Enter")$("authGo").click()});
$("logout").addEventListener("click",async function(){try{await api("POST","logout")}catch(e){}DATA=null;sel=null;showAuth()});

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
  var pl=L.polygon(ring,{color:HEX[lab(f)],weight:3,fillOpacity:0.15}).addTo(dmap);
  dmap.fitBounds(pl.getBounds(),{padding:[24,24]});
}
function show(i){
  var f=DATA.farms[i];sel=f.id;armed=null;
  Array.prototype.forEach.call(document.querySelectorAll("#list button"),function(b){b.setAttribute("aria-current",b.getAttribute("data-id")==String(f.id))});
  var l=lastOf(f),a=f.advice,h='';
  h+='<div class="row"><div><h2 style="margin:0">'+esc(f.name)+'</h2><div class="sub">'+esc(f.crop||"Crop not set")+(f.areaHa?", "+f.areaHa+" ha":"")+'</div></div><span class="pill" style="color:'+COL[lab(f)]+'">'+lab(f)+'</span></div>';
  h+='<div id="dmap"></div>';
  h+='<div class="adv" style="border-color:'+(ACOL[a.action]||"var(--mute)")+'"><b>'+esc(a.headline)+'</b>'+esc(a.detail)+(a.weekRainMm!=null?'<div class="sub" style="margin-top:4px">Next 7 days: rain about '+Math.round(a.weekRainMm)+' mm, crop water use about '+Math.round(a.weekEtMm)+' mm</div>':'')+'</div>';
  if(f.forecast&&f.forecast.length){
    h+='<h3>7-day forecast</h3><div class="fc">'+f.forecast.map(function(d){return '<div><b>'+wd(d.date)+'</b>'+Math.round(d.rain)+' mm<br>'+Math.round(d.tmax)+'°/'+Math.round(d.tmin)+'°</div>'}).join("")+'</div>';
  }else h+='<p class="help">The weather forecast is unavailable right now.</p>';
  h+='<h3>Pest, disease and stress watch</h3>';
  h+=f.risks.length?f.risks.map(function(r){var c=r.level==="High"?"var(--dry)":r.level==="Info"?"var(--mute)":"var(--watch)";return '<div class="risk"><i style="color:'+c+'">'+esc(r.kind)+' ('+esc(r.level)+')</i><span>'+esc(r.text)+'</span></div>'}).join(""):'<p class="help" style="margin:4px 0 0">No warning signs right now.</p>';
  if(f.forecast&&f.forecast.length)h+='<p class="help" style="margin:8px 0 0">'+(f.sprayDays.length?"Good spraying days (calm and dry): "+f.sprayDays.join(", ")+".":"No calm, dry spraying day in the next 5 days.")+'</p>';
  if(l){
    var prev=f.series.length>1?f.series[f.series.length-2]:l,d=l.ndmi-prev.ndmi;
    h+='<h3>Satellite readings</h3><div class="stats"><div><b>'+l.ndmi.toFixed(2)+'</b><span>Moisture index (NDMI)</span></div><div><b>'+(d>0?"+":"")+d.toFixed(2)+'</b><span>Since previous pass</span></div><div><b>'+(l.ndvi==null?"n/a":l.ndvi.toFixed(2))+'</b><span>Greenness (NDVI)</span></div><div><b>'+esc(ago(l.date))+'</b><span>Latest clear image</span></div></div>'+chart(f.series);
  }else h+='<p class="help">No clear satellite image yet. Tap Update satellite data. Passes happen about every 5 days and cloudy ones are skipped.</p>';
  h+='<button class="b danger" type="button" id="del">'+(armed===f.id?"Tap again to delete":"Delete farm")+'</button>';
  $("detail").innerHTML=h;drawDetailMap(f);
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
  if(!farms.length){$("detail").innerHTML='<p class="help" style="margin:0">Add your first farm to see satellite moisture, the 7-day forecast and irrigation advice.</p>';return}
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

enter().catch(function(e){say("Could not load Farm Watch. "+e.message,1)});
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
