#!/usr/bin/env python3
"""
farmwatch: Sentinel-2 moisture pipeline for farm monitoring.

One process does everything: it serves the dashboard and the JSON feed, lets you add farms
from a web page, and fetches new satellite readings once a day in the background.

Commands
  python farmwatch.py serve             run the service (this is what Render runs)
  python farmwatch.py fetch             fetch new readings once and exit
  python farmwatch.py add-farm --name "North field" --crop Wheat --geojson north.geojson
  python farmwatch.py init              create the database

Environment variables
  CDSE_CLIENT_ID, CDSE_CLIENT_SECRET   OAuth client from the Copernicus Data Space dashboard
  ADMIN_TOKEN                          password for the /admin page (admin is disabled without it)
  FARMWATCH_DB                         database file (default farmwatch.db; on Render use /var/data/farmwatch.db)
  FETCH_EVERY_HOURS                    how often to check for new satellite passes (default 24)
  PORT                                 set automatically by Render
  ALLOWED_ORIGIN                       only needed if another website calls the API
  SMTP_HOST, SMTP_PORT, SMTP_USER, SMTP_PASS, ALERT_FROM, ALERT_TO   optional, enables email alerts
"""
import argparse
import hmac
import json
import math
import os
import smtplib
import sqlite3
import sys
import threading
import time
from contextlib import contextmanager
from datetime import date, timedelta
from email.message import EmailMessage
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import requests

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.environ.get("FARMWATCH_DB", "farmwatch.db")
ADMIN_TOKEN = os.environ.get("ADMIN_TOKEN", "")
FETCH_EVERY_HOURS = float(os.environ.get("FETCH_EVERY_HOURS", "24"))
TOKEN_URL = "https://identity.dataspace.copernicus.eu/auth/realms/CDSE/protocol/openid-connect/token"
STATS_URL = "https://sh.dataspace.copernicus.eu/api/v1/statistics"

THRESHOLDS = {"watch": 0.15, "dry": 0.05}  # NDMI cut-offs; tune per crop and growth stage
MIN_CLEAR = 0.5            # skip a pass if less than half of the farm is clear of cloud
MAX_TILE_CLOUD = 80        # skip scenes that are over 80% cloudy before processing
FIRST_LOOKBACK_DAYS = 30   # history to pull the first time a farm is fetched
RES_DEG = 0.0001           # about 10 m; pixel size in degrees
MAX_BBOX_DEG = 0.2         # reject farm boundaries wider or taller than about 20 km
API_SERIES_LENGTH = 60     # readings per farm sent to the dashboard

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
    if ndmi < THRESHOLDS["dry"]:
        return "Dry"
    if ndmi < THRESHOLDS["watch"]:
        return "Watch"
    return "Moist"


# ---------- database ----------

@contextmanager
def db():
    con = sqlite3.connect(DB_PATH, timeout=30)
    con.row_factory = sqlite3.Row
    try:
        yield con
        con.commit()
    finally:
        con.close()


def init_db():
    with db() as con:
        con.execute("PRAGMA journal_mode=WAL")
        con.executescript("""
        CREATE TABLE IF NOT EXISTS farms (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            crop TEXT,
            area_ha REAL,
            geometry TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS readings (
            farm_id INTEGER NOT NULL REFERENCES farms(id),
            date TEXT NOT NULL,
            ndmi REAL NOT NULL,
            ndvi REAL,
            clear_fraction REAL,
            PRIMARY KEY (farm_id, date)
        );
        """)


# ---------- farms ----------

def parse_polygon(g):
    """Accept a GeoJSON geometry, Feature or FeatureCollection holding one Polygon. Outer ring only."""
    try:
        if g.get("type") == "FeatureCollection":
            g = g["features"][0]
        if g.get("type") == "Feature":
            g = g["geometry"]
        if g.get("type") != "Polygon":
            raise ValueError("The boundary must be a single Polygon (draw one at geojson.io).")
        ring = [[float(p[0]), float(p[1])] for p in g["coordinates"][0]]
    except (AttributeError, KeyError, IndexError, TypeError):
        raise ValueError("That is not valid GeoJSON. Copy the full GeoJSON text from geojson.io.")
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


def insert_farm(name, crop, raw_geometry):
    geom = parse_polygon(raw_geometry)
    ha = area_ha(geom)
    with db() as con:
        cur = con.execute(
            "INSERT INTO farms (name, crop, area_ha, geometry) VALUES (?,?,?,?)",
            (name.strip(), (crop or "").strip(), ha, json.dumps(geom)))
        return cur.lastrowid, ha


def delete_farm(farm_id):
    with db() as con:
        con.execute("DELETE FROM readings WHERE farm_id=?", (farm_id,))
        con.execute("DELETE FROM farms WHERE id=?", (farm_id,))


# ---------- satellite fetch ----------

def get_token():
    cid, secret = os.environ.get("CDSE_CLIENT_ID"), os.environ.get("CDSE_CLIENT_SECRET")
    if not cid or not secret:
        sys.exit("Set CDSE_CLIENT_ID and CDSE_CLIENT_SECRET first.")
    r = requests.post(TOKEN_URL, data={
        "grant_type": "client_credentials", "client_id": cid, "client_secret": secret,
    }, timeout=30)
    r.raise_for_status()
    return r.json()["access_token"]


def request_stats(token, geometry, start, end):
    """One call returns daily NDMI/NDVI averages for the whole farm polygon."""
    body = {
        "input": {
            "bounds": {
                "geometry": geometry,
                "properties": {"crs": "http://www.opengis.net/def/crs/EPSG/0/4326"},
            },
            "data": [{
                "type": "sentinel-2-l2a",
                "dataFilter": {"mosaickingOrder": "leastCC", "maxCloudCoverage": MAX_TILE_CLOUD},
            }],
        },
        "aggregation": {
            "timeRange": {"from": f"{start}T00:00:00Z", "to": f"{end + timedelta(days=1)}T00:00:00Z"},
            "aggregationInterval": {"of": "P1D"},
            "evalscript": EVALSCRIPT,
            "resx": RES_DEG,
            "resy": RES_DEG,
        },
    }
    for attempt in range(3):
        r = requests.post(STATS_URL, json=body, headers={"Authorization": f"Bearer {token}"}, timeout=120)
        if r.status_code == 429:
            time.sleep(5 * (attempt + 1))
            continue
        r.raise_for_status()
        return r.json().get("data", [])
    raise RuntimeError("Rate limited by the Copernicus API; try again later.")


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
        out.append({
            "date": item["interval"]["from"][:10],
            "ndmi": round(ndmi, 4), "ndvi": round(ndvi, 4), "clear": round(clear, 2),
        })
    return out


def fetch_all():
    token = get_token()
    today = date.today()
    with db() as con:
        farms = con.execute("SELECT * FROM farms").fetchall()
    if not farms:
        print("No farms yet. Add one on the /admin page.")
        return
    for farm in farms:
        try:
            with db() as con:
                row = con.execute(
                    "SELECT date, ndmi FROM readings WHERE farm_id=? ORDER BY date DESC LIMIT 1",
                    (farm["id"],)).fetchone()
            start = date.fromisoformat(row["date"]) + timedelta(days=1) if row \
                else today - timedelta(days=FIRST_LOOKBACK_DAYS)
            if start > today:
                continue
            readings = parse_stats(request_stats(token, json.loads(farm["geometry"]), start, today))
            if not readings:
                print(f"{farm['name']}: no new clear pass yet")
                continue
            with db() as con:
                con.executemany(
                    "INSERT OR IGNORE INTO readings (farm_id,date,ndmi,ndvi,clear_fraction) VALUES (?,?,?,?,?)",
                    [(farm["id"], r["date"], r["ndmi"], r["ndvi"], r["clear"]) for r in readings])
            print(f"{farm['name']}: stored {len(readings)} new reading(s)")
            previous = status_of(row["ndmi"]) if row else None
            latest = max(readings, key=lambda r: r["date"])
            current = status_of(latest["ndmi"])
            if previous and STATUS_RANK[current] > STATUS_RANK[previous]:
                send_alert(farm["name"], farm["crop"], previous, current, latest)
        except Exception as e:  # one failing farm should not stop the rest
            print(f"{farm['name']}: failed ({e})")


FETCH_LOCK = threading.Lock()


def run_fetch():
    """Run a fetch unless one is already running; never raises."""
    if not FETCH_LOCK.acquire(blocking=False):
        print("A fetch is already running.")
        return False
    try:
        fetch_all()
    except SystemExit as e:
        print(e)
    except Exception as e:
        print("Fetch failed:", e)
    finally:
        FETCH_LOCK.release()
    return True


def scheduler():
    time.sleep(30)
    while True:
        run_fetch()
        time.sleep(FETCH_EVERY_HOURS * 3600)


# ---------- alerts ----------

def send_alert(name, crop, previous, current, reading):
    subject = f"{name} moved from {previous} to {current}"
    body = (f"{name} ({crop or 'crop not set'}) is now {current}.\n"
            f"Moisture index (NDMI): {reading['ndmi']:.2f} on {reading['date']}.\n"
            f"Check the dashboard for the trend.")
    print("ALERT:", subject)
    host, to = os.environ.get("SMTP_HOST"), os.environ.get("ALERT_TO")
    if not host or not to:
        return  # email not configured; the alert is only logged
    msg = EmailMessage()
    msg["Subject"], msg["To"] = subject, to
    msg["From"] = os.environ.get("ALERT_FROM", os.environ.get("SMTP_USER", "farmwatch@localhost"))
    msg.set_content(body)
    with smtplib.SMTP(host, int(os.environ.get("SMTP_PORT", "587"))) as s:
        s.starttls()
        if os.environ.get("SMTP_USER"):
            s.login(os.environ["SMTP_USER"], os.environ.get("SMTP_PASS", ""))
        s.send_message(msg)


# ---------- web service ----------

def farms_payload():
    out = []
    with db() as con:
        for f in con.execute("SELECT * FROM farms ORDER BY name"):
            rows = con.execute(
                "SELECT date, ndmi, ndvi FROM readings WHERE farm_id=? ORDER BY date DESC LIMIT ?",
                (f["id"], API_SERIES_LENGTH)).fetchall()
            if not rows:
                continue  # the dashboard needs at least one reading per farm
            out.append({
                "id": f["id"], "name": f["name"], "crop": f["crop"], "areaHa": f["area_ha"],
                "series": [dict(r) for r in reversed(rows)],
            })
    return {"farms": out}


def admin_farms():
    with db() as con:
        rows = con.execute(
            "SELECT f.id, f.name, f.crop, f.area_ha, "
            "(SELECT MAX(date) FROM readings WHERE farm_id=f.id) AS last_reading "
            "FROM farms f ORDER BY f.name").fetchall()
    return {"farms": [{"id": r["id"], "name": r["name"], "crop": r["crop"],
                       "areaHa": r["area_ha"], "lastReading": r["last_reading"]} for r in rows]}


PAGES = {"/": "index.html", "/index.html": "index.html", "/admin": "admin.html"}


class Handler(BaseHTTPRequestHandler):
    def send(self, code, body, ctype="application/json"):
        if not isinstance(body, bytes):
            body = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype + ("; charset=utf-8" if ctype.startswith("text") else ""))
        self.send_header("Content-Length", str(len(body)))
        origin = os.environ.get("ALLOWED_ORIGIN")
        if origin:
            self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Access-Control-Allow-Headers", "Authorization, Content-Type")
            self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
        self.end_headers()
        self.wfile.write(body)

    def authed(self):
        if not ADMIN_TOKEN:
            self.send(503, {"error": "Admin is disabled. Set the ADMIN_TOKEN setting first."})
            return False
        auth = self.headers.get("Authorization", "")
        given = auth[7:] if auth.startswith("Bearer ") else ""
        if not hmac.compare_digest(given.encode(), ADMIN_TOKEN.encode()):
            self.send(401, {"error": "Wrong admin token."})
            return False
        return True

    def read_json(self):
        n = int(self.headers.get("Content-Length") or 0)
        if n > 1_000_000:
            raise ValueError("Request too large.")
        return json.loads(self.rfile.read(n) or b"{}")

    def do_OPTIONS(self):
        self.send(204, b"")

    def do_GET(self):
        path = self.path.split("?")[0]
        if path in PAGES:
            try:
                with open(os.path.join(BASE_DIR, PAGES[path]), "rb") as f:
                    return self.send(200, f.read(), "text/html")
            except FileNotFoundError:
                return self.send(404, {"error": "Page file missing from the deployment."})
        if path == "/api/farms":
            return self.send(200, farms_payload())
        if path == "/health":
            return self.send(200, {"ok": True})
        if path == "/api/admin/farms":
            if self.authed():
                self.send(200, admin_farms())
            return
        self.send(404, {"error": "not found"})

    def do_POST(self):
        path = self.path.split("?")[0]
        if not self.authed():
            return
        try:
            if path == "/api/admin/farms":
                data = self.read_json()
                name = (data.get("name") or "").strip()
                if not name:
                    raise ValueError("Give the farm a name.")
                farm_id, ha = insert_farm(name, data.get("crop"), data.get("geometry"))
                return self.send(201, {"id": farm_id, "areaHa": ha})
            if path == "/api/admin/fetch":
                threading.Thread(target=run_fetch, daemon=True).start()
                return self.send(202, {"started": True})
        except (ValueError, json.JSONDecodeError) as e:
            return self.send(400, {"error": str(e)})
        self.send(404, {"error": "not found"})

    def do_DELETE(self):
        path = self.path.split("?")[0]
        if not self.authed():
            return
        prefix = "/api/admin/farms/"
        if path.startswith(prefix) and path[len(prefix):].isdigit():
            delete_farm(int(path[len(prefix):]))
            return self.send(200, {"deleted": True})
        self.send(404, {"error": "not found"})

    def log_message(self, *a):
        pass


def serve(port):
    init_db()
    threading.Thread(target=scheduler, daemon=True).start()
    print(f"Serving on port {port}. Satellite check every {FETCH_EVERY_HOURS:g} hours.")
    if not ADMIN_TOKEN:
        print("ADMIN_TOKEN is not set, so the /admin page is disabled.")
    ThreadingHTTPServer(("0.0.0.0", port), Handler).serve_forever()


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("init")
    a = sub.add_parser("add-farm")
    a.add_argument("--name", required=True)
    a.add_argument("--crop", default="")
    a.add_argument("--geojson", required=True)
    sub.add_parser("fetch")
    s = sub.add_parser("serve")
    s.add_argument("--port", type=int, default=int(os.environ.get("PORT", 8000)))
    args = p.parse_args()

    init_db()
    if args.cmd == "init":
        print(f"Database ready: {DB_PATH}")
    elif args.cmd == "add-farm":
        with open(args.geojson) as f:
            try:
                farm_id, ha = insert_farm(args.name, args.crop, json.load(f))
            except ValueError as e:
                sys.exit(str(e))
        print(f"Added '{args.name}' (id {farm_id}, about {ha} ha)")
    elif args.cmd == "fetch":
        run_fetch()
    elif args.cmd == "serve":
        serve(args.port)


if __name__ == "__main__":
    main()
