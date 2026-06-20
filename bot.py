import os, sys, asyncio, aiohttp, aiofiles, json, zlib, hashlib
import time, uuid, random, re, tempfile
import aiosqlite
import socket, ipaddress 
from collections import OrderedDict 
from datetime import datetime, timedelta
from urllib.parse import urlparse, quote_plus, unquote
from functools import wraps
from typing import List, Dict, Optional

try:
    import pypdf
except ImportError:
    pypdf = None

from dotenv import load_dotenv
load_dotenv()

from bs4 import BeautifulSoup
from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client, filters
from pyrogram.types import (
    Message, InlineKeyboardMarkup, InlineKeyboardButton, CallbackQuery
)
from pyrogram.errors import FloodWait, MessageNotModified
import redis.asyncio as aioredis
import structlog

# ─────────────────────────────────────────────
#  LOGGING & NODE IDENTIFICATION 
# ─────────────────────────────────────────────
NODE_ID = os.getenv("NODE_ID", uuid.uuid4().hex[:8])

structlog.configure(
    processors=[
        structlog.processors.TimeStamper(fmt="%Y-%m-%d %H:%M:%S"),
        structlog.processors.JSONRenderer()
    ],
    logger_factory=structlog.PrintLoggerFactory()
)
log = structlog.get_logger().bind(node=NODE_ID)

# ─────────────────────────────────────────────
#  ENV CONFIG & PROXIES 
# ─────────────────────────────────────────────
_RAW_API_ID = os.getenv("API_ID", "0")
API_ID    = int(_RAW_API_ID) if str(_RAW_API_ID).strip().isdigit() else 0
API_HASH  = os.getenv("API_HASH", "")
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
MONGO_URI = os.getenv("MONGO_URI", "mongodb://localhost:27017/pharma_bot")
REDIS_URL = os.getenv("REDIS_URL", "redis://localhost:6379/0")
ADMIN_IDS = [int(x) for x in os.getenv("ADMIN_IDS", "0").split(",") if x.strip().isdigit()]
ALLOWED_USERS = [int(x) for x in os.getenv("ALLOWED_USERS", "").split(",") if x.strip().isdigit()]
PROXIES = [p for p in os.getenv("PROXIES", "").split(",") if p.strip()]
GOOGLE_SEARCH_API_KEY = os.getenv("GOOGLE_SEARCH_API_KEY", "")
GOOGLE_SEARCH_CX = os.getenv("GOOGLE_SEARCH_CX", "")

# ─────────────────────────────────────────────
#  STATE LOCKS & ENGINE COUNTERS
# ─────────────────────────────────────────────
STATE_LOCK = asyncio.Lock()
SQLITE_LOCK = asyncio.Lock()
DNS_CACHE = {}
DNS_CACHE_TTL = 3600
DNS_CACHE_LOCK = asyncio.Lock()
USER_DL_TIMESTAMPS = {}

PROXY_FAILS = {p: 0 for p in PROXIES}
PROXY_SUCCESS = {p: 0 for p in PROXIES}
PROXY_LATENCY = {p: 5.0 for p in PROXIES} 
DEAD_PROXIES = set()
PROXY_REVIVE_COUNTS = {p: 0 for p in PROXIES}
ABSOLUTE_DEAD_PROXIES = set()
PROXY_BLACKLIST_THRESHOLD = 10

DOMAIN_PROXY_STATS = {
    "google": {p: {"fails": 0, "success": 0, "latency": 5.0} for p in PROXIES},
    "bing":   {p: {"fails": 0, "success": 0, "latency": 5.0} for p in PROXIES},
    "ddg":    {p: {"fails": 0, "success": 0, "latency": 5.0} for p in PROXIES},
    "telegram":{p: {"fails": 0, "success": 0, "latency": 5.0} for p in PROXIES}
}

YEARS = list(range(2024, 2014, -1))

EXAM_TREE = {
    "AIIMS_CRE": {
        "label": "🏥 AIIMS CRE Pharmacist",
        "regions": [
            "AIIMS Delhi", "AIIMS Bhopal", "AIIMS Raipur", "AIIMS Rishikesh",
            "AIIMS Jodhpur", "AIIMS Patna", "AIIMS Bhubaneswar", "AIIMS Nagpur",
            "AIIMS Kalyani", "AIIMS Mangalagiri", "AIIMS Bibinagar",
            "AIIMS Gorakhpur", "AIIMS Rajkot", "AIIMS Deoghar",
        ],
    },
    "ESIC": {
        "label": "🏨 ESIC Pharmacist",
        "regions": [
            "ESIC Central", "ESIC Delhi", "ESIC Mumbai", "ESIC Chennai",
            "ESIC Kolkata", "ESIC Hyderabad", "ESIC Bengaluru",
        ],
    },
    "DSSSB": {
        "label": "🏛️ DSSSB Pharmacist",
        "regions": ["DSSSB Delhi"],
    },
    "RUHS": {
        "label": "🎓 RUHS Pharmacist",
        "regions": ["RUHS Rajasthan"],
    },
    "NHM": {
        "label": "🌿 NHM Pharmacist",
        "regions": [
            "NHM UP", "NHM MP", "NHM Bihar", "NHM Rajasthan",
            "NHM Maharashtra", "NHM Gujarat", "NHM Punjab",
        ],
    },
    "DRUG_INSPECTOR": {
        "label": "💊 Drug Inspector",
        "regions": [
            "Drug Inspector Central", "Drug Inspector UP", "Drug Inspector MP",
            "Drug Inspector Bihar", "Drug Inspector Rajasthan",
            "Drug Inspector Delhi", "Drug Inspector Maharashtra", "Drug Inspector Gujarat",
        ],
    },
    "GPAT": {
        "label": "📚 GPAT / NIPER",
        "regions": ["GPAT All India"],
    },
    "STATE_PHARMA": {
        "label": "🗺️ State PSC Pharmacist",
        "regions": [
            "UPPSC Pharmacist", "MPPSC Pharmacist", "BPSC Pharmacist",
            "RPSC Pharmacist", "HPSC Pharmacist", "KPSC Pharmacist",
            "TNPSC Pharmacist", "WBPSC Pharmacist", "SSC Pharmacist",
        ],
    },
}

MATERIAL_TYPES = {
    "pyq":      "📝 Previous Year Papers",
    "syllabus": "📋 Syllabus",
    "notes":    "📖 Study Notes / Material",
    "anskey":   "✅ Answer Keys",
    "mock":     "🎯 Mock Tests",
    "books":    "📗 Reference Books PDF",
}

TELEGRAM_CHANNELS = [
    "pharmacist_pyq", "pharma_exam_material", "aiims_pharmacist_pyq",
    "drug_inspector_notes", "pharmacy_exam_pdf", "gpat_material",
    "pharmacist_exam_zone", "pharma_study_hub",
]

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_4) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:124.0) Gecko/20100101 Firefox/124.0",
]

REGION_ID_MAP = {}
def get_region_hash(region_str: str) -> str:
    rh = hashlib.md5(region_str.encode()).hexdigest()[:8]
    REGION_ID_MAP[rh] = region_str
    if len(REGION_ID_MAP) > 1000:
        REGION_ID_MAP.pop(next(iter(REGION_ID_MAP)))
    return rh

# ─────────────────────────────────────────────
#  GLOBAL NETWORK STATE
# ─────────────────────────────────────────────
SESSION:    Optional[aiohttp.ClientSession] = None
REDIS:      Optional[aioredis.Redis]        = None
MONGO_DB                                    = None

DOWNLOAD_QUEUE     = asyncio.Queue(maxsize=1000)
DOWNLOAD_SEMAPHORE = asyncio.Semaphore(5)
SCRAPE_SEMAPHORE   = asyncio.Semaphore(8)   

DOMAIN_LIMITS = {
    "google": asyncio.Semaphore(2),
    "bing": asyncio.Semaphore(3),
    "ddg": asyncio.Semaphore(4),
    "telegram": asyncio.Semaphore(3)
}

DOMAIN_PENALTY = {"google": 0.0, "bing": 0.0, "ddg": 0.0, "telegram": 0.0}
DOMAIN_CIRCUIT_BREAKER = {"google": 0, "bing": 0, "ddg": 0, "telegram": 0}
CIRCUIT_TRIP_TIME = {"google": 0.0, "bing": 0.0, "ddg": 0.0, "telegram": 0.0}
CIRCUIT_STATE = {"google": "CLOSED", "bing": "CLOSED", "ddg": "CLOSED", "telegram": "CLOSED"}

def is_circuit_open(domain: str) -> bool:
    if CIRCUIT_STATE[domain] == "OPEN":
        if time.time() > CIRCUIT_TRIP_TIME.get(domain, 0):
            CIRCUIT_STATE[domain] = "HALF_OPEN"
            return False 
        return True
    return False

def trip_circuit(domain: str):
    DOMAIN_CIRCUIT_BREAKER[domain] += 1
    if DOMAIN_CIRCUIT_BREAKER[domain] > 5:
        CIRCUIT_STATE[domain] = "OPEN"
        CIRCUIT_TRIP_TIME[domain] = time.time() + 300 
        DOMAIN_CIRCUIT_BREAKER[domain] = 0 

def heal_circuit(domain: str):
    DOMAIN_CIRCUIT_BREAKER[domain] = 0
    if CIRCUIT_STATE[domain] in ["OPEN", "HALF_OPEN"]:
        CIRCUIT_STATE[domain] = "CLOSED"

ACTIVE_DL      = 0
BURST_WORKERS  = 0
MAX_BURST_WORKERS = 10 
MAX_TOTAL_WORKERS = 15
BURST_TASKS    = set()
LAST_BURST_TIME = 0.0
BURST_COOLDOWN = 30.0 

LOCAL_MEM_CACHE: Dict[str, Dict] = {}
CACHE_LOCK = asyncio.Lock()
TASK_REGISTRY = {"static_workers": set(), "burst_workers": set(), "background_loops": set()}

BOT_METRICS = {
    "total_searches": 0, "pdfs_downloaded": 0, "bytes_downloaded": 0, "api_fallback_hits": 0,
    "engine_errors": {"google": 0, "bing": 0, "ddg": 0, "telegram": 0}
}
MONGO_SYNCED_SIDS = set() 
DOWNLOAD_LATENCY_EMA = 0.0
EVENT_LOOP_LAG = 0.0
ACTIVE_DL_LOCK = asyncio.Lock()
QUEUE_PAUSED   = False
BOT_START_TIME = time.time()
LAST_BAN_CLEAR_TIME = time.time()

SESSION_MAP: Dict[str, bytes] = OrderedDict() 
SESSION_EXPIRY = {}
SESSION_LAST_ACCESSED: Dict[str, float] = {} 
SESSION_TTL = 3600
REDIS_DISABLED_WARNING = False

GLOBAL_BANS = set()
USER_VIOLATIONS = {}
USER_DL_COUNTS = {}
USER_DAILY_QUOTA = {}

# ─────────────────────────────────────────────
#  AIOSQLITE BACKUP LAYER
# ─────────────────────────────────────────────
SQLITE_DB_PATH = "sessions_spillover.db"

async def init_sqlite_spillover():
    async with SQLITE_LOCK:
        async with aiosqlite.connect(SQLITE_DB_PATH) as db:
            await db.execute('''CREATE TABLE IF NOT EXISTS spillover (sid TEXT PRIMARY KEY, data BLOB, ts REAL)''')
            await db.execute('''CREATE TABLE IF NOT EXISTS persistent_metrics (id TEXT PRIMARY KEY, data TEXT)''')
            await db.commit()

async def sqlite_save(sid: str, data: bytes):
    async with SQLITE_LOCK:
        try:
            async with aiosqlite.connect(SQLITE_DB_PATH) as db:
                await db.execute("REPLACE INTO spillover (sid, data, ts) VALUES (?, ?, ?)", (sid, data, time.time()))
                await db.commit()
        except Exception:
            pass

async def sqlite_load(sid: str) -> Optional[bytes]:
    async with SQLITE_LOCK:
        try:
            async with aiosqlite.connect(SQLITE_DB_PATH) as db:
                async with db.execute("SELECT data FROM spillover WHERE sid=?", (sid,)) as cursor:
                    row = await cursor.fetchone()
                    return row[0] if row else None
        except Exception:
            return None

async def save_persistent_metrics():
    payload = {"BOT_METRICS": BOT_METRICS, "USER_DAILY_QUOTA": USER_DAILY_QUOTA, "USER_DL_COUNTS": USER_DL_COUNTS}
    async with SQLITE_LOCK:
        try:
            async with aiosqlite.connect(SQLITE_DB_PATH) as db:
                await db.execute("REPLACE INTO persistent_metrics (id, data) VALUES (?, ?)", ("bot_metrics_v2", json.dumps(payload)))
                await db.commit()
        except Exception:
            pass

async def load_persistent_metrics():
    async with SQLITE_LOCK:
        try:
            async with aiosqlite.connect(SQLITE_DB_PATH) as db:
                async with db.execute("SELECT data FROM persistent_metrics WHERE id=?", ("bot_metrics_v2",)) as cursor:
                    row = await cursor.fetchone()
                    if row:
                        loaded = json.loads(row[0])
                        BOT_METRICS.update(loaded.get("BOT_METRICS", {}))
                        USER_DAILY_QUOTA.update(loaded.get("USER_DAILY_QUOTA", {}))
                        USER_DL_COUNTS.update(loaded.get("USER_DL_COUNTS", {}))
        except Exception:
            pass

def log_task_exception(task: asyncio.Task):
    try:
        task.result()
    except Exception as e:
        log.error("background_task_crashed", task_name=task.get_name(), err=str(e))

def create_safe_task(coro, name: str) -> asyncio.Task:
    task = asyncio.create_task(coro, name=name)
    task.add_done_callback(log_task_exception)
    return task

def dump_local_queue():
    items = []
    while not DOWNLOAD_QUEUE.empty():
        try:
            item = DOWNLOAD_QUEUE.get_nowait()
            if isinstance(item, tuple) and len(item) == 5:
                items.append({"chat_id": item[1], "url": item[2], "title": item[3], "user_id": item[4]})
            DOWNLOAD_QUEUE.task_done()
        except Exception:
            pass
    if items:
        try:
            with open("local_queue_backup.json", "w") as f:
                json.dump(items, f)
        except Exception:
            pass

def load_local_queue():
    if os.path.exists("local_queue_backup.json"):
        try:
            with open("local_queue_backup.json", "r") as f:
                items = json.load(f)
            for item in items:
                try:
                    DOWNLOAD_QUEUE.put_nowait(("restored_app", item["chat_id"], item["url"], item["title"], item["user_id"]))
                except asyncio.QueueFull:
                    break
            os.remove("local_queue_backup.json")
        except Exception:
            pass

# ─────────────────────────────────────────────
#  INITIALIZE BOT CLIENT
# ─────────────────────────────────────────────
app = Client("pharma_ultimate_v2", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN)

def safe(func):
    @wraps(func)
    async def wrapper(*args, **kwargs):
        user_id = None
        for a in args:
            if isinstance(a, (Message, CallbackQuery)):
                user_id = a.from_user.id
                break
        if ALLOWED_USERS and user_id and user_id not in ALLOWED_USERS and user_id not in ADMIN_IDS:
            return
        try:
            return await func(*args, **kwargs)
        except FloodWait as fw:
            await asyncio.sleep(fw.value + 1)
            return await func(*args, **kwargs)
        except (MessageNotModified, Exception):
            pass
    return wrapper

# ─────────────────────────────────────────────
#  ANTI-SPAM & REDIS CORE ENGINE
# ─────────────────────────────────────────────
async def is_rate_limited(user_id: int, prefix: str, ttl: int = 5) -> bool:
    async with STATE_LOCK:
        if user_id in GLOBAL_BANS: return True
    if not REDIS: return False
    key = f"rl:{prefix}:{user_id}"
    if await REDIS.get(key):
        async with STATE_LOCK:
            USER_VIOLATIONS[user_id] = USER_VIOLATIONS.get(user_id, 0) + 1
            if USER_VIOLATIONS[user_id] > 15: GLOBAL_BANS.add(user_id)
        return True
    await REDIS.setex(key, ttl, b"1")
    return False

async def redis_get(key: str) -> Optional[bytes]:
    if not REDIS: return None
    try: return await REDIS.get(key)
    except Exception: return None

async def redis_set(key: str, value: bytes, ttl: int = 7200):
    if not REDIS: return
    try: await REDIS.setex(key, ttl, value)
    except Exception: pass

def compress(data: list) -> bytes:
    return zlib.compress(json.dumps(data, ensure_ascii=False).encode("utf-8"), level=6)

def decompress(b: bytes) -> list:
    return json.loads(zlib.decompress(b).decode("utf-8"))

def make_search_id(exam_key: str, region: str, year: int, mat: str) -> str:
    return hashlib.sha256(f"{exam_key}|{region}|{year}|{mat}".encode()).hexdigest()[:24]

def make_search_id_v2(exam_key: str, region: str, year: int, mat: str, user_id=None) -> str:
    return hashlib.sha256(f"{exam_key}|{region}|{year}|{mat}|{user_id or 0}".encode()).hexdigest()[:24]

# ─────────────────────────────────────────────
#  SSRF PROTECTION SYSTEM
# ─────────────────────────────────────────────
async def async_valid_url(url: str) -> bool:
    try:
        p = urlparse(url)
        if p.scheme not in ("http", "https"): return False
        clean_host = (p.hostname or "").lower().strip("[]")
        async with DNS_CACHE_LOCK:
            if clean_host in DNS_CACHE and time.time() - DNS_CACHE[clean_host]['ts'] < DNS_CACHE_TTL:
                return DNS_CACHE[clean_host]['safe']
        addr_info = await asyncio.to_thread(socket.getaddrinfo, clean_host, None)
        is_safe = True
        for res in addr_info:
            ip = res[4][0]
            if ipaddress.ip_address(ip).is_private or ipaddress.ip_address(ip).is_loopback:
                is_safe = False
                break
        async with DNS_CACHE_LOCK:
            DNS_CACHE[clean_host] = {'safe': is_safe, 'ts': time.time()}
        return is_safe
    except Exception:
        return False

def valid_url(url: str) -> bool:
    try:
        p = urlparse(url)
        h = (p.hostname or "").lower().split(":")[0].strip("[]")
        return p.scheme in ("http", "https") and not (h in {"127.0.0.1", "0.0.0.0", "localhost"} or h.startswith("192.168."))
    except Exception:
        return False

class SSRFSenseResolver(aiohttp.ThreadedResolver):
    async def resolve(self, host, port=0, family=socket.AF_INET):
        ips = await super().resolve(host, port, family)
        for ip in ips:
            if ipaddress.ip_address(ip['host']).is_private or ipaddress.ip_address(ip['host']).is_loopback:
                raise ValueError("SSRF Attack Blocked")
        return ips

# ─────────────────────────────────────────────
#  SMART PROXY ROTATOR
# ─────────────────────────────────────────────
async def get_random_proxy() -> Optional[str]:
    async with STATE_LOCK:
        if not PROXIES: return None
        v = [p for p in PROXIES if p not in DEAD_PROXIES and PROXY_FAILS.get(p, 0) < 3]
        if not v:
            for p in PROXIES:
                if p not in DEAD_PROXIES: PROXY_FAILS[p] = 0
            v = [p for p in PROXIES if p not in DEAD_PROXIES]
        return random.choice(v) if v else None

async def get_domain_aware_proxy(domain: str) -> Optional[str]:
    if not PROXIES or domain not in DOMAIN_PROXY_STATS: return await get_random_proxy()
    async with STATE_LOCK:
        v = [p for p in PROXIES if p not in DEAD_PROXIES and DOMAIN_PROXY_STATS[domain][p]["fails"] < 3]
        return random.choice(v[:3]) if v else await get_random_proxy()

async def mark_proxy_failed(proxy: str):
    async with STATE_LOCK:
        if proxy and proxy in PROXY_FAILS:
            PROXY_FAILS[proxy] += 1
            if PROXY_FAILS[proxy] > PROXY_BLACKLIST_THRESHOLD: DEAD_PROXIES.add(proxy)

async def mark_proxy_success(proxy: str, latency: float):
    async with STATE_LOCK:
        if proxy and proxy in PROXY_FAILS:
            PROXY_FAILS[proxy] = 0
            PROXY_SUCCESS[proxy] += 1

# ─────────────────────────────────────────────
#  FIX #1: SESSION None guard in safe_get()
# ─────────────────────────────────────────────
async def safe_get(url: str, headers: Optional[dict] = None, timeout: Optional[aiohttp.ClientTimeout] = None, explicit_proxy: str = None, domain_marker: str = None, retries: int = 2) -> Optional[aiohttp.ClientResponse]:
    # FIX #1: Guard against SESSION being None (start_services() failure)
    if SESSION is None:
        log.warning("safe_get_called_before_session_init", url=url)
        return None
    if not await async_valid_url(url): return None
    h = headers or {"User-Agent": random.choice(USER_AGENTS)}
    t = timeout or aiohttp.ClientTimeout(total=25)
    for attempt in range(retries + 1):
        req_proxy = explicit_proxy or await get_random_proxy()
        start = time.time()
        try:
            resp = await SESSION.get(url, headers=h, timeout=t, allow_redirects=True, proxy=req_proxy)
            lat = time.time() - start
            if resp.status in (429, 403, 500, 502, 503, 504):
                await mark_proxy_failed(req_proxy)
                if attempt < retries: continue
            else:
                await mark_proxy_success(req_proxy, lat)
                return resp
        except Exception:
            await mark_proxy_failed(req_proxy)
            if attempt < retries: await asyncio.sleep(1)
    return None

def build_queries(exam_label: str, region: str, year: Optional[int], mat: str) -> List[str]:
    cl = re.sub(r"[^\w\s]", "", exam_label).strip()
    yr = str(year) if year else ""
    base = {
        "pyq": [f"{cl} {region} pharmacist previous year question paper {yr} pdf", f"{cl} pharmacist PYQ {yr} pdf download"],
        "syllabus": [f"{cl} pharmacist syllabus {yr} pdf", f"{cl} {region} pharmacist exam pattern syllabus"],
        "notes": [f"{cl} pharmacist study material {yr} pdf", f"{cl} pharmacist notes pdf download"],
        "anskey": [f"{cl} {region} pharmacist answer key {yr} pdf"],
        "mock": [f"{cl} pharmacist mock test {yr} pdf"],
        "books": [f"pharmacist competitive exam book pdf free download"]
    }
    return base.get(mat, base["pyq"])

# ─────────────────────────────────────────────
#  EXTREME ASYNC MULTI-ENGINE SCRAPER 
# ─────────────────────────────────────────────
async def scrape_ddg(query: str) -> List[Dict]:
    if is_circuit_open("ddg"): return []
    async with DOMAIN_LIMITS["ddg"], SCRAPE_SEMAPHORE:
        res = []
        try:
            url = "https://html.duckduckgo.com/html/?q=" + quote_plus(query + " filetype:pdf")
            resp = await safe_get(url, domain_marker="ddg")
            if not resp: return []
            async with resp:
                soup = BeautifulSoup(await resp.text(), "html.parser")
            for a in soup.find_all("a", class_="result__a"):
                href = a.get("href", "")
                if "uddg=" in href: href = unquote(href.split("uddg=")[1].split("&")[0])
                if href.startswith("http") and valid_url(href): res.append({"title": a.get_text(strip=True)[:140], "url": href, "source": "DDG"})
        except Exception: pass
        return res

async def scrape_bing(query: str) -> List[Dict]:
    if is_circuit_open("bing"): return []
    async with DOMAIN_LIMITS["bing"], SCRAPE_SEMAPHORE:
        res = []
        try:
            url = "https://www.bing.com/search?q=" + quote_plus(query + " filetype:pdf") + "&count=30"
            resp = await safe_get(url, domain_marker="bing")
            if not resp: return []
            async with resp:
                soup = BeautifulSoup(await resp.text(), "html.parser")
            for li in soup.find_all("li", class_="b_algo"):
                a = li.find("a")
                if a and valid_url(a.get("href", "")): res.append({"title": a.get_text(strip=True)[:140], "url": a["href"], "source": "Bing"})
        except Exception: pass
        return res

async def scrape_google(query: str) -> List[Dict]:
    if is_circuit_open("google"): return []
    async with DOMAIN_LIMITS["google"], SCRAPE_SEMAPHORE:
        res = []
        try:
            if GOOGLE_SEARCH_API_KEY and GOOGLE_SEARCH_CX:
                api_url = f"https://www.googleapis.com/customsearch/v1?key={GOOGLE_SEARCH_API_KEY}&cx={GOOGLE_SEARCH_CX}&q={quote_plus(query)}&fileType=pdf"
                resp = await safe_get(api_url)
                if resp:
                    async with resp:
                        d = await resp.json()
                        for item in d.get("items", []):
                            if valid_url(item.get("link", "")): res.append({"title": item.get("title", "")[:140], "url": item["link"], "source": "Google-API"})
            if len(res) >= 5: return res
            url = "https://www.google.com/search?q=" + quote_plus(query) + "&num=20&as_filetype=pdf"
            resp = await safe_get(url, domain_marker="google")
            if not resp: return res
            async with resp: html = await resp.text()
            soup = BeautifulSoup(html, "html.parser")
            for div in soup.find_all("div", class_="g"):
                a = div.find("a", href=True)
                if a and valid_url(a["href"]):
                    h3 = div.find("h3")
                    res.append({"title": h3.get_text(strip=True) if h3 else a["href"], "url": a["href"], "source": "Google"})
        except Exception: pass
        return res

async def scrape_telegram(keyword: str) -> List[Dict]:
    res = []
    kw_words = [w for w in keyword.lower().split() if len(w) > 3]
    for ch in TELEGRAM_CHANNELS:
        async with DOMAIN_LIMITS["telegram"], SCRAPE_SEMAPHORE:
            try:
                resp = await safe_get(f"https://t.me/s/{ch}")
                if not resp: continue
                async with resp: soup = BeautifulSoup(await resp.text(), "html.parser")
                for msg in soup.find_all("div", class_="tgme_widget_message_wrap"):
                    el = msg.find("div", class_="tgme_widget_message_text")
                    if el and any(w in el.get_text().lower() for w in kw_words):
                        a = msg.find("a", href=True)
                        res.append({"title": f"[TG @{ch}] {el.get_text()[:110]}", "url": a["href"] if a else f"https://t.me/{ch}", "source": "Telegram"})
            except Exception: pass
    return res

# ─────────────────────────────────────────────
#  ALGORITHMIC SCORING ENGINE & DUAL-CACHING
# ─────────────────────────────────────────────
async def full_search(exam_key: str, exam_label: str, region: str, year: Optional[int], mat: str) -> List[Dict]:
    BOT_METRICS["total_searches"] += 1 
    sid = make_search_id(exam_key, region, year or 0, mat)
    cached = await redis_get(f"res:{sid}")
    if cached: return decompress(cached)
    if MONGO_DB is not None:
        try:
            doc = await MONGO_DB.search_cache.find_one({"_id": sid})
            if doc:
                await redis_set(f"res:{sid}", doc["data"])
                return decompress(doc["data"])
        except Exception: pass

    queries = build_queries(exam_label, region, year, mat)
    tasks = [scrape_ddg(q) for q in queries[:3]] + [scrape_bing(q) for q in queries[:2]] + [scrape_google(queries[0]), scrape_telegram(f"{exam_label} {region}")]
    batch = await asyncio.gather(*tasks, return_exceptions=True)
    all_res = []
    for b in batch:
        if isinstance(b, list): all_res.extend(b)

    seen, scored = set(), []
    rank_kws = [w.lower() for w in exam_label.split() + region.split()]
    for item in all_res:
        u = item.get("url", "")
        if not u or u in seen or not valid_url(u): continue
        seen.add(u)
        score = 10 if ".pdf" in u.lower() else 0
        if any(g in u.lower() for g in ["gov.in", "nic.in", ".edu"]): score += 6
        score += sum(5 for w in rank_kws if w in item["title"].lower() or w in u.lower())
        item["score"] = score
        scored.append(item)
    
    scored.sort(key=lambda x: x["score"], reverse=True)
    final = scored[:100]
    if final:
        comp = compress(final)
        await redis_set(f"res:{sid}", comp)
        if MONGO_DB is not None:
            try: await MONGO_DB.search_cache.update_one({"_id": sid}, {"$set": {"data": comp, "ts": datetime.utcnow()}}, upsert=True)
            except Exception: pass
    return final

# ─────────────────────────────────────────────
#  DISTRIBUTED MEMORY RAM CACHE POOL
# ─────────────────────────────────────────────
async def store_session(sid: str, results: List[Dict]):
    compressed = compress(results)
    async with CACHE_LOCK:
        SESSION_MAP[sid] = compressed
        SESSION_EXPIRY[sid] = time.time() + SESSION_TTL
        SESSION_LAST_ACCESSED[sid] = time.time()
    if REDIS: await redis_set(f"session:{sid}", compressed, SESSION_TTL)
    if MONGO_DB is not None:
        try: await MONGO_DB.sessions.update_one({"_id": sid}, {"$set": {"data": compressed, "ts": datetime.utcnow()}}, upsert=True)
        except Exception: pass

async def load_session(sid: str) -> Optional[List[Dict]]:
    r_data = await redis_get(f"session:{sid}")
    if r_data: return decompress(r_data)
    async with CACHE_LOCK:
        if sid in SESSION_MAP:
            SESSION_LAST_ACCESSED[sid] = time.time()
            return decompress(SESSION_MAP[sid])
    disk = await sqlite_load(sid)
    if disk: return decompress(disk)
    if MONGO_DB is not None:
        doc = await MONGO_DB.sessions.find_one({"_id": sid})
        if doc: return decompress(doc["data"])
    return None

# ─────────────────────────────────────────────
#  UI INTERFACE KEYBOARDS
# ─────────────────────────────────────────────
def main_menu_kb(user_id: int) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(v["label"], callback_data=f"exam|{k}")] for k, v in EXAM_TREE.items()]
    rows.append([InlineKeyboardButton("🔍 Custom Search", callback_data="custom_search"), InlineKeyboardButton("ℹ️ Help", callback_data="help")])
    if user_id in ADMIN_IDS: rows.append([InlineKeyboardButton("⚙️ Admin Panel", callback_data="admin|dash")])
    return InlineKeyboardMarkup(rows)

def regions_kb(exam_key: str) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(f"📍 {r}", callback_data=f"region|{exam_key}|{get_region_hash(r)}")] for r in EXAM_TREE[exam_key]["regions"]]
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="back_main")])
    return InlineKeyboardMarkup(rows)

def years_kb(exam_key: str, region_hash: str) -> InlineKeyboardMarkup:
    rows, row = [], []
    for yr in YEARS:
        row.append(InlineKeyboardButton(str(yr), callback_data=f"mattype|{exam_key}|{region_hash}|{yr}"))
        if len(row) == 4: rows.append(row); row = []
    if row: rows.append(row)
    rows.append([InlineKeyboardButton("📅 All Years", callback_data=f"mattype|{exam_key}|{region_hash}|0")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data=f"exam|{exam_key}")])
    return InlineKeyboardMarkup(rows)

def mattype_kb(exam_key: str, region_hash: str, year: int) -> InlineKeyboardMarkup:
    rows = [[InlineKeyboardButton(label, callback_data=f"dosearch|{exam_key}|{region_hash}|{year}|{code}|1")] for code, label in MATERIAL_TYPES.items()]
    rows.append([InlineKeyboardButton("🔙 Back", callback_data=f"region|{exam_key}|{region_hash}")])
    return InlineKeyboardMarkup(rows)

# ─────────────────────────────────────────────
#  FIX #2: results_kb() — callback_data size guard (64 byte Telegram limit)
#  sid already hashed to 24 chars; exam_key max ~14, region_hash 8, year 4, mat 8
#  Total max ~65 chars — trimmed exam_key to 12 chars to stay safe
# ─────────────────────────────────────────────
def results_kb(results: List[Dict], page: int, exam_key: str, region_hash: str, year: int, mat: str, sid: str) -> InlineKeyboardMarkup:
    per_page, rows = 10, []
    start = (page - 1) * per_page
    sliced = results[start:start + per_page]
    icon_map = {"DDG": "🔷", "Bing": "🔶", "Google": "🔴", "Google-API": "🟢", "Telegram": "📱"}
    # Trim exam_key to 12 chars to keep callback_data within 64-byte Telegram limit
    ek_safe = exam_key[:12]
    for i, item in enumerate(sliced):
        icon = icon_map.get(item.get("source", ""), "🔗")
        short = item["title"][:35] + "..." if len(item["title"]) > 35 else item["title"]
        rows.append([
            InlineKeyboardButton(f"{icon} {short}", url=item["url"]),
            InlineKeyboardButton("📥 PDF", callback_data=f"dl|{sid}|{start+i}")
        ])
    nav = []
    if page > 1: nav.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"dosearch|{ek_safe}|{region_hash}|{year}|{mat}|{page-1}"))
    if start + per_page < len(results): nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"dosearch|{ek_safe}|{region_hash}|{year}|{mat}|{page+1}"))
    if nav: rows.append(nav)
    total_pages = -(-len(results) // per_page)
    rows.append([
        InlineKeyboardButton(f"📊 {page}/{total_pages} ({len(results)} items)", callback_data="noop"),
        InlineKeyboardButton("🔙 Menu", callback_data="back_main")
    ])
    return InlineKeyboardMarkup(rows)

# ─────────────────────────────────────────────
#  ADVANCED PDF SCANNER & DOWNLOAD WORKER
# ─────────────────────────────────────────────
def _cpu_bound_pdf_check(tmp_path):
    if not pypdf: return True
    try:
        r = pypdf.PdfReader(tmp_path)
        if len(r.pages) < 1: raise ValueError("Empty PDF")
        if len(r.pages) > 1000: raise ValueError("Page DOS Limit Exceeded")
        return True
    except Exception as e: raise ValueError(f"Malicious Structure: {e}")

async def worker_safe_send(c, chat_id, text):
    try: await c.send_message(chat_id, text)
    except Exception: pass

async def worker_safe_doc(c, chat_id, path, name, cap):
    try: await c.send_document(chat_id=chat_id, document=path, file_name=name, caption=cap)
    except Exception: pass

async def download_worker(stop_event: asyncio.Event):
    global ACTIVE_DL, DOWNLOAD_LATENCY_EMA
    while not stop_event.is_set():
        try: task = await asyncio.wait_for(DOWNLOAD_QUEUE.get(), timeout=2)
        except asyncio.TimeoutError: continue
        if not isinstance(task, tuple) or len(task) != 5:
            DOWNLOAD_QUEUE.task_done(); continue
        c_ref, chat_id, url, title, uid = task
        if c_ref in ("app_ref", "restored_app"): c_ref = app
        tmp_path = None
        try:
            async with DOWNLOAD_SEMAPHORE:
                async with ACTIVE_DL_LOCK: ACTIVE_DL += 1
                resp = await safe_get(url, timeout=aiohttp.ClientTimeout(total=90))
                if not resp:
                    await worker_safe_send(c_ref, chat_id, f"❌ Failed link: {url}")
                    continue
                async with resp:
                    size = 0
                    tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".pdf")
                    tmp_path = tmp.name; tmp.close()
                    async with aiofiles.open(tmp_path, "wb") as f:
                        async_content = resp.content.iter_chunked(8192)
                        async for chunk in async_content:
                            await f.write(chunk); size += len(chunk)
                            if size > 50*1024*1024: break
                
                async with aiofiles.open(tmp_path, "rb") as f_check:
                    magic = await f_check.read(4)
                    await f_check.seek(max(0, size - 128))
                    tail = await f_check.read()
                if magic != b"%PDF" or (b"%%EOF" not in tail and b"%EOF" not in tail):
                    await worker_safe_send(c_ref, chat_id, "⚠️ Invalid PDF signature structural block.")
                    continue
                
                if pypdf:
                    await asyncio.to_thread(_cpu_bound_pdf_check, tmp_path)
                
                safe_n = re.sub(r"[^\w\s\-]", "", title)[:60] + ".pdf"
                await worker_safe_doc(c_ref, chat_id, tmp_path, safe_n, f"📄 **{title[:150]}**\n🔗 {url[:60]}")
                BOT_METRICS["pdfs_downloaded"] += 1
                BOT_METRICS["bytes_downloaded"] += size

                # FIX #5: Use SETNX (SET NX EX) to prevent Redis job duplication race
                if REDIS and url:
                    jh = hashlib.sha256(url.encode()).hexdigest()
                    await REDIS.set(f"processed_job:{jh}", "1", ex=86400, nx=True)
        except Exception as e:
            await worker_safe_send(c_ref, chat_id, f"❌ Download error: `{str(e)[:50]}`")
        finally:
            async with ACTIVE_DL_LOCK: ACTIVE_DL = max(0, ACTIVE_DL - 1)
            async with STATE_LOCK: USER_DL_COUNTS[uid] = max(0, USER_DL_COUNTS.get(uid, 1) - 1)
            DOWNLOAD_QUEUE.task_done()
            if tmp_path and os.path.exists(tmp_path): os.remove(tmp_path)

# ─────────────────────────────────────────────
#  TELEGRAM ROUTING CONTROL & WORKERS
# ─────────────────────────────────────────────
@app.on_message(filters.command("start") & filters.private)
@safe
async def cmd_start_core(_, msg: Message):
    await msg.reply_text(f"👋 **Welcome {msg.from_user.first_name}!**\nSelect your target sector:", reply_markup=main_menu_kb(msg.from_user.id))

@app.on_message(filters.command("stats") & filters.private)
@safe
async def cmd_stats_core(_, msg: Message):
    await msg.reply_text(f"📊 **Engine Metrics:**\nSearches: `{BOT_METRICS['total_searches']}`\nPDFs: `{BOT_METRICS['pdfs_downloaded']}`\nQueue: `{DOWNLOAD_QUEUE.qsize()}`")

# ─────────────────────────────────────────────
#  FIX #3: cmd_search_core — explicit variable assignment (no operator precedence risk)
# ─────────────────────────────────────────────
@app.on_message(filters.command("search") & filters.private)
@safe
async def cmd_search_core(_, msg: Message):
    q = msg.text.replace("/search", "").strip()
    if not q: return await msg.reply_text("Usage: `/search exam_name`")
    w = await msg.reply_text("🔍 Multi-Engine scraping active...")
    ddg_res = await scrape_ddg(q)
    bing_res = await scrape_bing(q)
    res = ddg_res + bing_res
    if not res: return await w.edit_text("❌ No items found.")
    sid = make_search_id_v2("CUSTOM", q[:30], 0, "pyq", msg.from_user.id)
    await store_session(sid, res)
    await w.edit_text(f"Found **{len(res)}** results:", reply_markup=results_kb(res, 1, "CUSTOM", "CUSTOM", 0, "pyq", sid))

@app.on_callback_query()
@safe
async def router_callback(_, cq: CallbackQuery):
    d = cq.data
    if d == "back_main": return await cq.message.edit_text("Select sector:", reply_markup=main_menu_kb(cq.from_user.id))
    if d.startswith("exam|"):
        ek = d.split("|")[1]
        return await cq.message.edit_text("Select Region:", reply_markup=regions_kb(ek))
    if d.startswith("region|"):
        _, ek, rh = d.split("|")
        return await cq.message.edit_text("Select Year:", reply_markup=years_kb(ek, rh))
    if d.startswith("mattype|"):
        _, ek, rh, y = d.split("|")
        return await cq.message.edit_text("Select Category:", reply_markup=mattype_kb(ek, rh, int(y)))
    if d.startswith("dosearch|"):
        _, ek, rh, y, mat, p = d.split("|")
        r_str = REGION_ID_MAP.get(rh, rh)
        sid = make_search_id(ek, r_str, int(y), mat)
        res = await load_session(sid)
        if not res:
            res = await full_search(ek, EXAM_TREE.get(ek, {}).get("label", ek), r_str, int(y) or None, mat)
            await store_session(sid, res)
        if not res: return await cq.message.edit_text("❌ No structural data found.", reply_markup=main_menu_kb(cq.from_user.id))
        return await cq.message.edit_text("Scraped links:", reply_markup=results_kb(res, int(p), ek, rh, int(y), mat, sid))
    if d.startswith("dl|"):
        _, sid, idx = d.split("|")
        res = await load_session(sid)
        if not res: return await cq.answer("Session dead.", show_alert=True)
        item = res[int(idx)]
        async with STATE_LOCK:
            if USER_DAILY_QUOTA.get(cq.from_user.id, 0) >= 50: return await cq.answer("Daily 50 files exhausted.", show_alert=True)
            USER_DAILY_QUOTA[cq.from_user.id] = USER_DAILY_QUOTA.get(cq.from_user.id, 0) + 1
            USER_DL_COUNTS[cq.from_user.id] = USER_DL_COUNTS.get(cq.from_user.id, 0) + 1
        if REDIS:
            await REDIS.lpush("global_dl_queue", json.dumps({"chat_id": cq.message.chat.id, "url": item["url"], "title": item["title"], "user_id": cq.from_user.id}))
            await cq.answer("Dispatched to cluster.")
        else:
            # FIX #4: QueueFull guard — safe put with user-facing error
            try:
                DOWNLOAD_QUEUE.put_nowait((app, cq.message.chat.id, item["url"], item["title"], cq.from_user.id))
                await cq.answer("Queued on local engine loop.")
            except asyncio.QueueFull:
                await cq.answer("⚠️ Download queue full. Try again in a moment.", show_alert=True)

# ─────────────────────────────────────────────
#  BACKGROUND POOL PULLERS & RECOVERY
# ─────────────────────────────────────────────
async def redis_queue_puller_task():
    if not REDIS: return
    while True:
        try:
            item = await REDIS.brpoplpush("global_dl_queue", "processing_dl_queue", timeout=5)
            if item:
                p = json.loads(item)
                jh = hashlib.sha256(p['url'].encode()).hexdigest()
                if await REDIS.get(f"processed_job:{jh}"):
                    await REDIS.lrem("processing_dl_queue", 1, item); continue
                DOWNLOAD_QUEUE.put_nowait(("app_ref", p['chat_id'], p['url'], p['title'], p['user_id']))
                await REDIS.lrem("processing_dl_queue", 1, item)
        except Exception: await asyncio.sleep(2)

async def system_cleanup_loop():
    while True:
        await save_persistent_metrics()
        await asyncio.sleep(300)

# ─────────────────────────────────────────────
#  LIFECYCLE INITIALIZER
# ─────────────────────────────────────────────
STOP_EVENT = asyncio.Event()

async def start_services():
    global SESSION, REDIS, MONGO_DB
    await init_sqlite_spillover()
    await load_persistent_metrics()
    SESSION = aiohttp.ClientSession(connector=aiohttp.TCPConnector(resolver=SSRFSenseResolver(), ssl=True))
    try:
        REDIS = aioredis.from_url(REDIS_URL); await REDIS.ping()
    except Exception:
        REDIS = None
        log.warning("redis_unavailable_running_local_mode")
    try:
        c = AsyncIOMotorClient(MONGO_URI); MONGO_DB = c.get_database()
        await MONGO_DB.search_cache.create_index("ts", expireAfterSeconds=86400)
    except Exception:
        MONGO_DB = None
        log.warning("mongo_unavailable_running_without_persistent_cache")
    for _ in range(6): create_safe_task(download_worker(STOP_EVENT), "worker")
    create_safe_task(redis_queue_puller_task(), "puller")
    create_safe_task(system_cleanup_loop(), "cleaner")

# ─────────────────────────────────────────────
#  FIX #6: Graceful shutdown — close SESSION & REDIS properly
# ─────────────────────────────────────────────
async def shutdown_services():
    log.info("shutdown_initiated")
    STOP_EVENT.set()
    dump_local_queue()
    await save_persistent_metrics()
    if SESSION and not SESSION.closed:
        await SESSION.close()
        log.info("aiohttp_session_closed")
    if REDIS:
        await REDIS.aclose()
        log.info("redis_connection_closed")

async def main():
    if not all([API_ID, API_HASH, BOT_TOKEN]): sys.exit("Setup environment configurations correctly.")
    await start_services()
    load_local_queue()
    await app.start()
    log.info("System Engine fully synchronized.")
    try:
        await asyncio.Event().wait()
    except (KeyboardInterrupt, asyncio.CancelledError):
        pass
    finally:
        await app.stop()
        await shutdown_services()

if __name__ == "__main__":
    asyncio.run(main())