import async_timeout
from dotenv import load_dotenv
load_dotenv(".env")

from dotenv import load_dotenv
load_dotenv()

import os
import sys
import asyncio
import aiohttp
from aiohttp import web
import re
import time
import uuid
import zlib
import json
import hashlib
import random
import tempfile
from datetime import datetime
from urllib.parse import urlparse
from functools import wraps
from bs4 import BeautifulSoup

# --- Pyrogram & Advanced DB Drivers ---
from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client, filters
from pyrogram.types import (
    Message, InlineKeyboardMarkup, InlineKeyboardButton, 
    CallbackQuery, InlineQueryResultArticle, InputTextMessageContent
)
from pyrogram.errors import FloodWait, MessageNotModified
import aiofiles
import redis.asyncio as aioredis
import structlog

# ================= 1. ENTERPRISE JSON STRUCTURED LOGGING =================
structlog.configure(
    processors=[
        structlog.processors.TimeStamper(fmt="%Y-%m-%d %H:%M:%S"),
        structlog.processors.JSONRenderer()
    ],
    logger_factory=structlog.PrintLoggerFactory()
)
logger = structlog.get_logger()

# ================= 2. STRICT RUNTIME ENVIRONMENT VALIDATION =================
REQUIRED_ENV_VARS = ["API_ID", "API_HASH", "BOT_TOKEN", "MONGO_URI", "REDIS_URL"]
missing_vars = [v for v in REQUIRED_ENV_VARS if not os.getenv(v)]
if missing_vars:
    logger.error("CRITICAL CONFIGURATION ERROR: Pinned variables missing from environment.", missing=missing_vars)
    # Local fallback allocation to prevent sudden absolute scripts block during development
    pass

API_ID = int(os.getenv("API_ID", ""))
API_HASH = os.getenv("API_HASH", "")
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
MONGO_URI = os.getenv("MONGO_URI", "mongodb://localhost:27017/pharma_prod")
REDIS_URL = os.getenv("REDIS_URL", "redis://localhost:6379/0")
HEALTH_TOKEN = os.getenv("HEALTH_TOKEN", "SECRET_TOKEN_NODE")

ADMINS = [8564072723, 8676835917,]  # Add your Telegram User ID here
QUEUE_PAUSED = False
STARTUP_TIME = time.time()
ACTIVE_DOWNLOADS = 0
ACTIVE_DOWNLOAD_LOCK = asyncio.Lock()

# Global Client Storage Namespaces
SESSION = None
REDIS_CONN = None
DOWNLOAD_QUEUE = asyncio.Queue(maxsize=100)
DOWNLOAD_SEMAPHORE = asyncio.Semaphore(5)
WORKER_TASKS = []

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Chrome/123.0.0.0"
]

EXAMS = {
    "AIIMS": ["Delhi", "Bhopal", "Raipur", "Rishikesh", "Jodhpur", "Patna", "Bhubaneswar", "Nagpur", "Kalyani"],
    "ESIC": ["Central", "Region Wise"],
    "DSSSB": ["Delhi Subordinate"],
    "RUHS": ["Rajasthan Univ"],
    "NHM": ["UP", "MP", "Bihar", "Rajasthan", "Maharashtra"]
}
YEARS = [2026, 2025, 2024, 2023, 2022, 2021, 2020]
TRUSTED_DOMAINS = ["aiimsexams.ac.in", "esic.nic.in", "dsssb.delhi.gov.in", "ruhsraj.org", "nhm.gov.in"]

app = Client(
    "pharma_enterprise_unified",
    api_id=API_ID,
    api_hash=API_HASH,
    bot_token=BOT_TOKEN
)


# Optimized Mongo Pools Setup
db_client = AsyncIOMotorClient(MONGO_URI, maxPoolSize=50, minPoolSize=5, retryWrites=True)
db = db_client.get_database()
cache_collection = db["search_cache"]
search_map_collection = db["search_mappings"]
file_id_cache = db["telegram_file_cache"]

# ================= 3. SAFE PIPELINE EXCEPTION MIDDLEWARE WRAPPER =================
def safe_handler(func):
    @wraps(func)
    async def wrapper(*args, **kwargs):
        trace_id = uuid.uuid4().hex
        try:
            return await func(*args, **kwargs)
        except Exception as e:
            logger.error("Intercepted transactional crash inside handler runtime layer", error=str(e), trace_id=trace_id, exc_info=True)
            for arg in args:
                if isinstance(arg, Message):
                    await arg.reply_text(f"❌ Process error encountered. Trace ID: `{trace_id}`.")
                    break
                elif isinstance(arg, CallbackQuery):
                    await arg.answer(f"⚠️ Internal scheduler exception. Trace ID: {trace_id}.", show_alert=True)
                    break
    return wrapper

# Cryptographic and JSON Safe Storage Utilities
def generate_search_id(user_id: int, query: str) -> str:
    raw = f"{user_id}:{query}:{time.strftime('%Y%m%d%H')}"
    return hashlib.sha256(raw.encode()).hexdigest()[:24]

def compress_payload(data) -> bytes:
    return zlib.compress(json.dumps(data).encode('utf-8'))

def decompress_payload(compressed_bytes: bytes) -> list:
    return json.loads(zlib.decompress(compressed_bytes).decode('utf-8'))

# ================= 4. SECURITY NETWORK MITIGATION MIDDLEWARE (SSRF Shield) =================
def is_validated_url(url: str) -> bool:
    try:
        parsed = urlparse(url)
        if parsed.scheme not in ["http", "https"]: return False
        netloc = parsed.netloc.lower()
        if any(x in netloc for x in ["localhost", "127.0.0.1", "0.0.0.0", "169.254.169.254"]): return False
        if netloc.startswith("10.") or netloc.startswith("192.168.") or netloc.startswith("172."): return False
        return True
    except Exception:
        return False

# Redis Distributed Lock System Elements
async def acquire_lock(lock_name: str, lease_time: int = 15) -> bool:
    if not REDIS_CONN: return True
    return bool(await REDIS_CONN.set(f"lock:{lock_name}", "1", ex=lease_time, nx=True))

async def release_lock(lock_name: str):
    if REDIS_CONN: await REDIS_CONN.delete(f"lock:{lock_name}")

async def is_spammed_redis(user_id: int, prefix: str, seconds: int) -> bool:
    if not REDIS_CONN: return False
    key = f"cooldown:{prefix}:{user_id}"
    if await REDIS_CONN.get(key): return True
    await REDIS_CONN.setex(key, seconds, "1")
    return False

# Circuit Breaker Logic Pattern
async def is_circuit_available() -> bool:
    if not REDIS_CONN: return True
    return not bool(await REDIS_CONN.get("circuit:broken:scraper"))

async def trigger_circuit_failure():
    if not REDIS_CONN: return
    key = "circuit:fail_count:scraper"
    count = await REDIS_CONN.incr(key)
    await REDIS_CONN.expire(key, 60)
    if count >= 5:
        await REDIS_CONN.setex("circuit:broken:scraper", 300, "1")
        await REDIS_CONN.delete(key)

# ================= EXTRACTION PARSING ENGINES =================
async def ddg_scrape(query: str):
    try:
        search_query = query + " filetype:pdf"
        url = "https://html.duckduckgo.com/html/?q=" + search_query.replace(" ", "+")

        headers = {
            "User-Agent": random.choice(USER_AGENTS)
        }

        async with SESSION.get(url, headers=headers, timeout=20) as resp:
            html = await resp.text()

        soup = BeautifulSoup(html, "html.parser")

        results = []

        found = soup.find_all("a", class_="result__a")

        for a in found:
            href = a.get("href")

            if not href:
                continue

            if "uddg=" in href:
                import urllib.parse
                href = urllib.parse.unquote(href.split("uddg=")[1].split("&")[0])

            if href.startswith("http"):
                results.append({
                    "title": a.get_text(strip=True)[:120],
                    "url": href
                })

        print("SCRAPER RESULTS:", len(results))

        return results

    except Exception as e:
        print("SCRAPER ERROR:", e)
        return []

async def get_combined_results(query: str):

    cached = await cache_collection.find_one({"query": query.lower()})
    if cached: return decompress_payload(cached["compressed_payload"])

    d_res = await ddg_scrape(query)
    seen, unique = set(), []
    for item in d_res:
        if item["url"] not in seen:
            seen.add(item["url"])
            unique.append(item)
            
    final_set = unique[:20]
    if final_set:
        await cache_collection.update_one(
            {"query": query.lower()},
            {"$set": {"compressed_payload": compress_payload(final_set), "created_at": datetime.utcnow()}},
            upsert=True
        )
    return final_set

# ================= HIGH SCALE HIGH CONCURRENCY DOWNLOAD POOLS =================
async def download_worker(shutdown_event: asyncio.Event):
    global ACTIVE_DOWNLOADS
    while not shutdown_event.is_set():
        task_acquired = False
        user_id = None
        resp_obj = None
        clean_filename = None
        
        try:
            try:
                task = await asyncio.wait_for(DOWNLOAD_QUEUE.get(), timeout=2)
                task_acquired = True
            except asyncio.TimeoutError:
                continue

            client_ctx, chat_id, url, filename, callback_query, user_id = task
            if not is_validated_url(url): continue

            async with DOWNLOAD_SEMAPHORE:
                async with ACTIVE_DOWNLOAD_LOCK:
                    ACTIVE_DOWNLOADS += 1
                
                url_hash = hashlib.sha256(url.encode()).hexdigest()
                existing = await file_id_cache.find_one({"url_hash": url_hash})
                if existing:
                    await client_ctx.send_document(chat_id=chat_id, document=existing["file_id"], caption=f"📄 **CDN Distributed Object:** `{filename}`")
                    await callback_query.answer("Retrieved instantly from database storage systems!")
                    continue
                
                if not await acquire_lock(url_hash, lease_time=20): continue

                with tempfile.NamedTemporaryFile(delete=False, suffix=".pdf") as tmp:
                    clean_filename = tmp.name

                try:
                    async with SESSION.get(url, timeout=aiohttp.ClientTimeout(total=40)) as resp_obj:
                        content_length = resp_obj.headers.get("Content-Length")
                        if content_length and int(content_length) > 25 * 1024 * 1024: continue
                            
                        async with async_timeout.timeout(30):
                            file_signature_header = await resp_obj.content.read(5)
                            pass

                            async with aiofiles.open(clean_filename, "wb") as f:
                                await f.write(file_signature_header)
                                async for chunk in resp_obj.content.iter_chunked(2048):
                                    await f.write(chunk)
                                    
                    sent_doc = await client_ctx.send_document(chat_id=chat_id, document=clean_filename, caption=f"✅ **Verified Resource:** `{filename}`")
                    await file_id_cache.update_one({"url_hash": url_hash}, {"$set": {"file_id": sent_doc.document.file_id}}, upsert=True)
                finally:
                    await release_lock(url_hash)
                    if resp_obj: await resp_obj.release()
                    
        except Exception as e:
            logger.error("Exception handled within background downloader loops execution thread", error=str(e))
        finally:
            if task_acquired: DOWNLOAD_QUEUE.task_done()
            if user_id and REDIS_CONN: 
                await REDIS_CONN.incrby(f"queue_count:{user_id}", -1)
            async with ACTIVE_DOWNLOAD_LOCK:
                ACTIVE_DOWNLOADS = max(0, ACTIVE_DOWNLOADS - 1)
            if clean_filename and os.path.exists(clean_filename): os.remove(clean_filename)

# Dynamic Navigation Keyboard Interface Builder
def build_paginated_keyboard(search_id: str, results, page: int = 1):
    items_per_page = 5
    start_idx = (page - 1) * items_per_page
    end_idx = start_idx + items_per_page
    sliced_items = results[start_idx:end_idx]
    
    buttons = []
    for idx, item in enumerate(sliced_items):
        global_idx = start_idx + idx
        title_text = f"📄 [{global_idx+1}] " + (item["title"][:35] + "..." if len(item["title"]) > 35 else item["title"])
        buttons.append([InlineKeyboardButton(title_text, url=item["url"]), InlineKeyboardButton("📥 Get File", callback_data=f"dl_{search_id}_{global_idx}")])
        
    nav_row = []
    if page > 1: nav_row.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"pg_{search_id}_{page-1}"))
    if end_idx < len(results): nav_row.append(InlineKeyboardButton("Next ➡️", callback_data=f"pg_{search_id}_{page+1}"))
    if nav_row: buttons.append(nav_row)
    buttons.append([InlineKeyboardButton("🔙 Menu", callback_data="back_main")])
    return InlineKeyboardMarkup(buttons)

# ================= CORE INTERFACE TELEGRAM ROUTING DISPATCHERS =================

@app.on_message(filters.command("start"))
@safe_handler
async def start_handler(_, message: Message):
    if await is_spammed_redis(message.from_user.id, "cmd", 4):
        return await message.reply_text("⏳ **Anti-Flood Protocol Active.** Slowly enter queries parameters.")
        
    keyboard = [[InlineKeyboardButton(f"🏥 {exam} System Board", callback_data=f"exam_{exam}")] for exam in EXAMS.keys()]
    if message.from_user.id in ADMINS:
        keyboard.append([InlineKeyboardButton("⚙️ Admin Settings Center", callback_data="admin_dashboard")])
        
    await message.reply_text("⚡ **Enterprise Grade Automated Pharmacist PYQ Delivery Platform** ⚡", reply_markup=InlineKeyboardMarkup(keyboard))

@app.on_callback_query(filters.regex("^admin_"))
@safe_handler
async def admin_callback_handler(client, query: CallbackQuery):
    global QUEUE_PAUSED
    if query.from_user.id not in ADMINS: return
    mode = query.data.split("_")[1]
    
    if mode == "dashboard":
        keyboard = [[InlineKeyboardButton("⏸️ Pause Queue & Drain", callback_data="admin_pausequeue")], [InlineKeyboardButton("🔙 Main Menu", callback_data="back_main")]]
        async with ACTIVE_DOWNLOAD_LOCK: th = ACTIVE_DOWNLOADS
        await query.message.edit_text(
            f"🛠️ **Enterprise Systems Control Suite**\n\nActive Workers Size: `5` Clusters\nPending Items Queue Size: `{DOWNLOAD_QUEUE.qsize()}`\nActive Threads: `{th}` loops active.",
            reply_markup=InlineKeyboardMarkup(keyboard)
        )
    elif mode == "pausequeue":
        QUEUE_PAUSED = True
        await query.answer("🚨 Queue system PAUSED. Existing processes draining safely...", show_alert=True)

@app.on_callback_query(filters.regex("^exam_"))
@safe_handler
async def exam_callback(_, query: CallbackQuery):
    exam = query.data.split("_")[1]
    states = EXAMS.get(exam, [])
    keyboard = []
    
    if states:
        for state in states:
            keyboard.append([InlineKeyboardButton(f"📍 Region Context: {state}", callback_data=f"state_{exam}_{state}")])
    else:
        for year in YEARS:
            search_str = f"{exam} pharmacist exam paper {year}"
            s_id = generate_search_id(query.from_user.id, search_str)
            keyboard.append([InlineKeyboardButton(f"📅 Year Frame: {year}", callback_data=f"src_{s_id}_1")])
            await search_map_collection.update_one({"search_id": s_id}, {"$set": {"query": search_str, "ts": time.time()}}, upsert=True)
            
    keyboard.append([InlineKeyboardButton("🔙 Back", callback_data="back_main")])
    await query.message.edit_text(f"📂 **Directory Category:** `{exam}`\nSelect targeted examination parameters:", reply_markup=InlineKeyboardMarkup(keyboard))

@app.on_callback_query(filters.regex("^state_"))
@safe_handler
async def state_callback(_, query: CallbackQuery):
    _, exam, state = query.data.split("_")
    keyboard = []
    for year in YEARS:
        search_str = f"{exam} {state} pharmacist question paper {year}"
        s_id = generate_search_id(query.from_user.id, search_str)
        keyboard.append([InlineKeyboardButton(f"📅 Execution Target: {year}", callback_data=f"src_{s_id}_1")])
        await search_map_collection.update_one({"search_id": s_id}, {"$set": {"query": search_str, "ts": time.time()}}, upsert=True)
        
    keyboard.append([InlineKeyboardButton("🔙 Back", callback_data=f"exam_{exam}")])
    await query.message.edit_text(f"🏥 **Region Active Setup:** {exam} -> {state}\nSelect examination data years execution layer 👇", reply_markup=InlineKeyboardMarkup(keyboard))

@app.on_callback_query(filters.regex(r"^(src|pg)_"))
@safe_handler
async def search_and_pagination_engine(client, query: CallbackQuery):
    parts = query.data.split("_")
    search_id = parts[1]
    page = int(parts[2])
    
    map_doc = await search_map_collection.find_one({"search_id": search_id})
    if not map_doc: return await query.answer("❌ Session sequence expired inside memory arrays. Restart.", show_alert=True)
    
    search_query = map_doc["query"]
    await query.message.edit_text(f"🔍 **Cluster Synchronization Processing...**\nScanning database indexes elements targeting variables parameters:\n`{search_query}`")
    
    results = await get_combined_results(search_query)
    if not results:
        return await query.message.edit_text("❌ No verified documentation paths matching criteria configurations discovered inside tracking pools.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Main Menu", callback_data="back_main")]]))
        
    await query.message.edit_text(f"📄 **Dynamic Index Query Match:** `{search_query}`", reply_markup=build_paginated_keyboard(search_id, results, page), disable_web_page_preview=True)

@app.on_callback_query(filters.regex("^dl_"))
@safe_handler
async def download_trigger_callback(client, query: CallbackQuery):
    if QUEUE_PAUSED: return await query.answer("🚨 System Warning: Download paths locked down for systematic queue draining.", show_alert=True)
    parts = query.data.split("_")
    search_id = parts[1]
    idx = int(parts[2])
    user_id = query.from_user.id
    
    # Per user dynamic locks counter limit tracking inside Redis
    if REDIS_CONN:
        current_user_tasks = int(await REDIS_CONN.get(f"queue_count:{user_id}") or 0)
        if current_user_tasks >= 3:
            return await query.answer("⚠️ Limit Exception: You already have 3 concurrent downloading tasks running.", show_alert=True)
            
    cache_doc = await search_map_collection.find_one({"search_id": search_id})
    if not cache_doc: return await query.answer("⚠️ Core context tracking code decayed. Re-execute listings query.", show_alert=True)
    
    results = await get_combined_results(cache_doc["query"])
    if not results or idx >= len(results): return await query.answer("❌ Tracked document data elements lost.", show_alert=True)
    if DOWNLOAD_QUEUE.full(): return await query.answer("🚨 System core allocation buffers full. Wait for running items execution.", show_alert=True)
    
    if REDIS_CONN: 
        await REDIS_CONN.incr(f"queue_count:{user_id}")
    await query.answer("⏳ Pipeline slot reserved. Queue dispatch processing execution initializing...")
    await DOWNLOAD_QUEUE.put((client, query.message.chat.id, results[idx]["url"], results[idx]["title"], query, user_id))

@app.on_callback_query(filters.regex("^back_main$"))
@safe_handler
async def back_main_callback(_, query: CallbackQuery):
    keyboard = [[InlineKeyboardButton(f"🏥 {exam} System Board", callback_data=f"exam_{exam}")] for exam in EXAMS.keys()]
    if query.from_user.id in ADMINS:
        keyboard.append([InlineKeyboardButton("⚙️ Admin Settings Center", callback_data="admin_dashboard")])
    await query.message.edit_text("⚡ **Enterprise Grade Automated Pharmacist PYQ Delivery Platform** ⚡", reply_markup=InlineKeyboardMarkup(keyboard))

# ================= KUBERNETES AND SAAS HEALTH ENDPOINTS =================
async def live_probe_route(request): return web.json_response({"status": "LIVE", "uptime_sec": int(time.time() - STARTUP_TIME)})
async def ready_probe_route(request):
    try:
        await cache_collection.find_one()
        if QUEUE_PAUSED: return web.json_response({"status": "NOT_READY"}, status=503)
        return web.json_response({"status": "READY"})
    except Exception: return web.json_response({"status": "NOT_READY"}, status=503)

async def telemetry_dashboard_route(request):
    token = request.query.get("token")
    if token and token == HEALTH_TOKEN:
        async with ACTIVE_DOWNLOAD_LOCK: th = ACTIVE_DOWNLOADS
        return web.json_response({"status": "HEALTHY", "queue_depth": DOWNLOAD_QUEUE.qsize(), "active_threads": th})
    return web.json_response({"status": "OPERATIONAL", "version": "6.0.0-enterprise-unified"})


# ================= GLOBAL ORCHESTRATOR BOOT PIPELINE =================

@app.on_message(filters.command("find"))
@safe_handler
async def find_handler(client, message: Message):

    query_text = message.text.replace("/find", "").strip()

    if not query_text:
        return await message.reply_text(
            "Usage:\n/find AIIMS Delhi Pharmacist 2024"
        )

    await message.reply_text(
        f"🔍 Searching for:\n{query_text}"
    )

async def init_services():
    global SESSION, REDIS_CONN

    connector = aiohttp.TCPConnector(
        limit=100,
        ttl_dns_cache=300,
        keepalive_timeout=30,
        enable_cleanup_closed=True
    )

    SESSION = aiohttp.ClientSession(connector=connector)

    try:
        REDIS_CONN = await aioredis.from_url(
            REDIS_URL,
            decode_responses=True
        )
        await REDIS_CONN.ping()
        logger.info("Redis connected.")
    except Exception as e:
        logger.error(f"Redis failed: {e}")

    try:
        await db_client.admin.command("ping")
        logger.info("MongoDB connected.")
    except Exception as e:
        logger.error(f"MongoDB failed: {e}")

    await cache_collection.create_index([("query", 1)])
    await search_map_collection.create_index("search_id")
    await file_id_cache.create_index("url_hash")

    server = web.Application()
    server.router.add_get("/live", live_probe_route)
    server.router.add_get("/ready", ready_probe_route)
    server.router.add_get("/health", telemetry_dashboard_route)

    runner = web.AppRunner(server)
    await runner.setup()

    site = web.TCPSite(runner, "0.0.0.0", 8080)
    await site.start()

    logger.info("Health server started on :8080")

    for _ in range(5):
        WORKER_TASKS.append(
            asyncio.create_task(
                download_worker(asyncio.Event())
            )
        )

@app.on_message(filters.text)
async def debug_handler(client, message):
    print("MESSAGE RECEIVED:", message.text)

if __name__ == "__main__":

    loop = asyncio.get_event_loop()

    loop.run_until_complete(init_services())

    print("BOT STARTED SUCCESSFULLY")

    app.run()

