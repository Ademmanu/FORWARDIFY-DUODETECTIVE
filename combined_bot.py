#!/usr/bin/env python3
"""
Combined Forwarder + Duplicate Monitor Bot

This script merges the features of:
- FORWARDIFY (forward.py): forwarding messages from sources -> targets with flexible filters,
  send workers, rate limiting and flood-wait handling.
- DUODETECTIVE (monitor.py): duplicate detection in monitored chats, notification + manual/auto-reply,
  per-(user,chat) message history, notification workers, DB caching and robust init.

It provides a single bot that supports both sets of commands:
- Forwarding: /forwadd, /fortasks
- Monitoring: /monitoradd, /monitortasks
- Session management: /login, /logout, /getallid, /start, /ownersets
- Owner utilities for sessions and allowed users

Notes:
- This file is a careful merge of both original codebases' logic and structure.
- Database contains tables for users, forwarding_tasks, monitoring_tasks, and allowed_users.
- Both send workers (for forwarding) and notification workers (for duplicate alerts) are included.
"""

import os
import sys
import asyncio
import logging
import functools
import gc
import re
import time
import signal
import threading
import sqlite3
import json
import hashlib
import atexit
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Set, Callable, Any, DefaultDict
from collections import OrderedDict, defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache, partial
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlparse

from flask import Flask, request, jsonify

from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.errors import SessionPasswordNeededError, FloodWaitError

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, Bot
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    ContextTypes,
    MessageHandler,
    filters,
)
from telegram.helpers import escape_markdown

# Optional imports
try:
    import psycopg
    from psycopg.rows import dict_row
except Exception:
    psycopg = None

# Logging setup (both stdout and optional file)
LOG_FILE = os.getenv("LOG_FILE", "")
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        *( [logging.FileHandler(LOG_FILE, mode='a', encoding='utf-8')] if LOG_FILE else [] )
    ]
)
logger = logging.getLogger("combined_bot")

# Environment & configuration
BOT_TOKEN = os.getenv("BOT_TOKEN")
API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH", "")

DATABASE_TYPE = os.getenv("DATABASE_TYPE", "sqlite").lower()
DATABASE_URL = os.getenv("DATABASE_URL")
SQLITE_DB_PATH = os.getenv("SQLITE_DB_PATH", "bot_data.db")

if DATABASE_TYPE == "postgres" and not DATABASE_URL:
    logger.warning("DATABASE_TYPE is set to 'postgres' but DATABASE_URL is not set, falling back to sqlite")
    DATABASE_TYPE = "sqlite"

USER_SESSIONS = {}
user_sessions_env = os.getenv("USER_SESSIONS", "").strip()
if user_sessions_env:
    for session_entry in user_sessions_env.split(","):
        if not session_entry or ":" not in session_entry:
            continue
        try:
            user_id_str, session_string = session_entry.split(":", 1)
            user_id = int(user_id_str.strip())
            USER_SESSIONS[user_id] = session_string.strip()
        except ValueError:
            continue

OWNER_IDS: Set[int] = set()
owner_env = os.getenv("OWNER_IDS", "").strip()
if owner_env:
    OWNER_IDS.update(int(part) for part in owner_env.split(",") if part.strip().isdigit())

ALLOWED_USERS: Set[int] = set()
allowed_env = os.getenv("ALLOWED_USERS", "").strip()
if allowed_env:
    ALLOWED_USERS.update(int(part) for part in allowed_env.split(",") if part.strip().isdigit())

# Forwarder settings
SEND_WORKER_COUNT = int(os.getenv("SEND_WORKER_COUNT", "50"))
SEND_QUEUE_MAXSIZE = int(os.getenv("SEND_QUEUE_MAXSIZE", "10000"))
TARGET_RESOLVE_RETRY_SECONDS = int(os.getenv("TARGET_RESOLVE_RETRY_SECONDS", "3"))
MAX_CONCURRENT_USERS = max(50, int(os.getenv("MAX_CONCURRENT_USERS", "200")))
SEND_CONCURRENCY_PER_USER = int(os.getenv("SEND_CONCURRENCY_PER_USER", "30"))
SEND_RATE_PER_USER = float(os.getenv("SEND_RATE_PER_USER", "30.0"))
TARGET_ENTITY_CACHE_SIZE = int(os.getenv("TARGET_ENTITY_CACHE_SIZE", "100"))

# Monitor settings
MONITOR_WORKER_COUNT = int(os.getenv("MONITOR_WORKER_COUNT", "10"))
NOTIFY_QUEUE_MAXSIZE = int(os.getenv("NOTIFY_QUEUE_MAXSIZE", str(2000)))
DUPLICATE_CHECK_WINDOW = int(os.getenv("DUPLICATE_CHECK_WINDOW", "600"))
MESSAGE_HASH_LIMIT = int(os.getenv("MESSAGE_HASH_LIMIT", "2000"))

# Misc
WEB_SERVER_PORT = int(os.getenv("WEB_SERVER_PORT", "5000"))
GC_INTERVAL = int(os.getenv("GC_INTERVAL", "600"))
_DEFAULT_CONTAINER_MAX_RAM_MB = int(os.getenv("CONTAINER_MAX_RAM_MB", "512"))

# Patterns & helpers
EMOJI_PATTERN = re.compile(
    "["
    "\U0001F600-\U0001F64F"
    "\U0001F300-\U0001F5FF"
    "\U0001F680-\U0001F6FF"
    "\U0001F1E0-\U0001F1FF"
    "\U00002702-\U000027B0"
    "\U000024C2-\U0001F251"
    "]+", flags=re.UNICODE
)

WORD_PATTERN = re.compile(r'\S+')
NUMERIC_PATTERN = re.compile(r'^\d+$')
ALPHABETIC_PATTERN = re.compile(r'^[A-Za-z]+$')

UNAUTHORIZED_MESSAGE = """🚫 **Access Denied!** 

You are not authorized to use this bot.

📞 **Call this number:** `07089430305`

Or

🗨️ **Message Developer:** [HEMMY](https://t.me/justmemmy)
"""

# --- Database class (merged & enhanced) ---
class Database:
    """
    Combined Database supporting:
    - users (same schema)
    - forwarding_tasks (from forward.py)
    - monitoring_tasks (from monitor.py)
    - allowed_users
    Includes caching for performance similar to monitor.py.
    """

    def __init__(self, db_path: str = SQLITE_DB_PATH):
        self.db_type = DATABASE_TYPE
        self.db_path = db_path
        self.postgres_url = DATABASE_URL

        self._conn_init_lock = threading.Lock()
        self._thread_local = threading.local()

        # caches
        self._user_cache: Dict[int, Dict] = {}
        self._forward_tasks_cache: Dict[int, List[Dict]] = defaultdict(list)
        self._monitor_tasks_cache: Dict[int, List[Dict]] = defaultdict(list)
        self._allowed_users_cache: Set[int] = set()
        self._admin_cache: Set[int] = set()

        try:
            self.init_db()
            self._load_caches()
            logger.info(f"Database initialized with type: {self.db_type}")
        except Exception as e:
            logger.exception("Failed initializing DB: %s", e)
            # Attempt recreate if sqlite file corrupted
            if self.db_type == "sqlite":
                try:
                    if os.path.exists(self.db_path):
                        os.remove(self.db_path)
                        logger.info("Removed corrupted database file, retrying init")
                    self.init_db()
                    self._load_caches()
                except Exception as e2:
                    logger.exception("Recreate DB failed: %s", e2)
                    raise
            else:
                raise

        atexit.register(self.close_connection)

    def _create_sqlite_connection(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.db_path, timeout=30, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        self._apply_sqlite_pragmas(conn)
        return conn

    def _create_postgres_connection(self):
        if not psycopg:
            raise RuntimeError("psycopg not available for postgres connections")
        if not self.postgres_url:
            raise ValueError("DATABASE_URL not set for PostgreSQL")

        parsed = urlparse(self.postgres_url)
        dbname = parsed.path[1:]
        user = parsed.username
        password = parsed.password
        host = parsed.hostname
        port = parsed.port or 5432

        conn_str = f"postgresql://{user}:{password}@{host}:{port}/{dbname}"
        if parsed.query:
            params = dict(pair.split('=') for pair in parsed.query.split('&') if '=' in pair)
            sslmode = params.get('sslmode', 'require')
            conn_str += f"?sslmode={sslmode}"

        conn = psycopg.connect(conn_str, autocommit=False, row_factory=dict_row)
        return conn

    def _apply_sqlite_pragmas(self, conn: sqlite3.Connection):
        try:
            conn.execute("PRAGMA journal_mode=WAL;")
            conn.execute("PRAGMA synchronous=NORMAL;")
            conn.execute("PRAGMA temp_store=MEMORY;")
            conn.execute("PRAGMA cache_size=-1000;")
            conn.execute("PRAGMA mmap_size=268435456;")
        except Exception:
            pass

    def get_connection(self):
        conn = getattr(self._thread_local, "conn", None)
        if conn:
            try:
                if self.db_type == "sqlite":
                    conn.execute("SELECT 1")
                else:
                    with conn.cursor() as cur:
                        cur.execute("SELECT 1")
                return conn
            except Exception:
                try:
                    conn.close()
                except Exception:
                    pass
                self._thread_local.conn = None

        try:
            if self.db_type == "sqlite":
                self._thread_local.conn = self._create_sqlite_connection()
            else:
                self._thread_local.conn = self._create_postgres_connection()
            return self._thread_local.conn
        except Exception as e:
            logger.exception("Failed to create DB connection: %s", e)
            raise

    def close_connection(self):
        conn = getattr(self._thread_local, "conn", None)
        if conn:
            try:
                conn.close()
            except Exception:
                logger.exception("Failed to close DB connection")
            self._thread_local.conn = None

    def init_db(self):
        with self._conn_init_lock:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        user_id INTEGER PRIMARY KEY,
                        phone TEXT,
                        name TEXT,
                        session_data TEXT,
                        is_logged_in INTEGER DEFAULT 0,
                        created_at TEXT DEFAULT (datetime('now')),
                        updated_at TEXT DEFAULT (datetime('now'))
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS forwarding_tasks (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        user_id INTEGER,
                        label TEXT,
                        source_ids TEXT,
                        target_ids TEXT,
                        filters TEXT,
                        is_active INTEGER DEFAULT 1,
                        created_at TEXT DEFAULT (datetime('now')),
                        updated_at TEXT DEFAULT (datetime('now')),
                        FOREIGN KEY (user_id) REFERENCES users (user_id),
                        UNIQUE(user_id, label)
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS monitoring_tasks (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        user_id INTEGER,
                        label TEXT,
                        chat_ids TEXT,
                        settings TEXT,
                        is_active INTEGER DEFAULT 1,
                        created_at TEXT DEFAULT (datetime('now')),
                        updated_at TEXT DEFAULT (datetime('now')),
                        FOREIGN KEY (user_id) REFERENCES users (user_id),
                        UNIQUE(user_id, label)
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS allowed_users (
                        user_id INTEGER PRIMARY KEY,
                        username TEXT,
                        is_admin INTEGER DEFAULT 0,
                        added_by INTEGER,
                        created_at TEXT DEFAULT (datetime('now'))
                    )
                """)
                # Useful indices
                cur.execute("CREATE INDEX IF NOT EXISTS idx_users_logged_in ON users(is_logged_in)")
                cur.execute("CREATE INDEX IF NOT EXISTS idx_forward_tasks_user_active ON forwarding_tasks(user_id, is_active)")
                cur.execute("CREATE INDEX IF NOT EXISTS idx_monitor_tasks_user_active ON monitoring_tasks(user_id, is_active)")
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS users (
                            user_id BIGINT PRIMARY KEY,
                            phone VARCHAR(255),
                            name TEXT,
                            session_data TEXT,
                            is_logged_in BOOLEAN DEFAULT FALSE,
                            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                        )
                    """)
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS forwarding_tasks (
                            id SERIAL PRIMARY KEY,
                            user_id BIGINT,
                            label VARCHAR(255),
                            source_ids JSONB,
                            target_ids JSONB,
                            filters JSONB,
                            is_active BOOLEAN DEFAULT TRUE,
                            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            FOREIGN KEY (user_id) REFERENCES users (user_id),
                            UNIQUE(user_id, label)
                        )
                    """)
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS monitoring_tasks (
                            id SERIAL PRIMARY KEY,
                            user_id BIGINT,
                            label VARCHAR(255),
                            chat_ids JSONB,
                            settings JSONB,
                            is_active BOOLEAN DEFAULT TRUE,
                            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                            FOREIGN KEY (user_id) REFERENCES users (user_id),
                            UNIQUE(user_id, label)
                        )
                    """)
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS allowed_users (
                            user_id BIGINT PRIMARY KEY,
                            username VARCHAR(255),
                            is_admin BOOLEAN DEFAULT FALSE,
                            added_by BIGINT,
                            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                        )
                    """)
                conn.commit()

    def _load_caches(self):
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, is_admin FROM allowed_users")
                for row in cur.fetchall():
                    uid = row["user_id"]
                    self._allowed_users_cache.add(uid)
                    if row["is_admin"]:
                        self._admin_cache.add(uid)
                cur.execute("SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at FROM users WHERE is_logged_in = 1")
                for row in cur.fetchall():
                    uid = row["user_id"]
                    self._user_cache[uid] = {
                        'user_id': uid,
                        'phone': row["phone"],
                        'name': row["name"],
                        'session_data': row["session_data"],
                        'is_logged_in': bool(row["is_logged_in"]),
                        'created_at': row["created_at"],
                        'updated_at': row["updated_at"],
                    }
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, is_admin FROM allowed_users")
                    for row in cur.fetchall():
                        uid = row["user_id"]
                        self._allowed_users_cache.add(uid)
                        if row["is_admin"]:
                            self._admin_cache.add(uid)
                    cur.execute("SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at FROM users WHERE is_logged_in = TRUE")
                    for row in cur.fetchall():
                        uid = row["user_id"]
                        self._user_cache[uid] = {
                            'user_id': uid,
                            'phone': row["phone"],
                            'name': row["name"],
                            'session_data': row["session_data"],
                            'is_logged_in': row["is_logged_in"],
                            'created_at': row["created_at"].isoformat() if row["created_at"] else None,
                            'updated_at': row["updated_at"].isoformat() if row["updated_at"] else None,
                        }
            logger.info(f"Loaded caches: {len(self._allowed_users_cache)} allowed users, {len(self._user_cache)} logged-in users")
        except Exception as e:
            logger.exception("Error loading DB caches: %s", e)

    # --- User methods ---
    def get_user(self, user_id: int) -> Optional[Dict]:
        if user_id in self._user_cache:
            return self._user_cache[user_id].copy()
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at FROM users WHERE user_id = ?", (user_id,))
                row = cur.fetchone()
                if not row:
                    return None
                data = {
                    'user_id': row["user_id"],
                    'phone': row["phone"],
                    'name': row["name"],
                    'session_data': row["session_data"],
                    'is_logged_in': bool(row["is_logged_in"]),
                    'created_at': row["created_at"],
                    'updated_at': row["updated_at"]
                }
                self._user_cache[user_id] = data.copy()
                return data
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at FROM users WHERE user_id = %s", (user_id,))
                    row = cur.fetchone()
                    if not row:
                        return None
                    data = {
                        'user_id': row["user_id"],
                        'phone': row["phone"],
                        'name': row["name"],
                        'session_data': row["session_data"],
                        'is_logged_in': row["is_logged_in"],
                        'created_at': row["created_at"].isoformat() if row["created_at"] else None,
                        'updated_at': row["updated_at"].isoformat() if row["updated_at"] else None
                    }
                    self._user_cache[user_id] = data.copy()
                    return data
        except Exception as e:
            logger.exception("Error in get_user for %s: %s", user_id, e)
            return None

    def save_user(self, user_id: int, phone: Optional[str] = None, name: Optional[str] = None,
                  session_data: Optional[str] = None, is_logged_in: bool = False):
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT 1 FROM users WHERE user_id = ?", (user_id,))
                exists = cur.fetchone() is not None
                if exists:
                    updates = []
                    params = []
                    if phone is not None:
                        updates.append("phone = ?"); params.append(phone)
                    if name is not None:
                        updates.append("name = ?"); params.append(name)
                    if session_data is not None:
                        updates.append("session_data = ?"); params.append(session_data)
                    updates.append("is_logged_in = ?"); params.append(1 if is_logged_in else 0)
                    updates.append("updated_at = datetime('now')")
                    params.append(user_id)
                    query = f"UPDATE users SET {', '.join(updates)} WHERE user_id = ?"
                    cur.execute(query, params)
                else:
                    cur.execute("INSERT INTO users (user_id, phone, name, session_data, is_logged_in) VALUES (?, ?, ?, ?, ?)",
                                (user_id, phone, name, session_data, 1 if is_logged_in else 0))
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT 1 FROM users WHERE user_id = %s", (user_id,))
                    exists = cur.fetchone() is not None
                    if exists:
                        updates = []
                        params = []
                        if phone is not None:
                            updates.append("phone = %s"); params.append(phone)
                        if name is not None:
                            updates.append("name = %s"); params.append(name)
                        if session_data is not None:
                            updates.append("session_data = %s"); params.append(session_data)
                        updates.append("is_logged_in = %s"); params.append(is_logged_in)
                        updates.append("updated_at = CURRENT_TIMESTAMP")
                        params.append(user_id)
                        query = f"UPDATE users SET {', '.join(updates)} WHERE user_id = %s"
                        cur.execute(query, params)
                    else:
                        cur.execute("""
                            INSERT INTO users (user_id, phone, name, session_data, is_logged_in)
                            VALUES (%s, %s, %s, %s, %s)
                            ON CONFLICT (user_id) DO UPDATE SET
                                phone = EXCLUDED.phone,
                                name = EXCLUDED.name,
                                session_data = EXCLUDED.session_data,
                                is_logged_in = EXCLUDED.is_logged_in,
                                updated_at = CURRENT_TIMESTAMP
                        """, (user_id, phone, name, session_data, is_logged_in))
                conn.commit()

            # update cache
            if user_id in self._user_cache:
                ud = self._user_cache[user_id]
                if phone is not None: ud['phone'] = phone
                if name is not None: ud['name'] = name
                if session_data is not None: ud['session_data'] = session_data
                ud['is_logged_in'] = is_logged_in
                ud['updated_at'] = datetime.now().isoformat()
            else:
                if is_logged_in:
                    self._user_cache[user_id] = {
                        'user_id': user_id, 'phone': phone, 'name': name, 'session_data': session_data,
                        'is_logged_in': is_logged_in, 'updated_at': datetime.now().isoformat()
                    }
        except Exception as e:
            logger.exception("Error in save_user for %s: %s", user_id, e)
            raise

    def get_logged_in_users(self, limit: Optional[int] = None) -> List[Dict]:
        try:
            conn = self.get_connection()
            rows = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                if limit and int(limit) > 0:
                    cur.execute("SELECT user_id, session_data FROM users WHERE is_logged_in = 1 ORDER BY updated_at DESC LIMIT ?",
                                (int(limit),))
                else:
                    cur.execute("SELECT user_id, session_data FROM users WHERE is_logged_in = 1 ORDER BY updated_at DESC")
                rows = cur.fetchall()
                result = []
                for r in rows:
                    try:
                        uid = r["user_id"]; sess = r["session_data"]
                    except Exception:
                        uid, sess = r[0], r[1]
                    result.append({"user_id": uid, "session_data": sess})
                return result
            else:
                with conn.cursor() as cur:
                    if limit and int(limit) > 0:
                        cur.execute("SELECT user_id, session_data FROM users WHERE is_logged_in = TRUE ORDER BY updated_at DESC LIMIT %s",
                                    (int(limit),))
                    else:
                        cur.execute("SELECT user_id, session_data FROM users WHERE is_logged_in = TRUE ORDER BY updated_at DESC")
                    rows = cur.fetchall()
                    return [{"user_id": r["user_id"], "session_data": r["session_data"]} for r in rows]
        except Exception as e:
            logger.exception("Error fetching logged-in users: %s", e)
            return []

    # --- Allowed users (owner/admin) ---
    def is_user_allowed(self, user_id: int) -> bool:
        if user_id in self._allowed_users_cache:
            return True
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT 1 FROM allowed_users WHERE user_id = ?", (user_id,))
                exists = cur.fetchone() is not None
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT 1 FROM allowed_users WHERE user_id = %s", (user_id,))
                    exists = cur.fetchone() is not None
            if exists:
                self._allowed_users_cache.add(user_id)
            return exists
        except Exception:
            logger.exception("Error checking is_user_allowed for %s", user_id)
            return False

    def is_user_admin(self, user_id: int) -> bool:
        if user_id in self._admin_cache:
            return True
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT is_admin FROM allowed_users WHERE user_id = ?", (user_id,))
                row = cur.fetchone()
                if row and row["is_admin"]:
                    self._admin_cache.add(user_id)
                    self._allowed_users_cache.add(user_id)
                    return True
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT is_admin FROM allowed_users WHERE user_id = %s", (user_id,))
                    row = cur.fetchone()
                    if row and row["is_admin"]:
                        self._admin_cache.add(user_id)
                        self._allowed_users_cache.add(user_id)
                        return True
            return False
        except Exception:
            logger.exception("Error checking is_user_admin for %s", user_id)
            return False

    def add_allowed_user(self, user_id: int, username: Optional[str] = None,
                         is_admin: bool = False, added_by: Optional[int] = None) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                try:
                    cur.execute("INSERT INTO allowed_users (user_id, username, is_admin, added_by) VALUES (?, ?, ?, ?)",
                                (user_id, username, 1 if is_admin else 0, added_by))
                    conn.commit()
                    self._allowed_users_cache.add(user_id)
                    if is_admin: self._admin_cache.add(user_id)
                    return True
                except sqlite3.IntegrityError:
                    return False
            else:
                with conn.cursor() as cur:
                    try:
                        cur.execute("INSERT INTO allowed_users (user_id, username, is_admin, added_by) VALUES (%s, %s, %s, %s) ON CONFLICT (user_id) DO NOTHING RETURNING user_id",
                                    (user_id, username, is_admin, added_by))
                        row = cur.fetchone()
                        conn.commit()
                        if row:
                            self._allowed_users_cache.add(user_id)
                            if is_admin: self._admin_cache.add(user_id)
                            return True
                        return False
                    except Exception:
                        return False
        except Exception as e:
            logger.exception("Error in add_allowed_user for %s: %s", user_id, e)
            return False

    def remove_allowed_user(self, user_id: int) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("DELETE FROM allowed_users WHERE user_id = ?", (user_id,))
                deleted = cur.rowcount > 0
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("DELETE FROM allowed_users WHERE user_id = %s", (user_id,))
                    deleted = cur.rowcount > 0
                    conn.commit()
            if deleted:
                self._allowed_users_cache.discard(user_id)
                self._admin_cache.discard(user_id)
                self._user_cache.pop(user_id, None)
                self._forward_tasks_cache.pop(user_id, None)
                self._monitor_tasks_cache.pop(user_id, None)
            return deleted
        except Exception as e:
            logger.exception("Error in remove_allowed_user for %s: %s", user_id, e)
            return False

    def get_all_allowed_users(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            users = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, username, is_admin, added_by, created_at FROM allowed_users ORDER BY created_at DESC")
                for row in cur.fetchall():
                    users.append({
                        'user_id': row["user_id"], 'username': row["username"],
                        'is_admin': bool(row["is_admin"]), 'added_by': row["added_by"], 'created_at': row["created_at"]
                    })
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, username, is_admin, added_by, created_at FROM allowed_users ORDER BY created_at DESC")
                    for row in cur.fetchall():
                        users.append({
                            'user_id': row["user_id"], 'username': row["username"],
                            'is_admin': row["is_admin"], 'added_by': row["added_by"],
                            'created_at': row["created_at"].isoformat() if row["created_at"] else None
                        })
            return users
        except Exception as e:
            logger.exception("Error in get_all_allowed_users: %s", e)
            return []

    # --- Forwarding task methods (from forward.py) ---
    def add_forwarding_task(self, user_id: int, label: str, source_ids: List[int], target_ids: List[int], filters: Optional[Dict[str, Any]] = None) -> bool:
        try:
            if filters is None:
                filters = {
                    "filters": {
                        "raw_text": False,
                        "numbers_only": False,
                        "alphabets_only": False,
                        "removed_alphabetic": False,
                        "removed_numeric": False,
                        "prefix": "",
                        "suffix": ""
                    },
                    "outgoing": True,
                    "forward_tag": False,
                    "control": True
                }
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                try:
                    cur.execute("INSERT INTO forwarding_tasks (user_id, label, source_ids, target_ids, filters) VALUES (?, ?, ?, ?, ?)",
                                (user_id, label, json.dumps(source_ids), json.dumps(target_ids), json.dumps(filters)))
                    task_id = cur.lastrowid
                    conn.commit()
                    task = {
                        "id": task_id, "label": label, "source_ids": source_ids, "target_ids": target_ids,
                        "filters": filters, "is_active": 1
                    }
                    self._forward_tasks_cache[user_id].append(task)
                    return True
                except sqlite3.IntegrityError:
                    return False
            else:
                with conn.cursor() as cur:
                    try:
                        cur.execute("INSERT INTO forwarding_tasks (user_id, label, source_ids, target_ids, filters) VALUES (%s, %s, %s, %s, %s) ON CONFLICT (user_id, label) DO NOTHING RETURNING id",
                                    (user_id, label, json.dumps(source_ids), json.dumps(target_ids), json.dumps(filters)))
                        row = cur.fetchone()
                        conn.commit()
                        if row:
                            task_id = row["id"]
                            task = {
                                "id": task_id, "label": label, "source_ids": source_ids, "target_ids": target_ids,
                                "filters": filters, "is_active": 1
                            }
                            self._forward_tasks_cache[user_id].append(task)
                            return True
                        return False
                    except Exception:
                        return False
        except Exception as e:
            logger.exception("Error in add_forwarding_task for %s: %s", user_id, e)
            return False

    def update_forwarding_task_filters(self, user_id: int, label: str, filters: Dict[str, Any]) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("UPDATE forwarding_tasks SET filters = ?, updated_at = datetime('now') WHERE user_id = ? AND label = ?",
                            (json.dumps(filters), user_id, label))
                updated = cur.rowcount > 0
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("UPDATE forwarding_tasks SET filters = %s, updated_at = CURRENT_TIMESTAMP WHERE user_id = %s AND label = %s",
                                (json.dumps(filters), user_id, label))
                    updated = cur.rowcount > 0
                    conn.commit()
            if updated and user_id in self._forward_tasks_cache:
                for task in self._forward_tasks_cache[user_id]:
                    if task["label"] == label:
                        task["filters"] = filters
                        break
            return updated
        except Exception as e:
            logger.exception("Error in update_forwarding_task_filters for %s, task %s: %s", user_id, label, e)
            return False

    def remove_forwarding_task(self, user_id: int, label: str) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("DELETE FROM forwarding_tasks WHERE user_id = ? AND label = ?", (user_id, label))
                deleted = cur.rowcount > 0
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("DELETE FROM forwarding_tasks WHERE user_id = %s AND label = %s", (user_id, label))
                    deleted = cur.rowcount > 0
                    conn.commit()
            if deleted:
                if user_id in self._forward_tasks_cache:
                    self._forward_tasks_cache[user_id] = [t for t in self._forward_tasks_cache[user_id] if t.get("label") != label]
            return deleted
        except Exception as e:
            logger.exception("Error in remove_forwarding_task for %s: %s", user_id, e)
            return False

    def get_user_forwarding_tasks(self, user_id: int) -> List[Dict]:
        if self._forward_tasks_cache.get(user_id):
            return [t.copy() for t in self._forward_tasks_cache[user_id]]
        try:
            conn = self.get_connection()
            tasks = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT id, label, source_ids, target_ids, filters, is_active, created_at FROM forwarding_tasks WHERE user_id = ? AND is_active = 1 ORDER BY created_at DESC", (user_id,))
                for row in cur.fetchall():
                    try:
                        filters_data = json.loads(row["filters"]) if row["filters"] else {}
                    except Exception:
                        filters_data = {}
                    tasks.append({
                        "id": row["id"], "label": row["label"],
                        "source_ids": json.loads(row["source_ids"]) if row["source_ids"] else [],
                        "target_ids": json.loads(row["target_ids"]) if row["target_ids"] else [],
                        "filters": filters_data, "is_active": row["is_active"], "created_at": row["created_at"]
                    })
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT id, label, source_ids, target_ids, filters, is_active, created_at FROM forwarding_tasks WHERE user_id = %s AND is_active = TRUE ORDER BY created_at DESC", (user_id,))
                    for row in cur.fetchall():
                        tasks.append({
                            "id": row["id"], "label": row["label"], "source_ids": row["source_ids"] if row["source_ids"] else [],
                            "target_ids": row["target_ids"] if row["target_ids"] else [], "filters": row["filters"] if row["filters"] else {},
                            "is_active": row["is_active"], "created_at": row["created_at"].isoformat() if row["created_at"] else None
                        })
            if tasks:
                self._forward_tasks_cache[user_id] = tasks
            return [t.copy() for t in tasks]
        except Exception as e:
            logger.exception("Error in get_user_forwarding_tasks for %s: %s", user_id, e)
            return []

    def get_all_active_forwarding_tasks(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            tasks = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, id, label, source_ids, target_ids, filters FROM forwarding_tasks WHERE is_active = 1")
                for row in cur.fetchall():
                    try:
                        filters_data = json.loads(row["filters"]) if row["filters"] else {}
                    except Exception:
                        filters_data = {}
                    t = {
                        "user_id": row["user_id"], "id": row["id"], "label": row["label"],
                        "source_ids": json.loads(row["source_ids"]) if row["source_ids"] else [],
                        "target_ids": json.loads(row["target_ids"]) if row["target_ids"] else [],
                        "filters": filters_data
                    }
                    tasks.append(t)
                    if t["user_id"] not in self._forward_tasks_cache or not any(tt["id"] == t["id"] for tt in self._forward_tasks_cache.get(t["user_id"], [])):
                        self._forward_tasks_cache[t["user_id"]].append({**t, "is_active": 1})
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, id, label, source_ids, target_ids, filters FROM forwarding_tasks WHERE is_active = TRUE")
                    for row in cur.fetchall():
                        t = {
                            "user_id": row["user_id"], "id": row["id"], "label": row["label"],
                            "source_ids": row["source_ids"] if row["source_ids"] else [],
                            "target_ids": row["target_ids"] if row["target_ids"] else [],
                            "filters": row["filters"] if row["filters"] else {}
                        }
                        tasks.append(t)
                        if t["user_id"] not in self._forward_tasks_cache or not any(tt["id"] == t["id"] for tt in self._forward_tasks_cache.get(t["user_id"], [])):
                            self._forward_tasks_cache[t["user_id"]].append({**t, "is_active": 1})
            return tasks
        except Exception as e:
            logger.exception("Error in get_all_active_forwarding_tasks: %s", e)
            return []

    # --- Monitoring task methods (from monitor.py) ---
    def add_monitoring_task(self, user_id: int, label: str, chat_ids: List[int], settings: Optional[Dict[str, Any]] = None) -> bool:
        try:
            if settings is None:
                settings = {
                    "check_duplicate_and_notify": True,
                    "manual_reply_system": True,
                    "auto_reply_system": False,
                    "auto_reply_message": "",
                    "outgoing_message_monitoring": True
                }
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                try:
                    cur.execute("INSERT INTO monitoring_tasks (user_id, label, chat_ids, settings) VALUES (?, ?, ?, ?)",
                                (user_id, label, json.dumps(chat_ids), json.dumps(settings)))
                    task_id = cur.lastrowid
                    conn.commit()
                    task = {'id': task_id, 'label': label, 'chat_ids': chat_ids, 'settings': settings, 'is_active': 1}
                    self._monitor_tasks_cache[user_id].append(task)
                    return True
                except sqlite3.IntegrityError:
                    return False
            else:
                with conn.cursor() as cur:
                    try:
                        cur.execute("INSERT INTO monitoring_tasks (user_id, label, chat_ids, settings) VALUES (%s, %s, %s, %s) ON CONFLICT (user_id, label) DO NOTHING RETURNING id",
                                    (user_id, label, json.dumps(chat_ids), json.dumps(settings)))
                        row = cur.fetchone()
                        conn.commit()
                        if row:
                            task_id = row["id"]
                            task = {'id': task_id, 'label': label, 'chat_ids': chat_ids, 'settings': settings, 'is_active': 1}
                            self._monitor_tasks_cache[user_id].append(task)
                            return True
                        return False
                    except Exception:
                        return False
        except Exception as e:
            logger.exception("Error in add_monitoring_task for %s: %s", user_id, e)
            return False

    def update_monitor_task_settings(self, user_id: int, label: str, settings: Dict[str, Any]) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("UPDATE monitoring_tasks SET settings = ?, updated_at = datetime('now') WHERE user_id = ? AND label = ?",
                            (json.dumps(settings), user_id, label))
                updated = cur.rowcount > 0
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("UPDATE monitoring_tasks SET settings = %s, updated_at = CURRENT_TIMESTAMP WHERE user_id = %s AND label = %s",
                                (json.dumps(settings), user_id, label))
                    updated = cur.rowcount > 0
                    conn.commit()
            if updated and user_id in self._monitor_tasks_cache:
                for task in self._monitor_tasks_cache[user_id]:
                    if task['label'] == label:
                        task['settings'] = settings
                        break
            return updated
        except Exception as e:
            logger.exception("Error in update_monitor_task_settings for %s, task %s: %s", user_id, label, e)
            return False

    def remove_monitoring_task(self, user_id: int, label: str) -> bool:
        try:
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("DELETE FROM monitoring_tasks WHERE user_id = ? AND label = ?", (user_id, label))
                deleted = cur.rowcount > 0
                conn.commit()
            else:
                with conn.cursor() as cur:
                    cur.execute("DELETE FROM monitoring_tasks WHERE user_id = %s AND label = %s", (user_id, label))
                    deleted = cur.rowcount > 0
                    conn.commit()
            if deleted and user_id in self._monitor_tasks_cache:
                self._monitor_tasks_cache[user_id] = [t for t in self._monitor_tasks_cache[user_id] if t.get('label') != label]
            return deleted
        except Exception as e:
            logger.exception("Error in remove_monitoring_task for %s: %s", user_id, e)
            return False

    def get_user_monitoring_tasks(self, user_id: int) -> List[Dict]:
        if self._monitor_tasks_cache.get(user_id):
            return [t.copy() for t in self._monitor_tasks_cache[user_id]]
        try:
            conn = self.get_connection()
            tasks = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT id, label, chat_ids, settings, is_active FROM monitoring_tasks WHERE user_id = ? AND is_active = 1 ORDER BY created_at ASC", (user_id,))
                for row in cur.fetchall():
                    tasks.append({
                        'id': row["id"], 'label': row["label"],
                        'chat_ids': json.loads(row["chat_ids"]) if row["chat_ids"] else [],
                        'settings': json.loads(row["settings"]) if row["settings"] else {},
                        'is_active': row["is_active"]
                    })
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT id, label, chat_ids, settings, is_active FROM monitoring_tasks WHERE user_id = %s AND is_active = TRUE ORDER BY created_at ASC", (user_id,))
                    for row in cur.fetchall():
                        tasks.append({
                            'id': row["id"], 'label': row["label"],
                            'chat_ids': row["chat_ids"] if row["chat_ids"] else [],
                            'settings': row["settings"] if row["settings"] else {},
                            'is_active': row["is_active"]
                        })
            if tasks:
                self._monitor_tasks_cache[user_id] = tasks
            return [t.copy() for t in tasks]
        except Exception as e:
            logger.exception("Error in get_user_monitoring_tasks for %s: %s", user_id, e)
            return []

    def get_all_active_monitoring_tasks(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            tasks = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, id, label, chat_ids, settings FROM monitoring_tasks WHERE is_active = 1")
                for row in cur.fetchall():
                    uid = row["user_id"]
                    task = {
                        'user_id': uid, 'id': row["id"], 'label': row["label'],
                        'chat_ids': json.loads(row["chat_ids"]) if row["chat_ids"] else [],
                        'settings': json.loads(row["settings"]) if row["settings"] else {}
                    }
                    tasks.append(task)
                    if uid not in self._monitor_tasks_cache or not any(t['id'] == task['id'] for t in self._monitor_tasks_cache.get(uid, [])):
                        self._monitor_tasks_cache[uid].append({**task, 'is_active': 1})
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, id, label, chat_ids, settings FROM monitoring_tasks WHERE is_active = TRUE")
                    for row in cur.fetchall():
                        uid = row["user_id"]
                        task = {
                            'user_id': uid, 'id': row["id"], 'label': row["label"],
                            'chat_ids': row["chat_ids"] if row["chat_ids"] else [],
                            'settings': row["settings"] if row["settings"] else {}
                        }
                        tasks.append(task)
                        if uid not in self._monitor_tasks_cache or not any(t['id'] == task['id'] for t in self._monitor_tasks_cache.get(uid, [])):
                            self._monitor_tasks_cache[uid].append({**task, 'is_active': 1})
            return tasks
        except Exception as e:
            logger.exception("Error in get_all_active_monitoring_tasks: %s", e)
            return []

    def get_all_string_sessions(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            sessions = []
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT user_id, session_data, name, phone, is_logged_in FROM users WHERE session_data IS NOT NULL AND session_data != '' ORDER BY user_id")
                for row in cur.fetchall():
                    sessions.append({"user_id": row["user_id"], "session_data": row["session_data"], "name": row["name"], "phone": row["phone"], "is_logged_in": bool(row["is_logged_in"])})
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id, session_data, name, phone, is_logged_in FROM users WHERE session_data IS NOT NULL AND session_data != '' ORDER BY user_id")
                    for row in cur.fetchall():
                        sessions.append({"user_id": row["user_id"], "session_data": row["session_data"], "name": row["name"], "phone": row["phone"], "is_logged_in": row["is_logged_in"]})
            return sessions
        except Exception as e:
            logger.exception("Error in get_all_string_sessions: %s", e)
            raise

    def get_db_status(self) -> Dict:
        status = {
            "type": self.db_type,
            "path": self.db_path if self.db_type == "sqlite" else self.postgres_url,
            "exists": False,
            "size_bytes": None,
            "cache_counts": {
                "users": len(self._user_cache),
                "forwarding_tasks": sum(len(v) for v in self._forward_tasks_cache.values()),
                "monitoring_tasks": sum(len(v) for v in self._monitor_tasks_cache.values()),
                "allowed_users": len(self._allowed_users_cache),
                "admins": len(self._admin_cache)
            }
        }
        try:
            if self.db_type == "sqlite":
                status["exists"] = os.path.exists(self.db_path)
                if status["exists"]:
                    status["size_bytes"] = os.path.getsize(self.db_path)
            else:
                status["exists"] = True
            conn = self.get_connection()
            if self.db_type == "sqlite":
                cur = conn.cursor()
                cur.execute("SELECT name FROM sqlite_master WHERE type='table'")
                status["tables"] = [row[0] for row in cur.fetchall()]
            else:
                with conn.cursor() as cur:
                    cur.execute("SELECT table_name FROM information_schema.tables WHERE table_schema = 'public'")
                    status["tables"] = [row["table_name"] for row in cur.fetchall()]
        except Exception as e:
            logger.exception("Error getting DB status: %s", e)
            status["error"] = str(e)
        return status

    def __del__(self):
        try:
            self.close_connection()
        except Exception:
            pass

# Instantiate DB
db = Database()

# --- Web server (merged) ---
class WebServer:
    def __init__(self, port: int = WEB_SERVER_PORT):
        self.port = port
        self.app = Flask(__name__)
        self.start_time = time.time()
        self._monitor_callback = None
        self._cached_container_limit_mb = None
        self.setup_routes()

    def register_monitoring(self, callback):
        self._monitor_callback = callback
        logger.info("Monitoring callback registered")

    def _mb_from_bytes(self, n_bytes: int) -> float:
        return round(n_bytes / (1024 * 1024), 2)

    def _read_cgroup_memory_limit_bytes(self) -> int:
        candidates = [
            "/sys/fs/cgroup/memory.max",
            "/sys/fs/cgroup/memory/memory.limit_in_bytes",
        ]
        for path in candidates:
            try:
                if not os.path.exists(path):
                    continue
                with open(path, "r") as fh:
                    raw = fh.read().strip()
                if raw == "max":
                    return 0
                val = int(raw)
                if val <= 0:
                    return 0
                if val > (1 << 50):
                    return 0
                return val
            except Exception:
                continue
        try:
            with open("/proc/self/cgroup", "r") as fh:
                lines = fh.read().splitlines()
            for ln in lines:
                parts = ln.split(":")
                if len(parts) >= 3:
                    controllers = parts[1]
                    cpath = parts[2]
                    if "memory" in controllers.split(","):
                        possible = f"/sys/fs/cgroup/memory{cpath}/memory.limit_in_bytes"
                        if os.path.exists(possible):
                            with open(possible, "r") as fh:
                                raw = fh.read().strip()
                            val = int(raw)
                            if val > 0 and val < (1 << 50):
                                return val
                        possible2 = f"/sys/fs/cgroup{cpath}/memory.max"
                        if os.path.exists(possible2):
                            with open(possible2, "r") as fh:
                                raw = fh.read().strip()
                            if raw != "max":
                                val = int(raw)
                                if val > 0 and val < (1 << 50):
                                    return val
        except Exception:
            pass
        return 0

    def get_container_memory_limit_mb(self) -> float:
        if self._cached_container_limit_mb is not None:
            return self._cached_container_limit_mb
        bytes_limit = self._read_cgroup_memory_limit_bytes()
        if bytes_limit and bytes_limit > 0:
            self._cached_container_limit_mb = self._mb_from_bytes(bytes_limit)
        else:
            self._cached_container_limit_mb = float(os.getenv("CONTAINER_MAX_RAM_MB", str(_DEFAULT_CONTAINER_MAX_RAM_MB)))
        return self._cached_container_limit_mb

    def setup_routes(self):
        @self.app.route("/", methods=["GET"])
        def home():
            container_limit = self.get_container_memory_limit_mb()
            html = f"""
            <!DOCTYPE html>
            <html>
            <head>
                <title>Combined Bot Status</title>
                <style>
                    body {{
                        font-family: Arial, sans-serif;
                        text-align: center;
                        padding: 50px;
                        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                        color: white;
                    }}
                    .status {{
                        background: rgba(255,255,255,0.1);
                        padding: 30px;
                        border-radius: 15px;
                        max-width: 800px;
                        margin: 0 auto;
                        text-align: left;
                    }}
                    h1 {{ font-size: 2.2em; margin: 0; text-align: center; }}
                    p {{ font-size: 1.0em; }}
                    .emoji {{ font-size: 2.5em; text-align: center; }}
                    .stats {{ font-family: monospace; margin-top: 12px; }}
                </style>
            </head>
            <body>
                <div class="status">
                    <div class="emoji">🤖🔍</div>
                    <h1>Combined Forwarder & Monitor Bot Status</h1>
                    <p>Bot is running. Use the monitoring endpoints:</p>
                    <ul>
                      <li>/health — basic uptime</li>
                      <li>/webhook — simple webhook endpoint</li>
                      <li>/metrics — bot metrics</li>
                    </ul>
                    <div class="stats">
                      <strong>Container memory limit (detected):</strong> {container_limit} MB
                    </div>
                </div>
            </body>
            </html>
            """
            return html

        @self.app.route("/health", methods=["GET"])
        def health():
            uptime = int(time.time() - self.start_time)
            return jsonify({"status": "healthy", "uptime_seconds": uptime}), 200

        @self.app.route("/webhook", methods=["GET", "POST"])
        def webhook():
            now = int(time.time())
            if request.method == "POST":
                data = request.get_json(silent=True) or {}
                return jsonify({"status": "ok", "received": True, "timestamp": now, "data": data}), 200
            return jsonify({"status": "ok", "method": "GET", "timestamp": now}), 200

        @self.app.route("/metrics", methods=["GET"])
        def metrics():
            if self._monitor_callback is None:
                return jsonify({"status": "unavailable", "reason": "no monitor registered"}), 200
            try:
                data = self._monitor_callback()
                return jsonify({"status": "ok", "metrics": data}), 200
            except Exception as e:
                logger.exception("Monitoring callback failed")
                return jsonify({"status": "error", "error": str(e)}), 500

    def run_server(self):
        self.app.run(host="0.0.0.0", port=self.port, debug=False, use_reloader=False, threaded=True)

    def start(self):
        server_thread = threading.Thread(target=self.run_server, daemon=True)
        server_thread.start()
        logger.info(f"🌐 Web server started on port {self.port}")

web_server = WebServer(port=WEB_SERVER_PORT)

# --- Flood wait manager (from forward.py) ---
class FloodWaitManager:
    """Manages flood wait states for users"""
    def __init__(self):
        self.user_flood_wait_until: Dict[int, float] = {}
        self.start_notifications_sent: Set[str] = set()
        self.end_notifications_pending: Set[int] = set()
        self.lock = threading.Lock()

    def set_flood_wait(self, user_id: int, wait_seconds: int):
        with self.lock:
            wait_until = time.time() + wait_seconds + 5
            self.user_flood_wait_until[user_id] = wait_until

            should_notify_start = False
            if wait_seconds > 60:
                flood_wait_key = f"{user_id}_start_{int(wait_until)}"
                if flood_wait_key not in self.start_notifications_sent:
                    self.start_notifications_sent.add(flood_wait_key)
                    self.end_notifications_pending.add(user_id)
                    should_notify_start = True
            return should_notify_start, wait_seconds

    def is_in_flood_wait(self, user_id: int):
        with self.lock:
            if user_id not in self.user_flood_wait_until:
                should_notify_end = user_id in self.end_notifications_pending
                if should_notify_end:
                    self.end_notifications_pending.discard(user_id)
                    self._cleanup_old_notifications(user_id)
                return False, 0, should_notify_end
            wait_until = self.user_flood_wait_until[user_id]
            current_time = time.time()
            if current_time >= wait_until:
                del self.user_flood_wait_until[user_id]
                should_notify_end = user_id in self.end_notifications_pending
                if should_notify_end:
                    self.end_notifications_pending.discard(user_id)
                    self._cleanup_old_notifications(user_id)
                return False, 0, should_notify_end
            return True, wait_until - current_time, False

    def _cleanup_old_notifications(self, user_id: int):
        keys_to_remove = [k for k in list(self.start_notifications_sent) if k.startswith(f"{user_id}_")]
        for k in keys_to_remove:
            self.start_notifications_sent.discard(k)

    def clear_flood_wait(self, user_id: int):
        with self.lock:
            self.user_flood_wait_until.pop(user_id, None)
            self._cleanup_old_notifications(user_id)
            self.end_notifications_pending.discard(user_id)

flood_wait_manager = FloodWaitManager()

# --- Globals for bot runtime ---
user_clients: Dict[int, TelegramClient] = {}
login_states: Dict[int, Dict] = {}
logout_states: Dict[int, Dict] = {}
user_session_strings: Dict[int, str] = {}
phone_verification_states: Dict[int, Dict] = {}
task_creation_states_forward: Dict[int, Dict[str, Any]] = {}
task_creation_states_monitor: Dict[int, Dict[str, Any]] = {}

tasks_cache_forward: Dict[int, List[Dict]] = {}
tasks_cache_monitor: Dict[int, List[Dict]] = {}
target_entity_cache: Dict[int, OrderedDict] = {}
handler_registered: Dict[int, Callable] = {}
handler_registered_monitor: Dict[int, List[Callable]] = {}
user_send_semaphores: Dict[int, asyncio.Semaphore] = {}
user_rate_limiters: Dict[int, Tuple[float, float, float]] = {}  # (tokens, last_refill_time, burst_tokens)

# For duplicate detection
message_history: Dict[Tuple[int, int], deque] = {}  # (user_id, chat_id) -> deque((hash, ts, preview))
notification_messages: Dict[int, Dict] = {}  # message_id -> metadata

# Queues and workers
send_queue: Optional[asyncio.Queue] = None
send_worker_tasks: List[asyncio.Task] = []
_notification_queue: Optional[asyncio.Queue] = None
notification_worker_tasks: List[asyncio.Task] = []
_workers_started = False
_main_loop: Optional[asyncio.AbstractEventLoop] = None

# Misc caches and GC
_last_gc_run = 0

# --- Utility functions (merged) ---
def _clean_phone_number(text: str) -> str:
    return '+' + ''.join(c for c in text if c.isdigit())

def _get_cached_auth(user_id: int) -> Optional[bool]:
    # lightweight auth cache shared between handlers
    if user_id in _auth_cache:
        allowed, ts = _auth_cache[user_id]
        if time.time() - ts < _AUTH_CACHE_TTL:
            return allowed
    return None

def _set_cached_auth(user_id: int, allowed: bool):
    _auth_cache[user_id] = (allowed, time.time())

_auth_cache: Dict[int, Tuple[bool, float]] = {}
_AUTH_CACHE_TTL = 300

async def db_call_threadpool(func, *args, **kwargs):
    """Run DB-bound function in a separate threadpool executor to avoid blocking event loop"""
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, functools.partial(func, *args, **kwargs))

async def optimized_gc():
    global _last_gc_run
    current_time = time.time()
    if current_time - _last_gc_run > GC_INTERVAL:
        try:
            collected = gc.collect(2)
            if collected > 1000:
                logger.debug("GC collected %s objects", collected)
        except Exception:
            try:
                gc.collect()
            except Exception:
                pass
        _last_gc_run = current_time

def extract_words(text: str) -> List[str]:
    return WORD_PATTERN.findall(text)

def is_numeric_word(word: str) -> bool:
    return bool(NUMERIC_PATTERN.match(word))

def is_alphabetic_word(word: str) -> bool:
    return bool(ALPHABETIC_PATTERN.match(word))

def contains_numeric(word: str) -> bool:
    return any(c.isdigit() for c in word)

def contains_alphabetic(word: str) -> bool:
    return any(c.isalpha() for c in word)

def contains_special_characters(word: str) -> bool:
    for char in word:
        if not char.isalnum() and not EMOJI_PATTERN.search(char):
            return True
    return False

def apply_filters(message_text: str, task_filters: Dict) -> List[str]:
    """Apply forwarding filters (word-splitting, special filters, prefix/suffix).
    Returns list of messages to send (may be multiple words)."""
    if not message_text:
        return []

    filters_enabled = task_filters.get('filters', {})

    if filters_enabled.get('raw_text', False):
        processed = message_text
        if prefix := filters_enabled.get('prefix'):
            processed = prefix + processed
        if suffix := filters_enabled.get('suffix'):
            processed = processed + suffix
        return [processed]

    messages_to_send = []

    if filters_enabled.get('numbers_only', False):
        if is_numeric_word(message_text.replace(' ', '')):
            processed = message_text
            if prefix := filters_enabled.get('prefix'):
                processed = prefix + processed
            if suffix := filters_enabled.get('suffix'):
                processed = processed + suffix
            messages_to_send.append(processed)

    elif filters_enabled.get('alphabets_only', False):
        if is_alphabetic_word(message_text.replace(' ', '')):
            processed = message_text
            if prefix := filters_enabled.get('prefix'):
                processed = prefix + processed
            if suffix := filters_enabled.get('suffix'):
                processed = processed + suffix
            messages_to_send.append(processed)

    else:
        words = extract_words(message_text)
        for word in words:
            if not word:
                continue
            skip_word = False
            if filters_enabled.get('removed_alphabetic', False):
                if contains_numeric(word) or EMOJI_PATTERN.search(word):
                    skip_word = True
            elif filters_enabled.get('removed_numeric', False):
                if contains_alphabetic(word) or EMOJI_PATTERN.search(word):
                    skip_word = True
            if not skip_word:
                processed = word
                if prefix := filters_enabled.get('prefix'):
                    processed = prefix + processed
                if suffix := filters_enabled.get('suffix'):
                    processed = processed + suffix
                messages_to_send.append(processed)
    return messages_to_send

# --- Rate limiter & semaphores for forwarding ---
def _ensure_user_target_cache(user_id: int):
    if user_id not in target_entity_cache:
        target_entity_cache[user_id] = OrderedDict()

def _get_cached_target(user_id: int, target_id: int):
    _ensure_user_target_cache(user_id)
    od = target_entity_cache[user_id]
    if target_id in od:
        od.move_to_end(target_id)
        return od[target_id]
    return None

def _set_cached_target(user_id: int, target_id: int, entity: object):
    _ensure_user_target_cache(user_id)
    od = target_entity_cache[user_id]
    od[target_id] = entity
    od.move_to_end(target_id)
    while len(od) > TARGET_ENTITY_CACHE_SIZE:
        od.popitem(last=False)

def _ensure_user_send_semaphore(user_id: int):
    if user_id not in user_send_semaphores:
        user_send_semaphores[user_id] = asyncio.Semaphore(SEND_CONCURRENCY_PER_USER)

def _ensure_user_rate_limiter(user_id: int):
    if user_id not in user_rate_limiters:
        user_rate_limiters[user_id] = (SEND_RATE_PER_USER, time.time(), SEND_RATE_PER_USER * 5)

async def _consume_token(user_id: int, amount: float = 1.0):
    _ensure_user_rate_limiter(user_id)
    while True:
        tokens, last_refill, burst = user_rate_limiters[user_id]
        now = time.time()
        elapsed = max(0.0, now - last_refill)
        refill = elapsed * SEND_RATE_PER_USER
        tokens = min(tokens + refill, burst)
        if tokens >= amount:
            tokens -= amount
            user_rate_limiters[user_id] = (tokens, now, burst)
            return
        user_rate_limiters[user_id] = (tokens, now, burst)
        needed = amount - tokens
        wait_time = needed / SEND_RATE_PER_USER
        await asyncio.sleep(min(wait_time, 0.1))

# --- Duplicate detection helpers (from monitor.py) ---
def create_message_hash(message_text: str, sender_id: Optional[int] = None) -> str:
    if sender_id:
        content = f"{sender_id}:{message_text.strip().lower()}"
    else:
        content = message_text.strip().lower()
    return hashlib.md5(content.encode()).hexdigest()[:12]

def is_duplicate_message_m(user_id: int, chat_id: int, message_hash: str) -> bool:
    key = (user_id, chat_id)
    if key not in message_history:
        return False
    current_time = time.time()
    dq = message_history[key]
    while dq and current_time - dq[0][1] > DUPLICATE_CHECK_WINDOW:
        dq.popleft()
    return any(stored_hash == message_hash for stored_hash, _, _ in dq)

def store_message_hash_m(user_id: int, chat_id: int, message_hash: str, message_text: str):
    key = (user_id, chat_id)
    if key not in message_history:
        message_history[key] = deque(maxlen=MESSAGE_HASH_LIMIT)
    message_history[key].append((message_hash, time.time(), message_text[:80]))

# --- Notifications for flood wait and duplicate events ---
async def notify_user_flood_wait(user_id: int, wait_seconds: int):
    try:
        bot = Bot(token=BOT_TOKEN)
        wait_minutes = wait_seconds // 60
        if wait_seconds % 60 > 0:
            wait_minutes += 1
        resume_time = datetime.fromtimestamp(time.time() + wait_seconds).strftime('%H:%M:%S')
        message = f"""⏰ **Flood Wait Alert**

Your account is temporarily limited by Telegram.

📋 **Details:**
• Wait time: {wait_minutes} minutes
• Resumes at: {resume_time}

⚠️ **Please note:**
• This is a Telegram restriction, not the bot
• Bot will automatically resume when the wait ends
• No action is needed on your part

🔄 **Status:** ⏳ Waiting for Telegram to lift restriction..."""
        await bot.send_message(user_id, message, parse_mode="Markdown")
    except Exception:
        pass

async def notify_user_flood_wait_ended(user_id: int):
    try:
        bot = Bot(token=BOT_TOKEN)
        message = f"""✅ **Flood Wait Ended**

Your account restriction has been lifted!

📋 **Status:**
• Forwarding has resumed automatically
• All queued messages are being sent
• You can now send messages normally

🔄 **Status:** ✅ Active and forwarding..."""
        await bot.send_message(user_id, message, parse_mode="Markdown")
    except Exception:
        pass

# --- Send worker loop (forwarding) ---
async def send_worker_loop(worker_id: int):
    logger.info(f"Send worker {worker_id} started")
    global send_queue
    if send_queue is None:
        return
    processed_count = 0
    last_log_time = time.time()
    while True:
        try:
            try:
                job = send_queue.get_nowait()
            except asyncio.QueueEmpty:
                await asyncio.sleep(0.01)
                continue

            user_id, target_id, message_text, task_filters, forward_tag, source_chat_id, message_id = job

            # Flood wait check
            in_flood_wait, wait_left, should_notify_end = flood_wait_manager.is_in_flood_wait(user_id)
            if should_notify_end:
                asyncio.create_task(notify_user_flood_wait_ended(user_id))
            if in_flood_wait:
                try:
                    send_queue.put_nowait(job)
                except asyncio.QueueFull:
                    logger.warning("Queue full while requeueing flood wait message")
                finally:
                    send_queue.task_done()
                await asyncio.sleep(min(wait_left, 1.0))
                continue

            client = user_clients.get(user_id)
            if not client:
                send_queue.task_done()
                continue

            await _consume_token(user_id, 1.0)

            try:
                entity = _get_cached_target(user_id, target_id)
                if not entity:
                    try:
                        entity = await client.get_input_entity(int(target_id))
                        _set_cached_target(user_id, target_id, entity)
                    except Exception:
                        entity = None

                if not entity:
                    send_queue.task_done()
                    continue

                try:
                    if forward_tag and source_chat_id and message_id:
                        try:
                            source_entity = await client.get_input_entity(int(source_chat_id))
                            await client.forward_messages(entity, message_id, source_entity)
                        except Exception:
                            await client.send_message(entity, message_text)
                    else:
                        await client.send_message(entity, message_text)
                    flood_wait_manager.clear_flood_wait(user_id)
                except FloodWaitError as fwe:
                    wait = int(getattr(fwe, "seconds", 10))
                    logger.warning("Worker %s: Flood wait %ss for user %s", worker_id, wait, user_id)
                    should_notify_start, wait_time = flood_wait_manager.set_flood_wait(user_id, wait)
                    try:
                        send_queue.put_nowait(job)
                    except asyncio.QueueFull:
                        logger.warning("Queue full while requeueing flood wait")
                    if should_notify_start and wait_time > 60:
                        asyncio.create_task(notify_user_flood_wait(user_id, wait_time))
                except Exception as e:
                    logger.debug("Send failed: %s", e)
            except Exception as e:
                logger.debug("Entity resolution failed: %s", e)
            finally:
                send_queue.task_done()
                processed_count += 1
                current_time = time.time()
                if current_time - last_log_time > 30:
                    qsize = send_queue.qsize() if send_queue else 0
                    logger.info("Worker %s: Processed %s, Queue: %s", worker_id, processed_count, qsize)
                    processed_count = 0
                    last_log_time = current_time
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(0.01)

async def start_send_workers():
    global send_queue, send_worker_tasks
    if send_queue is None:
        send_queue = asyncio.Queue(maxsize=SEND_QUEUE_MAXSIZE)
    if send_worker_tasks:
        return
    for i in range(SEND_WORKER_COUNT):
        t = asyncio.create_task(send_worker_loop(i + 1))
        send_worker_tasks.append(t)
    logger.info("Spawned %s send workers", SEND_WORKER_COUNT)

# --- Notification worker loop (monitoring) ---
async def notification_worker(worker_id: int, bot_instance: Bot):
    logger.info("Notification worker %s started", worker_id)
    global _notification_queue
    if _notification_queue is None:
        logger.error("notification worker started before queue initialized")
        return
    while True:
        try:
            user_id, task, chat_id, message_id, message_text, message_hash = await _notification_queue.get()
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.exception("Error getting item from notification queue: %s", e)
            break

        try:
            settings = task.get("settings", {})
            if not settings.get("manual_reply_system", True):
                continue

            task_label = task.get("label", "Unknown")
            preview_text = message_text[:100] + "..." if len(message_text) > 100 else message_text

            notification_msg = (
                f"🚨 **DUPLICATE MESSAGE DETECTED!**\n\n"
                f"**Task:** {task_label}\n"
                f"**Time:** {time.strftime('%Y-%m-%d %H:%M:%S')}\n\n"
                f"📝 **Message Preview:**\n`{preview_text}`\n\n"
                f"💬 **Reply to this message to respond to the duplicate!**\n"
                f"(Swipe left on this message and type your reply)"
            )
            try:
                sent_message = await bot_instance.send_message(chat_id=user_id, text=notification_msg, parse_mode="Markdown")
                notification_messages[sent_message.message_id] = {
                    "user_id": user_id,
                    "task_label": task_label,
                    "chat_id": chat_id,
                    "original_message_id": message_id,
                    "duplicate_hash": message_hash,
                    "message_preview": preview_text
                }
                logger.info("Sent duplicate notification to user %s for chat %s", user_id, chat_id)
            except Exception as e:
                logger.error("Failed to send notification to user %s: %s", user_id, e)
        except Exception:
            logger.exception("Unexpected error in notification worker")
        finally:
            try:
                _notification_queue.task_done()
            except Exception:
                pass

async def start_notification_workers(bot_instance: Bot):
    global _notification_queue, notification_worker_tasks
    if _notification_queue is None:
        _notification_queue = asyncio.Queue(maxsize=NOTIFY_QUEUE_MAXSIZE)
    if notification_worker_tasks:
        return
    for i in range(MONITOR_WORKER_COUNT):
        t = asyncio.create_task(notification_worker(i + 1, bot_instance))
        notification_worker_tasks.append(t)
    logger.info("Spawned %s notification workers", MONITOR_WORKER_COUNT)

# --- Event handler registration utilities ---
def ensure_forward_handler_registered_for_user(user_id: int, client: TelegramClient):
    """Attaches event handlers for forwarding (NewMessage and MessageEdited)."""
    if handler_registered.get(user_id):
        return

    async def _hot_message_handler(event):
        try:
            await optimized_gc()
            is_edit = isinstance(event, events.MessageEdited)
            message = getattr(event, "message", None)
            if not message:
                return
            message_text = getattr(event, "raw_text", None) or getattr(message, "message", None)
            if not message_text:
                return
            chat_id = getattr(event, "chat_id", None) or getattr(message, "chat_id", None)
            if chat_id is None:
                return
            user_tasks = tasks_cache_forward.get(user_id)
            if not user_tasks:
                return
            message_outgoing = getattr(message, "out", False)
            for task in user_tasks:
                # respect 'control' flag
                if not task.get("filters", {}).get("control", True):
                    continue
                if message_outgoing and not task.get("filters", {}).get("outgoing", True):
                    continue
                if chat_id in task.get("source_ids", []):
                    forward_tag = task.get("filters", {}).get("forward_tag", False)
                    filtered_messages = apply_filters(message_text, task.get("filters", {}))
                    for filtered_msg in filtered_messages:
                        for target_id in task.get("target_ids", []):
                            try:
                                if send_queue is None:
                                    continue
                                await send_queue.put((user_id, target_id, filtered_msg, task.get("filters", {}), forward_tag, chat_id if forward_tag else None, message.id if forward_tag else None))
                            except asyncio.QueueFull:
                                logger.warning("Send queue full")
        except Exception:
            logger.exception("Error in forward message handler")

    try:
        client.add_event_handler(_hot_message_handler, events.NewMessage())
        client.add_event_handler(_hot_message_handler, events.MessageEdited())
        handler_registered[user_id] = _hot_message_handler
    except Exception:
        logger.exception("Failed to add forward event handler")

async def resolve_target_entity_once(user_id: int, client: TelegramClient, target_id: int):
    ent = _get_cached_target(user_id, target_id)
    if ent:
        return ent
    try:
        entity = await client.get_input_entity(int(target_id))
        _set_cached_target(user_id, target_id, entity)
        return entity
    except Exception:
        return None

async def resolve_targets_for_user(user_id: int, target_ids: List[int]):
    client = user_clients.get(user_id)
    if not client:
        return
    for tid in target_ids:
        for attempt in range(3):
            ent = await resolve_target_entity_once(user_id, client, tid)
            if ent:
                break
            await asyncio.sleep(TARGET_RESOLVE_RETRY_SECONDS)

# Monitoring handlers utilities
async def register_monitor_handlers_for_user(user_id: int, client: TelegramClient):
    """Register per-monitored-chat handlers to detect duplicates"""
    if user_id in handler_registered_monitor:
        return

    handler_list = []

    # We'll register a single handler per user's monitored chats via iterating tasks
    async def _monitoring_handler(event):
        try:
            await optimized_gc()
            message = getattr(event, "message", None)
            if not message:
                return
            message_text = event.raw_text or message.message
            if not message_text:
                return
            sender_id = getattr(message, "sender_id", None)
            message_id = getattr(message, "id", None)
            chat_id = getattr(message, "chat_id", None) or getattr(event, "chat_id", None)
            message_outgoing = getattr(message, "out", False)

            user_tasks_local = tasks_cache_monitor.get(user_id, [])
            for task in user_tasks_local:
                if chat_id not in task.get("chat_ids", []):
                    continue
                settings = task.get("settings", {})
                if message_outgoing and not settings.get("outgoing_message_monitoring", True):
                    continue
                if settings.get("check_duplicate_and_notify", True):
                    message_hash = create_message_hash(message_text, sender_id)
                    if is_duplicate_message_m(user_id, chat_id, message_hash):
                        logger.info("DUPLICATE DETECTED: user=%s task=%s chat=%s", user_id, task.get("label"), chat_id)
                        # Auto-reply if configured
                        if settings.get("auto_reply_system", False) and settings.get("auto_reply_message"):
                            try:
                                chat_entity = await client.get_input_entity(chat_id)
                                await client.send_message(chat_entity, settings.get("auto_reply_message"), reply_to=message_id)
                            except Exception as e:
                                logger.exception("Error sending auto reply: %s", e)
                        # Manual notify: put into notification queue
                        if settings.get("manual_reply_system", True):
                            if _notification_queue:
                                try:
                                    await _notification_queue.put((user_id, task, chat_id, message_id, message_text, message_hash))
                                except asyncio.QueueFull:
                                    logger.warning("Notification queue full, dropping duplicate alert for user=%s", user_id)
                            else:
                                logger.error("Notification queue not initialized!")
                        continue
                    store_message_hash_m(user_id, chat_id, message_hash, message_text)
        except Exception:
            logger.exception("Error in monitoring handler for user %s", user_id)

    # Register handler on client for NewMessage and MessageEdited across all chats (we'll use chat filter when adding per-task)
    try:
        # Instead of adding per-chat handlers, to simplify we add global handler and check chat membership inside
        client.add_event_handler(_monitoring_handler, events.NewMessage())
        client.add_event_handler(_monitoring_handler, events.MessageEdited())
        handler_list.append(_monitoring_handler)
        handler_registered_monitor[user_id] = handler_list
        logger.info("Registered monitoring handler for user %s", user_id)
    except Exception:
        logger.exception("Failed to register monitoring handlers for user %s", user_id)

# --- Session restore and start forwarding/monitoring ---
async def start_forwarding_for_user(user_id: int):
    if user_id not in user_clients:
        return
    client = user_clients[user_id]
    tasks_cache_forward.setdefault(user_id, [])
    _ensure_user_target_cache(user_id)
    _ensure_user_send_semaphore(user_id)
    _ensure_user_rate_limiter(user_id)
    ensure_forward_handler_registered_for_user(user_id, client)
    # Resolve existing targets
    user_tasks = tasks_cache_forward.get(user_id, [])
    if user_tasks:
        all_targets = []
        for task in user_tasks:
            all_targets.extend(task.get("target_ids", []))
        if all_targets:
            unique_targets = list(set(all_targets))
            asyncio.create_task(resolve_targets_for_user(user_id, unique_targets))

async def start_monitoring_for_user(user_id: int):
    if user_id not in user_clients:
        return
    client = user_clients[user_id]
    tasks_cache_monitor.setdefault(user_id, [])
    register_monitor_handlers_for_user(user_id, client)

async def restore_sessions():
    """Restore sessions from env and DB and load tasks into caches"""
    logger.info("Restoring sessions (combined)...")
    # First, populate task caches from DB
    try:
        all_forward = await db_call_threadpool(db.get_all_active_forwarding_tasks)
    except Exception:
        all_forward = []
    try:
        all_monitor = await db_call_threadpool(db.get_all_active_monitoring_tasks)
    except Exception:
        all_monitor = []

    tasks_cache_forward.clear()
    tasks_cache_monitor.clear()
    for t in all_forward:
        uid = t["user_id"]
        tasks_cache_forward.setdefault(uid, []).append({
            "id": t["id"], "label": t["label"], "source_ids": t["source_ids"], "target_ids": t["target_ids"], "is_active": 1, "filters": t.get("filters", {})
        })
    for t in all_monitor:
        uid = t["user_id"]
        tasks_cache_monitor.setdefault(uid, []).append({
            "id": t["id"], "label": t["label"], "chat_ids": t["chat_ids"], "is_active": 1, "settings": t.get("settings", {})
        })

    # Restore sessions from env first
    for user_id, session_string in USER_SESSIONS.items():
        if len(user_clients) >= MAX_CONCURRENT_USERS:
            continue
        try:
            await restore_single_session(user_id, session_string, from_env=True)
        except Exception:
            pass

    # Then restore from DB logged-in users
    try:
        users = await asyncio.to_thread(lambda: db.get_logged_in_users(MAX_CONCURRENT_USERS * 2))
    except Exception:
        users = []

    batch_size = 3
    restore_tasks = []
    for row in users:
        try:
            user_id = row.get("user_id") if isinstance(row, dict) else row[0]
            session_data = row.get("session_data") if isinstance(row, dict) else row[1]
        except Exception:
            continue
        if session_data and user_id not in user_clients:
            restore_tasks.append(restore_single_session(user_id, session_data, from_env=False))
        if len(restore_tasks) >= batch_size:
            await asyncio.gather(*restore_tasks, return_exceptions=True)
            restore_tasks = []
            await asyncio.sleep(0.5)
    if restore_tasks:
        await asyncio.gather(*restore_tasks, return_exceptions=True)

async def restore_single_session(user_id: int, session_data: str, from_env: bool = False):
    try:
        client = TelegramClient(StringSession(session_data), API_ID, API_HASH)
        await client.connect()
        if await client.is_user_authorized():
            if len(user_clients) >= MAX_CONCURRENT_USERS:
                try: await client.disconnect()
                except Exception: pass
                if not from_env:
                    await db_call_threadpool(db.save_user, user_id, None, None, None, True)
                return
            user_clients[user_id] = client
            user_session_strings[user_id] = session_data
            me = await client.get_me()
            user_name = me.first_name or "User"
            user = await db_call_threadpool(db.get_user, user_id)
            has_phone = user and user.get("phone")
            await db_call_threadpool(db.save_user, user_id, user["phone"] if user else None, user_name, session_data, True)
            target_entity_cache.setdefault(user_id, OrderedDict())
            _ensure_user_send_semaphore(user_id)
            _ensure_user_rate_limiter(user_id)
            await start_forwarding_for_user(user_id)
            await start_monitoring_for_user(user_id)
            # Resolve targets & chat entities if tasks exist
            user_tasks_f = tasks_cache_forward.get(user_id, [])
            if user_tasks_f:
                all_targets = []
                for tt in user_tasks_f: all_targets.extend(tt.get("target_ids", []))
                if all_targets:
                    asyncio.create_task(resolve_targets_for_user(user_id, list(set(all_targets))))
            user_tasks_m = tasks_cache_monitor.get(user_id, [])
            if user_tasks_m:
                # nothing heavy to resolve besides starting handlers
                pass
            source = "environment variable" if from_env else "database"
            logger.info("Restored session for user %s from %s", user_id, source)
        else:
            if not from_env:
                await db_call_threadpool(db.save_user, user_id, None, None, None, False)
    except Exception as e:
        logger.exception("Failed to restore session for user %s: %s", user_id, e)
        if not from_env:
            try:
                await db_call_threadpool(db.save_user, user_id, None, None, None, False)
            except Exception:
                pass

# --- Shutdown cleanup ---
async def shutdown_cleanup():
    logger.info("Shutdown cleanup...")
    # cancel workers
    for t in list(send_worker_tasks):
        try: t.cancel()
        except Exception: pass
    for t in list(notification_worker_tasks):
        try: t.cancel()
        except Exception: pass
    if send_worker_tasks:
        try:
            await asyncio.gather(*send_worker_tasks, return_exceptions=True)
        except Exception:
            pass
    if notification_worker_tasks:
        try:
            await asyncio.gather(*notification_worker_tasks, return_exceptions=True)
        except Exception:
            pass

    # disconnect clients in batches
    user_ids = list(user_clients.keys())
    batch_size = 5
    for i in range(0, len(user_ids), batch_size):
        batch = user_ids[i:i + batch_size]
        disconnect_tasks = []
        for uid in batch:
            client = user_clients.get(uid)
            if not client: continue
            # remove handlers
            handler = handler_registered.get(uid)
            if handler:
                try:
                    client.remove_event_handler(handler)
                except Exception:
                    pass
                handler_registered.pop(uid, None)
            if uid in handler_registered_monitor:
                for h in handler_registered_monitor.get(uid, []):
                    try:
                        client.remove_event_handler(h)
                    except Exception:
                        pass
                handler_registered_monitor.pop(uid, None)
            try:
                disconnect_tasks.append(client.disconnect())
            except Exception:
                try:
                    sess = getattr(client, "session", None)
                    if sess: sess.close()
                except Exception:
                    pass
        if disconnect_tasks:
            try:
                await asyncio.gather(*disconnect_tasks, return_exceptions=True)
            except Exception:
                pass

    user_clients.clear()
    user_session_strings.clear()
    phone_verification_states.clear()
    tasks_cache_forward.clear()
    tasks_cache_monitor.clear()
    target_entity_cache.clear()
    user_send_semaphores.clear()
    user_rate_limiters.clear()
    notification_messages.clear()
    message_history.clear()

    try:
        db.close_connection()
    except Exception:
        pass

    logger.info("Shutdown cleanup complete.")

# --- Telegram bot handlers (merged) ---

# Authorization helpers (shared)
async def _send_unauthorized(update: Update):
    if update.message:
        await update.message.reply_text(UNAUTHORIZED_MESSAGE, parse_mode="Markdown", disable_web_page_preview=True)
    elif update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.message.reply_text(UNAUTHORIZED_MESSAGE, parse_mode="Markdown", disable_web_page_preview=True)

async def check_authorization(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    user_id = update.effective_user.id
    cached = _get_cached_auth(user_id)
    if cached is not None:
        if not cached:
            await _send_unauthorized(update)
        return cached
    if user_id in ALLOWED_USERS or user_id in OWNER_IDS:
        _set_cached_auth(user_id, True)
        return True
    try:
        is_allowed_db = await db_call_threadpool(db.is_user_allowed, user_id)
        _set_cached_auth(user_id, is_allowed_db)
        if not is_allowed_db:
            await _send_unauthorized(update)
        return is_allowed_db
    except Exception:
        logger.exception("Auth check failed for %s", user_id)
        _set_cached_auth(user_id, False)
        await _send_unauthorized(update)
        return False

# Phone verification flow (shared)
async def check_phone_number_required(user_id: int) -> bool:
    user = await db_call_threadpool(db.get_user, user_id)
    return bool(user and user.get("is_logged_in") and not user.get("phone"))

async def ask_for_phone_number(user_id: int, chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    phone_verification_states[user_id] = {"step": "waiting_phone", "chat_id": chat_id}
    message = """📱 **Phone Number Verification Required**

Your account was restored from a saved session, but we need your phone number for security.

⚠️ **Important:**
• This is the phone number associated with your Telegram account
• It will only be used for logout confirmation
• Your phone number is stored securely

**Please enter your phone number (with country code):**

**Examples:**
• `+1234567890`
• `+447911123456`
• `+4915112345678`

**Type your phone number now:**"""
    try:
        await context.bot.send_message(chat_id, message, parse_mode="Markdown")
    except Exception:
        logger.exception("Failed to send phone verification message")

async def handle_phone_verification(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id not in phone_verification_states:
        return
    text = (update.message.text or "").strip()
    state = phone_verification_states[user_id]
    if state.get("step") != "waiting_phone":
        return
    if not text.startswith('+'):
        await update.message.reply_text("❌ **Invalid format!**\n\nPhone number must start with `+`\nExample: `+1234567890`", parse_mode="Markdown")
        return
    clean_phone = _clean_phone_number(text)
    if len(clean_phone) < 8:
        await update.message.reply_text("❌ **Invalid phone number!**\n\nPhone number seems too short.", parse_mode="Markdown")
        return
    client = user_clients.get(user_id)
    try:
        me = None
        if client:
            me = await client.get_me()
        await db_call_threadpool(db.save_user, user_id, clean_phone, me.first_name if me else None, user_session_strings.get(user_id), True)
        phone_verification_states.pop(user_id, None)
        await update.message.reply_text(f"✅ **Phone number verified!**\n\n📱 **Phone:** `{clean_phone}`\n👤 **Name:** {me.first_name if me else 'User'}\n\nYour account is now fully restored! 🎉", parse_mode="Markdown")
    except Exception:
        logger.exception("Error verifying phone")
        await update.message.reply_text("❌ **Error verifying phone number!**")

# Main menu / start (merged UI)
async def show_main_menu(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    user = await db_call_threadpool(db.get_user, user_id)
    user_name = update.effective_user.first_name or "User"
    user_phone = user["phone"] if user and user.get("phone") else "Not connected"
    is_logged_in = bool(user and user.get("is_logged_in"))
    status_emoji = "🟢" if is_logged_in else "🔴"
    status_text = "Online" if is_logged_in else "Offline"
    message_text = f"""╔═══════════════════════════╗
║   🤖 FORWARDER & MONITOR  ║
║  TELEGRAM MESSAGE TOOLSET ║
╚═══════════════════════════╝

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

👤 **User:** {user_name}
📱 **Phone:** `{user_phone}`
{status_emoji} **Status:** {status_text}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📋 **COMMANDS:**

🔐 **Account Management:**
  /login - Connect your Telegram account
  /logout - Disconnect your account

📨 **Forwarding Tasks:**
  /forwadd - Create a new forwarding task
  /fortasks - List all your forwarding tasks

🔍 **Monitoring Tasks:**
  /monitoradd - Create a new monitoring task
  /monitortasks - List all your monitoring tasks

🆔 **Utilities:**
  /getallid - Get all your chat IDs"""
    if user_id in OWNER_IDS:
        message_text += "\n\n👑 **Owner Commands:**\n  /ownersets - Owner control panel"
    message_text += "\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n⚙️ **How it works:**\n1. Connect your account with /login\n2. Create forwarding/monitoring tasks\n3. For monitoring: duplicates send notifications; you can reply to the notification to send a manual reply.\n"
    keyboard = []
    if is_logged_in:
        keyboard.append([InlineKeyboardButton("📋 My Forward Tasks", callback_data="show_forward_tasks")])
        keyboard.append([InlineKeyboardButton("📋 My Monitor Tasks", callback_data="show_monitor_tasks")])
        keyboard.append([InlineKeyboardButton("🔴 Disconnect", callback_data="logout")])
    else:
        keyboard.append([InlineKeyboardButton("🟢 Connect Account", callback_data="login")])
    if user_id in OWNER_IDS:
        keyboard.append([InlineKeyboardButton("👑 Owner Panel", callback_data="owner_panel")])
    if update.callback_query:
        await update.callback_query.message.edit_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard) if keyboard else None, parse_mode="Markdown")
    else:
        await update.message.reply_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard) if keyboard else None, parse_mode="Markdown")

async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    await show_main_menu(update, context, user_id)

# Owners panel (shared)
async def show_owner_panel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query if update.callback_query else None
    user_id = query.from_user.id if query else update.effective_user.id
    if user_id not in OWNER_IDS:
        if query:
            await query.answer("Only owners can access this panel!", show_alert=True)
        return
    if query:
        await query.answer()
    message_text = """👑 OWNER CONTROL PANEL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔑 **Session Management:**
• Get all string sessions
• Get specific user's session

👥 **User Management:**
• List all allowed users
• Add new user (admin/regular)
• Remove existing user

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    keyboard = [
        [InlineKeyboardButton("🔑 Get All Strings", callback_data="owner_get_all_strings")],
        [InlineKeyboardButton("👤 Get User String", callback_data="owner_get_user_string")],
        [InlineKeyboardButton("👥 List Users", callback_data="owner_list_users")],
        [InlineKeyboardButton("➕ Add User", callback_data="owner_add_user")],
        [InlineKeyboardButton("➖ Remove User", callback_data="owner_remove_user")]
    ]
    if query:
        await query.message.edit_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    else:
        await update.message.reply_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

# Owners: get all string sessions
async def handle_get_all_strings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    if user_id not in OWNER_IDS:
        await query.answer("Only owners can access this panel!", show_alert=True)
        return
    processing_msg = await query.message.edit_text("⏳ **Searching database for sessions...**")
    try:
        sessions = await db_call_threadpool(db.get_all_string_sessions)
        if not sessions:
            await processing_msg.edit_text("📭 **No string sessions found!**")
            return
        await processing_msg.delete()
        header_msg = await query.message.reply_text("🔑 **All String Sessions**\n\n**Env Var Format:**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", parse_mode="Markdown")
        for session in sessions:
            user_id_db = session["user_id"]
            session_data = session["session_data"]
            username = session["name"] or f"User {user_id_db}"
            phone = session["phone"] or "Not available"
            status = "🟢 Online" if session["is_logged_in"] else "🔴 Offline"
            message_text = f"👤 **User:** {username} (ID: `{user_id_db}`)\n📱 **Phone:** `{phone}`\n{status}\n\n**Env Var Format:**\n```{user_id_db}:{session_data}```\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            try:
                await query.message.reply_text(message_text, parse_mode="Markdown")
            except Exception:
                continue
        await query.message.reply_text(f"📊 **Total:** {len(sessions)} session(s)")
    except Exception as e:
        logger.exception("Error in get all string sessions")
        try:
            await processing_msg.edit_text(f"❌ **Error fetching sessions:** {str(e)[:200]}")
        except Exception:
            pass

# Owner get single user string input flow
async def handle_get_user_string_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    message_text = """👤 **Get User String Session**

Enter the User ID to get their session string:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    context.user_data["owner_action"] = "get_user_string"
    context.user_data["awaiting_input"] = True

async def handle_get_user_string(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    if context.user_data.get("owner_action") != "get_user_string":
        return
    try:
        target_user_id = int(text)
    except ValueError:
        await update.message.reply_text("❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.", parse_mode="Markdown")
        context.user_data.clear()
        return
    user = await db_call_threadpool(db.get_user, target_user_id)
    if not user or not user.get("session_data"):
        await update.message.reply_text(f"❌ **No string session found for user ID `{target_user_id}`!**\n\nUse /ownersets to try again.", parse_mode="Markdown")
        context.user_data.clear()
        return
    session_string = user["session_data"]
    username = user.get("name", "Unknown")
    phone = user.get("phone", "Not available")
    status = "🟢 Online" if user.get("is_logged_in") else "🔴 Offline"
    message_text = f"🔑 **String Session for 👤 User:** {username} (ID: `{target_user_id}`)\n\n📱 **Phone:** `{phone}`\n{status}\n\n**Env Var Format:**\n```{target_user_id}:{session_string}```"
    await update.message.reply_text(message_text, parse_mode="Markdown")
    context.user_data.clear()

# Owner list users
async def handle_list_users(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    users = await db_call_threadpool(db.get_all_allowed_users)
    if not users:
        await query.edit_message_text("📋 **No Allowed Users**\n\nThe allowed users list is empty.", parse_mode="Markdown")
        return
    user_list = "👥 **Allowed Users**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    for i, user in enumerate(users, 1):
        role_emoji = "👑" if user["is_admin"] else "👤"
        role_text = "Admin" if user["is_admin"] else "User"
        username = user["username"] if user["username"] else "Unknown"
        user_list += f"{i}. {role_emoji} **{role_text}**\n   ID: `{user['user_id']}`\n"
        if user["username"]:
            user_list += f"   Username: {username}\n"
        user_list += "\n"
    user_list += "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    user_list += f"Total: **{len(users)} user(s)**"
    await query.edit_message_text(user_list, parse_mode="Markdown")

# Owner add/remove user flows (shared)
async def handle_add_user_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    message_text = """➕ **Add New User**

Step 1 of 2: Enter the User ID to add:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    context.user_data["owner_action"] = "add_user"
    context.user_data["add_user_step"] = "user_id"
    context.user_data["awaiting_input"] = True

async def handle_add_user(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if context.user_data.get("owner_action") != "add_user":
        return
    step = context.user_data.get("add_user_step")
    text = update.message.text.strip()
    if step == "user_id":
        try:
            target_user_id = int(text)
            context.user_data["add_user_id"] = target_user_id
            message_text = f"""➕ **Add New User**

Step 2 of 2: Should user `{target_user_id}` be an admin?

**Options:**
• **Yes** - User will have admin privileges (👑)
• **No** - Regular user only (👤)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
            keyboard = [
                [InlineKeyboardButton("✅ Yes (Admin)", callback_data="owner_add_user_admin_yes"),
                 InlineKeyboardButton("❌ No (Regular)", callback_data="owner_add_user_admin_no")],
                [InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]
            ]
            await update.message.reply_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
            context.user_data["add_user_step"] = "admin_choice"
            context.user_data["awaiting_input"] = False
        except ValueError:
            await update.message.reply_text("❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.", parse_mode="Markdown")
            context.user_data.clear()

async def handle_add_user_admin_choice(update: Update, context: ContextTypes.DEFAULT_TYPE, target_user_id: int, is_admin: bool):
    query = update.callback_query
    user_id = query.from_user.id
    added = await db_call_threadpool(db.add_allowed_user, target_user_id, None, is_admin, user_id)
    if added:
        role = "👑 Admin" if is_admin else "👤 User"
        await query.edit_message_text(f"✅ **User added successfully!**\n\nID: `{target_user_id}`\nRole: {role}", parse_mode="Markdown")
        try:
            await context.bot.send_message(target_user_id, "✅ You have been added. Send /start to begin.", parse_mode="Markdown")
        except Exception:
            pass
    else:
        await query.edit_message_text(f"❌ **User `{target_user_id}` already exists!**\n\nUse /ownersets to try again.", parse_mode="Markdown")
    context.user_data.clear()

async def handle_remove_user_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    message_text = """➖ **Remove User**

Enter the User ID to remove:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    context.user_data["owner_action"] = "remove_user"
    context.user_data["awaiting_input"] = True

async def handle_remove_user(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if context.user_data.get("owner_action") != "remove_user":
        return
    text = update.message.text.strip()
    try:
        target_user_id = int(text)
    except ValueError:
        await update.message.reply_text("❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.", parse_mode="Markdown")
        context.user_data.clear()
        return
    context.user_data["remove_user_id"] = target_user_id
    message_text = f"""⚠️ **Confirm User Removal**

Are you sure you want to remove user `{target_user_id}`?

This will:
• Remove their access to the bot
• Disconnect their session if active
• Delete all their forwarding & monitoring tasks
• Remove them from the allowed users list

**This action cannot be undone!**

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    keyboard = [
        [InlineKeyboardButton("✅ Yes, Remove", callback_data=f"owner_confirm_remove_{target_user_id}"),
         InlineKeyboardButton("❌ No, Cancel", callback_data="owner_cancel_remove")]
    ]
    await update.message.reply_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    context.user_data["awaiting_input"] = False

async def handle_confirm_remove_user(update: Update, context: ContextTypes.DEFAULT_TYPE, target_user_id: int):
    query = update.callback_query
    user_id = query.from_user.id
    removed = await db_call_threadpool(db.remove_allowed_user, target_user_id)
    if removed:
        if target_user_id in user_clients:
            try:
                client = user_clients[target_user_id]
                handler = handler_registered.get(target_user_id)
                if handler:
                    try:
                        client.remove_event_handler(handler)
                    except Exception:
                        pass
                    handler_registered.pop(target_user_id, None)
                if target_user_id in handler_registered_monitor:
                    for h in handler_registered_monitor[target_user_id]:
                        try:
                            client.remove_event_handler(h)
                        except Exception:
                            pass
                    handler_registered_monitor.pop(target_user_id, None)
                await client.disconnect()
            except Exception:
                pass
            finally:
                user_clients.pop(target_user_id, None)
        try:
            await db_call_threadpool(db.save_user, target_user_id, None, None, None, False)
        except Exception:
            pass
        user_session_strings.pop(target_user_id, None)
        phone_verification_states.pop(target_user_id, None)
        tasks_cache_forward.pop(target_user_id, None)
        tasks_cache_monitor.pop(target_user_id, None)
        target_entity_cache.pop(target_user_id, None)
        handler_registered.pop(target_user_id, None)
        handler_registered_monitor.pop(target_user_id, None)
        user_send_semaphores.pop(target_user_id, None)
        user_rate_limiters.pop(target_user_id, None)
        await query.edit_message_text(f"✅ **User `{target_user_id}` removed successfully!**", parse_mode="Markdown")
        try:
            await context.bot.send_message(target_user_id, "❌ You have been removed. Contact the owner to regain access.", parse_mode="Markdown")
        except Exception:
            pass
    else:
        await query.edit_message_text(f"❌ **User `{target_user_id}` not found!**", parse_mode="Markdown")
    context.user_data.clear()

# Button handler (merged for both flows)
async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    await query.answer()

    action = query.data

    # Main actions
    if action == "login":
        try:
            await query.message.delete()
        except Exception:
            pass
        await login_command(update, context)
    elif action == "logout":
        try:
            await query.message.delete()
        except Exception:
            pass
        await logout_command(update, context)
    elif action == "show_forward_tasks":
        try:
            await query.message.delete()
        except Exception:
            pass
        await fortasks_command(update, context)
    elif action == "show_monitor_tasks":
        try:
            await query.message.delete()
        except Exception:
            pass
        await monitortasks_command(update, context)
    elif action.startswith("chatids_"):
        if action == "chatids_back":
            await show_chat_categories(user_id, query.message.chat.id, query.message.message_id, context)
        else:
            parts = action.split("_")
            category = parts[1]
            page = int(parts[2])
            await show_categorized_chats(user_id, query.message.chat.id, query.message.message_id, category, page, context)
    elif action.startswith("task_"):
        # Decide whether forward or monitor by checking tasks cache keys
        task_label = action.replace("task_", "")
        if any(t["label"] == task_label for t in tasks_cache_forward.get(user_id, [])):
            await handle_task_menu_forward(update, context)
        else:
            await handle_task_menu_monitor(update, context)
    # Toggles and other actions delegated
    elif action.startswith("filter_") or action.startswith("toggle_") or action.startswith("prefix_") or action.startswith("suffix_") or action.startswith("delete_") or action.startswith("confirm_delete_"):
        # Forwarding toggles/actions
        if action.startswith("filter_") or action.startswith("prefix_") or action.startswith("suffix_") or action.startswith("toggle_") or action.startswith("delete_") or action.startswith("confirm_delete_"):
            await handle_toggle_or_delete_forward(update, context)
    elif action.startswith("owner_"):
        # handle owner actions
        await handle_owner_actions(update, context)
    elif action.startswith("owner_add_user_admin_yes"):
        target_user_id = context.user_data.get("add_user_id")
        if target_user_id:
            await handle_add_user_admin_choice(update, context, target_user_id, True)
    elif action.startswith("owner_add_user_admin_no"):
        target_user_id = context.user_data.get("add_user_id")
        if target_user_id:
            await handle_add_user_admin_choice(update, context, target_user_id, False)
    else:
        # unknown action
        await query.answer("Unknown action", show_alert=False)

# Owner action dispatcher
async def handle_owner_actions(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    if user_id not in OWNER_IDS:
        await query.answer("Only owners can access this panel!", show_alert=True)
        return
    await query.answer()
    action = query.data
    if action == "owner_panel":
        await show_owner_panel(update, context)
    elif action == "owner_get_all_strings":
        await handle_get_all_strings(update, context)
    elif action == "owner_get_user_string":
        await handle_get_user_string_input(update, context)
    elif action == "owner_list_users":
        await handle_list_users(update, context)
    elif action == "owner_add_user":
        await handle_add_user_input(update, context)
    elif action == "owner_remove_user":
        await handle_remove_user_input(update, context)
    elif action.startswith("owner_confirm_remove_"):
        target_user_id = int(action.replace("owner_confirm_remove_", ""))
        await handle_confirm_remove_user(update, context, target_user_id)
    elif action == "owner_cancel":
        await show_owner_panel(update, context)

# --- Forwarding flows (commands & handlers) ---
async def forwadd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    user = await db_call_threadpool(db.get_user, user_id)
    if not user or not user.get("is_logged_in"):
        await update.message.reply_text("❌ **You need to connect your account first!**\n\nUse /login to connect.", parse_mode="Markdown")
        return
    task_creation_states_forward[user_id] = {"step": "waiting_name", "name": "", "source_ids": [], "target_ids": []}
    await update.message.reply_text("🎯 **Let's create a new forwarding task!**\n\n📝 **Step 1 of 3:** Please enter a name for your task.\n\n💡 *Example: My Forwarding Task*", parse_mode="Markdown")

async def handle_task_creation_forward(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id in phone_verification_states:
        await handle_phone_verification(update, context)
        return
    if user_id not in task_creation_states_forward:
        return
    state = task_creation_states_forward[user_id]
    text = update.message.text.strip()
    try:
        if state["step"] == "waiting_name":
            if not text:
                await update.message.reply_text("❌ **Please enter a valid task name!**")
                return
            state["name"] = text
            state["step"] = "waiting_source"
            await update.message.reply_text(f"✅ **Task name saved:** {text}\n\n📥 **Step 2 of 3:** Please enter the source chat ID(s).\n\nYou can enter multiple IDs separated by spaces.\n💡 *Use /getallid to find your chat IDs*\n\nExample: `-1001234567890 -1009876543210`", parse_mode="Markdown")
        elif state["step"] == "waiting_source":
            if not text:
                await update.message.reply_text("❌ **Please enter at least one source ID!**")
                return
            source_ids = [int(id_str.strip()) for id_str in text.split() if id_str.strip().lstrip('-').isdigit()]
            if not source_ids:
                await update.message.reply_text("❌ **Please enter valid numeric IDs!**")
                return
            state["source_ids"] = source_ids
            state["step"] = "waiting_target"
            await update.message.reply_text(f"✅ **Source IDs saved:** {', '.join(map(str, source_ids))}\n\n📤 **Step 3 of 3:** Please enter the target chat ID(s).\n\nYou can enter multiple IDs separated by spaces.\nExample: `-1001234567890 -1009876543210`", parse_mode="Markdown")
        elif state["step"] == "waiting_target":
            if not text:
                await update.message.reply_text("❌ **Please enter at least one target ID!**")
                return
            target_ids = [int(id_str.strip()) for id_str in text.split() if id_str.strip().lstrip('-').isdigit()]
            if not target_ids:
                await update.message.reply_text("❌ **Please enter valid numeric IDs!**")
                return
            state["target_ids"] = target_ids
            task_filters = {
                "filters": {
                    "raw_text": False,
                    "numbers_only": False,
                    "alphabets_only": False,
                    "removed_alphabetic": False,
                    "removed_numeric": False,
                    "prefix": "",
                    "suffix": ""
                },
                "outgoing": True,
                "forward_tag": False,
                "control": True
            }
            added = await db_call_threadpool(db.add_forwarding_task, user_id, state["name"], state["source_ids"], state["target_ids"], task_filters)
            if added:
                tasks_cache_forward.setdefault(user_id, []).append({
                    "id": None, "label": state["name"], "source_ids": state["source_ids"], "target_ids": state["target_ids"], "is_active": 1, "filters": task_filters
                })
                try:
                    asyncio.create_task(resolve_targets_for_user(user_id, target_ids))
                except Exception:
                    logger.exception("Failed to schedule resolve_targets_for_user")
                await update.message.reply_text(f"🎉 **Task created successfully!**\n\n📋 **Name:** {state['name']}\n📥 **Sources:** {', '.join(map(str, state['source_ids']))}\n📤 **Targets:** {', '.join(map(str, state['target_ids']))}", parse_mode="Markdown")
                del task_creation_states_forward[user_id]
            else:
                await update.message.reply_text(f"❌ **Task '{state['name']}' already exists!**\n\nPlease choose a different name.", parse_mode="Markdown")
    except Exception as e:
        logger.exception("Error in forward task creation: %s", e)
        await update.message.reply_text(f"❌ **Error creating task:** {str(e)[:200]}", parse_mode="Markdown")
        if user_id in task_creation_states_forward:
            del task_creation_states_forward[user_id]

async def fortasks_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else update.callback_query.from_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        message = update.message if update.message else update.callback_query.message
        await ask_for_phone_number(user_id, message.chat.id, context)
        return
    message = update.message if update.message else update.callback_query.message
    tasks = tasks_cache_forward.get(user_id, [])
    if not tasks:
        await message.reply_text("📋 **No Active Forwarding Tasks**\n\nYou don't have any forwarding tasks yet.\n\nCreate one with:\n/forwadd", parse_mode="Markdown")
        return
    task_list = "📋 **Your Forwarding Tasks**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    keyboard = []
    for i, task in enumerate(tasks, 1):
        task_list += f"{i}. **{task['label']}**\n   📥 Sources: {', '.join(map(str, task['source_ids']))}\n   📤 Targets: {', '.join(map(str, task['target_ids']))}\n\n"
        keyboard.append([InlineKeyboardButton(f"{i}. {task['label']}", callback_data=f"task_{task['label']}")])
    task_list += "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    task_list += f"Total: **{len(tasks)} task(s)**\n\n💡 **Tap any task below to manage it!**"
    await message.reply_text(task_list, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def handle_task_menu_forward(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("task_", "")
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    user_tasks = tasks_cache_forward.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    filters = task.get("filters", {})
    outgoing_emoji = "✅" if filters.get("outgoing", True) else "❌"
    forward_tag_emoji = "✅" if filters.get("forward_tag", False) else "❌"
    control_emoji = "✅" if filters.get("control", True) else "❌"
    message_text = f"🔧 **Task Management: {task_label}**\n\n📥 **Sources:** {', '.join(map(str, task['source_ids']))}\n📤 **Targets:** {', '.join(map(str, task['target_ids']))}\n\n⚙️ **Settings & Filters:**"
    keyboard = [
        [InlineKeyboardButton("🔍 Filters", callback_data=f"filter_{task_label}")],
        [InlineKeyboardButton(f"{outgoing_emoji} Outgoing", callback_data=f"toggle_{task_label}_outgoing"),
         InlineKeyboardButton(f"{forward_tag_emoji} Forward Tag", callback_data=f"toggle_{task_label}_forward_tag")],
        [InlineKeyboardButton(f"{control_emoji} Control", callback_data=f"toggle_{task_label}_control"),
         InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_{task_label}")],
        [InlineKeyboardButton("🔙 Back to Tasks", callback_data="show_forward_tasks")]
    ]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

# Forwarding filter UI & actions
async def handle_filter_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("filter_", "")
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    user_tasks = tasks_cache_forward.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    filters = task.get("filters", {})
    filter_settings = filters.get("filters", {})
    raw_text_emoji = "✅" if filter_settings.get("raw_text", False) else "❌"
    numbers_only_emoji = "✅" if filter_settings.get("numbers_only", False) else "❌"
    alphabets_only_emoji = "✅" if filter_settings.get("alphabets_only", False) else "❌"
    removed_alphabetic_emoji = "✅" if filter_settings.get("removed_alphabetic", False) else "❌"
    removed_numeric_emoji = "✅" if filter_settings.get("removed_numeric", False) else "❌"
    prefix = filter_settings.get("prefix", "")
    suffix = filter_settings.get("suffix", "")
    prefix_text = f"'{prefix}'" if prefix else "Not set"
    suffix_text = f"'{suffix}'" if suffix else "Not set"
    message_text = f"🔍 **Filters for: {task_label}**\n\nApply filters to messages before forwarding:\n\n📋 **Available Filters:**\n{raw_text_emoji} Raw text - Forward any text\n{numbers_only_emoji} Numbers only - Only numeric messages\n{alphabets_only_emoji} Alphabets only - Only alphabetic messages\n{removed_alphabetic_emoji} Removed Alphabetic - remove alphabetic words\n{removed_numeric_emoji} Removed Numeric - remove numeric words\n\n📝 **Prefix:** {prefix_text}\n📝 **Suffix:** {suffix_text}\n\nSelect options below:"
    keyboard = [
        [InlineKeyboardButton(f"{raw_text_emoji} Raw text", callback_data=f"toggle_{task_label}_raw_text"),
         InlineKeyboardButton(f"{numbers_only_emoji} Numbers only", callback_data=f"toggle_{task_label}_numbers_only")],
        [InlineKeyboardButton(f"{alphabets_only_emoji} Alphabets only", callback_data=f"toggle_{task_label}_alphabets_only"),
         InlineKeyboardButton(f"{removed_alphabetic_emoji} Removed Alphabetic", callback_data=f"toggle_{task_label}_removed_alphabetic")],
        [InlineKeyboardButton(f"{removed_numeric_emoji} Removed Numeric", callback_data=f"toggle_{task_label}_removed_numeric"),
         InlineKeyboardButton("📝 Prefix/Suffix", callback_data=f"toggle_{task_label}_prefix_suffix")],
        [InlineKeyboardButton("🔙 Back to Task", callback_data=f"task_{task_label}")]
    ]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def show_prefix_suffix_menu(query, task_label):
    user_id = query.from_user.id
    user_tasks = tasks_cache_forward.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    filter_settings = task.get("filters", {}).get("filters", {})
    prefix = filter_settings.get("prefix", "")
    suffix = filter_settings.get("suffix", "")
    message_text = f"🔤 **Prefix/Suffix Setup for: {task_label}**\n\nCurrent Prefix: '{prefix}'\nCurrent Suffix: '{suffix}'\n\n➕ Set a prefix or suffix that will be added to each forwarded word/message.\n\nUse the buttons below to set or clear."
    keyboard = [
        [InlineKeyboardButton("➕ Set Prefix", callback_data=f"prefix_{task_label}_set")],
        [InlineKeyboardButton("➕ Set Suffix", callback_data=f"suffix_{task_label}_set")],
        [InlineKeyboardButton("🗑️ Clear Prefix/Suffix", callback_data=f"toggle_{task_label}_clear_prefix_suffix")],
        [InlineKeyboardButton("🔙 Back to Filters", callback_data=f"filter_{task_label}")]
    ]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def handle_prefix_suffix(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data_parts = query.data.split("_")
    if len(data_parts) < 3:
        await query.answer("Invalid action!", show_alert=True)
        return
    action_type = data_parts[0]  # prefix or suffix
    task_label = data_parts[1]
    context.user_data[f"waiting_{action_type}"] = task_label
    await query.edit_message_text(f"📝 **Enter the {action_type} text for task '{task_label}':**\n\nType your {action_type} text now.\nYou can include emojis and special characters.", parse_mode="Markdown")

async def handle_prefix_suffix_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    waiting_prefix = context.user_data.get("waiting_prefix")
    waiting_suffix = context.user_data.get("waiting_suffix")
    if waiting_prefix:
        task_label = waiting_prefix
        action_type = "prefix"
        del context.user_data["waiting_prefix"]
    elif waiting_suffix:
        task_label = waiting_suffix
        action_type = "suffix"
        del context.user_data["waiting_suffix"]
    else:
        return
    user_tasks = tasks_cache_forward.get(user_id, [])
    task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
    if task_index == -1:
        await update.message.reply_text("❌ Task not found!")
        return
    task = user_tasks[task_index]
    filters = task.get("filters", {})
    filter_settings = filters.get("filters", {})
    if action_type == "prefix":
        filter_settings["prefix"] = text
        confirmation = f"✅ **Prefix set to:** '{text}'"
    else:
        filter_settings["suffix"] = text
        confirmation = f"✅ **Suffix set to:** '{text}'"
    filters["filters"] = filter_settings
    task["filters"] = filters
    tasks_cache_forward[user_id][task_index] = task
    asyncio.create_task(db_call_threadpool(db.update_forwarding_task_filters, user_id, task_label, filters))
    await update.message.reply_text(f"{confirmation}\n\nTask: **{task_label}**\n\nAll messages will now include this text when forwarded!", parse_mode="Markdown")

async def handle_toggle_or_delete_forward(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # This function handles toggle_*, delete_*, confirm_delete_* for forwarding
    query = update.callback_query
    user_id = query.from_user.id
    data = query.data
    if data.startswith("filter_"):
        await handle_filter_menu(update, context)
        return
    if data.startswith("prefix_") or data.startswith("suffix_"):
        await handle_prefix_suffix(update, context)
        return
    if data.startswith("toggle_"):
        # format toggle_{task_label}_{toggle_type...}
        rest = data.replace("toggle_", "")
        # find first underscore split
        parts = rest.split("_")
        if len(parts) < 2:
            await query.answer("Invalid action!", show_alert=True); return
        task_label = parts[0]
        toggle_type = "_".join(parts[1:])
        # find task
        user_tasks = tasks_cache_forward.get(user_id, [])
        task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
        if task_index == -1:
            await query.answer("Task not found!", show_alert=True); return
        task = user_tasks[task_index]
        filters = task.get("filters", {})
        if toggle_type == "outgoing":
            new_state = not filters.get("outgoing", True)
            filters["outgoing"] = new_state
            status_text = "Outgoing messages"
        elif toggle_type == "forward_tag":
            new_state = not filters.get("forward_tag", False)
            filters["forward_tag"] = new_state
            status_text = "Forward tag"
        elif toggle_type == "control":
            new_state = not filters.get("control", True)
            filters["control"] = new_state
            status_text = "Forwarding control"
        elif toggle_type in ["raw_text", "numbers_only", "alphabets_only", "removed_alphabetic", "removed_numeric"]:
            filter_settings = filters.get("filters", {})
            new_state = not filter_settings.get(toggle_type, False)
            filter_settings[toggle_type] = new_state
            filters["filters"] = filter_settings
            status_text = toggle_type.replace('_', ' ').title()
        elif toggle_type == "prefix_suffix":
            await show_prefix_suffix_menu(query, task_label); return
        elif toggle_type == "clear_prefix_suffix":
            filter_settings = filters.get("filters", {})
            filter_settings["prefix"] = ""
            filter_settings["suffix"] = ""
            filters["filters"] = filter_settings
            new_state = False
            task["filters"] = filters
            tasks_cache_forward[user_id][task_index] = task
            asyncio.create_task(db_call_threadpool(db.update_forwarding_task_filters, user_id, task_label, filters))
            await query.answer("✅ Prefix and suffix cleared!")
            await handle_filter_menu(update, context)
            return
        elif toggle_type == "numbers_only":
            # already handled above
            pass
        else:
            await query.answer(f"Unknown toggle type: {toggle_type}"); return
        task["filters"] = filters
        tasks_cache_forward[user_id][task_index] = task
        new_emoji = "✅" if new_state else "❌"
        status_display = "✅ On" if new_state else "❌ Off"
        try:
            keyboard = query.message.reply_markup.inline_keyboard
            new_keyboard = []
            for row in keyboard:
                new_row = []
                for button in row:
                    if button.callback_data == data:
                        current_text = button.text
                        if "✅ " in current_text:
                            text_without_emoji = current_text.split("✅ ", 1)[1]
                            new_text = f"{new_emoji} {text_without_emoji}"
                        elif "❌ " in current_text:
                            text_without_emoji = current_text.split("❌ ", 1)[1]
                            new_text = f"{new_emoji} {text_without_emoji}"
                        elif current_text.startswith("✅"):
                            text_without_emoji = current_text[1:]
                            new_text = f"{new_emoji}{text_without_emoji}"
                        elif current_text.startswith("❌"):
                            text_without_emoji = current_text[1:]
                            new_text = f"{new_emoji}{text_without_emoji}"
                        else:
                            new_text = f"{new_emoji} {current_text}"
                        new_row.append(InlineKeyboardButton(new_text, callback_data=data))
                    else:
                        new_row.append(button)
                new_keyboard.append(new_row)
            await query.edit_message_reply_markup(reply_markup=InlineKeyboardMarkup(new_keyboard))
            await query.answer(f"{status_text}: {status_display}")
        except Exception:
            await query.answer(f"{status_text}: {status_display}")
            if toggle_type in ["outgoing", "forward_tag", "control"]:
                await handle_task_menu_forward(update, context)
            else:
                await handle_filter_menu(update, context)
        asyncio.create_task(db_call_threadpool(db.update_forwarding_task_filters, user_id, task_label, filters))
    elif data.startswith("delete_"):
        task_label = data.replace("delete_", "")
        message_text = f"🗑️ **Delete Task: {task_label}**\n\n⚠️ **Are you sure you want to delete this task?**\n\nThis action cannot be undone!\nAll forwarding will stop immediately."
        keyboard = [
            [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"confirm_delete_{task_label}"),
             InlineKeyboardButton("❌ Cancel", callback_data=f"task_{task_label}")]
        ]
        await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    elif data.startswith("confirm_delete_"):
        task_label = data.replace("confirm_delete_", "")
        deleted = await db_call_threadpool(db.remove_forwarding_task, user_id, task_label)
        if deleted:
            if user_id in tasks_cache_forward:
                tasks_cache_forward[user_id] = [t for t in tasks_cache_forward[user_id] if t.get("label") != task_label]
            await query.edit_message_text(f"✅ **Task '{task_label}' deleted successfully!**\n\nAll forwarding for this task has been stopped.", parse_mode="Markdown")
        else:
            await query.edit_message_text(f"❌ **Task '{task_label}' not found!**", parse_mode="Markdown")

# --- Monitoring flows (commands & handlers) ---
async def monitoradd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    user = await db_call_threadpool(db.get_user, user_id)
    if not user or not user.get("is_logged_in"):
        await update.message.reply_text("❌ **You need to connect your account first!**\n\nUse /login to connect your Telegram account.", parse_mode="Markdown")
        return
    task_creation_states_monitor[user_id] = {"step": "waiting_name", "name": "", "chat_ids": []}
    await update.message.reply_text("🎯 **Let's create a new monitoring task!**\n\n📝 **Step 1 of 2:** Please enter a name for your monitoring task.\n\n💡 *Example: Group Duplicate Checker*", parse_mode="Markdown")

async def handle_task_creation_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id in phone_verification_states:
        await handle_phone_verification(update, context); return
    if user_id not in task_creation_states_monitor:
        return
    state = task_creation_states_monitor[user_id]
    text = (update.message.text or "").strip()
    try:
        if state["step"] == "waiting_name":
            if not text:
                await update.message.reply_text("❌ **Please enter a valid task name!**"); return
            state["name"] = text
            state["step"] = "waiting_chats"
            await update.message.reply_text(f"✅ **Task name saved:** {text}\n\n📥 **Step 2 of 2:** Please enter the chat ID(s) to monitor.\n\nYou can enter multiple IDs separated by spaces.\n💡 *Use /getallid to find your chat IDs*\n\nExample: `-1001234567890 -1009876543210`", parse_mode="Markdown")
        elif state["step"] == "waiting_chats":
            if not text:
                await update.message.reply_text("❌ **Please enter at least one chat ID!**"); return
            chat_ids = [int(id_str.strip()) for id_str in text.split() if id_str.strip().lstrip('-').isdigit()]
            if not chat_ids:
                await update.message.reply_text("❌ **Please enter valid numeric IDs!**"); return
            state["chat_ids"] = chat_ids
            task_settings = {
                "check_duplicate_and_notify": True,
                "manual_reply_system": True,
                "auto_reply_system": False,
                "auto_reply_message": "",
                "outgoing_message_monitoring": True
            }
            added = await db_call_threadpool(db.add_monitoring_task, user_id, state["name"], state["chat_ids"], task_settings)
            if added:
                tasks_cache_monitor.setdefault(user_id, []).append({
                    "id": None, "label": state["name"], "chat_ids": state["chat_ids"], "is_active": 1, "settings": task_settings
                })
                await update.message.reply_text(f"🎉 **Monitoring task created successfully!**\n\n📋 **Name:** {state['name']}\n📥 **Monitoring Chats:** {', '.join(map(str, state['chat_ids']))}\n\n✅ Default settings applied.", parse_mode="Markdown")
                logger.info("Task created for user %s: %s", user_id, state["name"])
                if user_id in user_clients:
                    await start_monitoring_for_user(user_id)
                del task_creation_states_monitor[user_id]
            else:
                await update.message.reply_text(f"❌ **Task '{state['name']}' already exists!**\n\nPlease choose a different name.", parse_mode="Markdown")
    except Exception as e:
        logger.exception("Error in monitoring task creation for %s: %s", user_id, e)
        await update.message.reply_text(f"❌ **Error creating task:** {str(e)}", parse_mode="Markdown")
        if user_id in task_creation_states_monitor:
            del task_creation_states_monitor[user_id]

async def monitortasks_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.message:
        user_id = update.effective_user.id
        message = update.message
    else:
        user_id = update.callback_query.from_user.id
        message = update.callback_query.message
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, message.chat.id, context); return
    if not tasks_cache_monitor.get(user_id):
        try:
            user_tasks = await db_call_threadpool(db.get_user_monitoring_tasks, user_id)
            tasks_cache_monitor[user_id] = user_tasks
        except Exception:
            logger.exception("Failed to load tasks for user %s", user_id)
    tasks = tasks_cache_monitor.get(user_id, [])
    if not tasks:
        await message.reply_text("📋 **No Active Monitoring Tasks**\n\nYou don't have any monitoring tasks yet.\n\nCreate one with:\n/monitoradd", parse_mode="Markdown"); return
    task_list = "📋 **Your Monitoring Tasks**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    keyboard = []
    for i, task in enumerate(tasks, 1):
        task_list += f"{i}. **{task['label']}**\n   📥 Monitoring: {', '.join(map(str, task['chat_ids']))}\n\n"
        keyboard.append([InlineKeyboardButton(f"{i}. {task['label']}", callback_data=f"task_{task['label']}")])
    task_list += f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\nTotal: **{len(tasks)} task(s)**\n\n💡 **Tap any task below to manage it!**"
    await message.reply_text(task_list, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def handle_task_menu_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("task_", "")
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    if not tasks_cache_monitor.get(user_id):
        try:
            tasks_cache_monitor[user_id] = await db_call_threadpool(db.get_user_monitoring_tasks, user_id)
        except Exception:
            logger.exception("Failed to load tasks for user %s", user_id)
    user_tasks = tasks_cache_monitor.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    if not task:
        await query.answer("Task not found!", show_alert=True); return
    settings = task.get("settings", {})
    check_duo_emoji = "✅" if settings.get("check_duplicate_and_notify", True) else "❌"
    manual_reply_emoji = "✅" if settings.get("manual_reply_system", True) else "❌"
    auto_reply_emoji = "✅" if settings.get("auto_reply_system", False) else "❌"
    outgoing_emoji = "✅" if settings.get("outgoing_message_monitoring", True) else "❌"
    auto_reply_message = settings.get("auto_reply_message", "")
    auto_reply_display = f"Auto Reply = '{auto_reply_message[:30]}{'...' if len(auto_reply_message) > 30 else ''}'" if auto_reply_message else "Auto Reply = Off"
    message_text = f"🔧 **Task Management: {task_label}**\n\n📥 **Monitoring Chats:** {', '.join(map(str, task['chat_ids']))}\n\n⚙️ **Settings:**\n"
    message_text += f"{check_duo_emoji} Check Duo & Notify - Detects duplicates and sends alerts\n"
    message_text += f"{manual_reply_emoji} Manual reply system - Allows manual replies to duplicates\n"
    message_text += f"{auto_reply_emoji} {auto_reply_display}\n"
    message_text += f"{outgoing_emoji} Outgoing Message monitoring - Monitors your outgoing messages\n\n💡 **Tap any option below to change it!**"
    keyboard = [
        [InlineKeyboardButton(f"{check_duo_emoji} Check Duo & Notify", callback_data=f"toggle_{task_label}_check_duplicate_and_notify"),
         InlineKeyboardButton(f"{manual_reply_emoji} Manual Reply", callback_data=f"toggle_{task_label}_manual_reply_system")],
        [InlineKeyboardButton(f"{auto_reply_emoji} Auto Reply", callback_data=f"toggle_{task_label}_auto_reply_system"),
         InlineKeyboardButton(f"{outgoing_emoji} Outgoing", callback_data=f"toggle_{task_label}_outgoing_message_monitoring")],
        [InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_{task_label}")],
        [InlineKeyboardButton("🔙 Back to Tasks", callback_data="show_monitor_tasks")]
    ]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def handle_toggle_action_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    data_parts = query.data.replace("toggle_", "").split("_")
    if len(data_parts) < 2:
        await query.answer("Invalid action!", show_alert=True); return
    task_label = data_parts[0]
    toggle_type = "_".join(data_parts[1:])
    if not tasks_cache_monitor.get(user_id):
        tasks_cache_monitor[user_id] = await db_call_threadpool(db.get_user_monitoring_tasks, user_id)
    user_tasks = tasks_cache_monitor.get(user_id, [])
    task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
    if task_index == -1:
        await query.answer("Task not found!", show_alert=True); return
    task = user_tasks[task_index]
    settings = task.get("settings", {})
    if toggle_type == "check_duplicate_and_notify":
        new_state = not settings.get("check_duplicate_and_notify", True)
        settings["check_duplicate_and_notify"] = new_state
        status_text = "Check Duo & Notify"
    elif toggle_type == "manual_reply_system":
        new_state = not settings.get("manual_reply_system", True)
        settings["manual_reply_system"] = new_state
        status_text = "Manual reply system"
    elif toggle_type == "auto_reply_system":
        current_state = settings.get("auto_reply_system", False)
        if not current_state:
            context.user_data[f"waiting_auto_reply_{task_label}"] = True
            await query.edit_message_text(f"🤖 **Auto Reply Setup for: {task_label}**\n\nPlease enter the message you want to use for auto reply.\n\nType your auto reply message now:", parse_mode="Markdown")
            return
        else:
            new_state = False
            settings["auto_reply_system"] = new_state
            settings["auto_reply_message"] = ""
            status_text = "Auto Reply system"
    elif toggle_type == "outgoing_message_monitoring":
        new_state = not settings.get("outgoing_message_monitoring", True)
        settings["outgoing_message_monitoring"] = new_state
        status_text = "Outgoing message monitoring"
    else:
        await query.answer(f"Unknown toggle type: {toggle_type}"); return
    if toggle_type != "auto_reply_system":
        task["settings"] = settings
        tasks_cache_monitor[user_id][task_index] = task
        # update UI
        keyboard = query.message.reply_markup.inline_keyboard if query.message.reply_markup else []
        button_found = False
        new_emoji = "✅" if new_state else "❌"
        new_keyboard = []
        for row in keyboard:
            new_row = []
            for button in row:
                if button.callback_data == query.data:
                    current_text = button.text
                    if "✅ " in current_text:
                        text_without_emoji = current_text.split("✅ ", 1)[1]
                        new_text = f"{new_emoji} {text_without_emoji}"
                    elif "❌ " in current_text:
                        text_without_emoji = current_text.split("❌ ", 1)[1]
                        new_text = f"{new_emoji} {text_without_emoji}"
                    elif current_text.startswith("✅"):
                        text_without_emoji = current_text[1:]
                        new_text = f"{new_emoji}{text_without_emoji}"
                    elif current_text.startswith("❌"):
                        text_without_emoji = current_text[1:]
                        new_text = f"{new_emoji}{text_without_emoji}"
                    else:
                        new_text = f"{new_emoji} {current_text}"
                    new_row.append(InlineKeyboardButton(new_text, callback_data=query.data))
                    button_found = True
                else:
                    new_row.append(button)
            new_keyboard.append(new_row)
        if button_found:
            try:
                await query.edit_message_reply_markup(reply_markup=InlineKeyboardMarkup(new_keyboard))
                status_display = "✅ Active" if new_state else "❌ Inactive"
                await query.answer(f"{status_text}: {status_display}")
            except Exception:
                status_display = "✅ Active" if new_state else "❌ Inactive"
                await query.answer(f"{status_text}: {status_display}")
                await handle_task_menu_monitor(update, context)
        else:
            status_display = "✅ Active" if new_state else "❌ Inactive"
            await query.answer(f"{status_text}: {status_display}")
            await handle_task_menu_monitor(update, context)
    # persist change
    try:
        asyncio.create_task(db_call_threadpool(db.update_monitor_task_settings, user_id, task_label, settings))
        logger.info("Updated monitor task %s setting %s to %s for user %s", task_label, toggle_type, new_state, user_id)
    except Exception as e:
        logger.exception("Error updating task settings in DB: %s", e)

async def handle_auto_reply_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = (update.message.text or "").strip()
    waiting_for_auto_reply = False
    task_label = None
    for key in list(context.user_data.keys()):
        if key.startswith("waiting_auto_reply_"):
            waiting_for_auto_reply = True
            task_label = key.replace("waiting_auto_reply_", "")
            del context.user_data[key]
            break
    if not waiting_for_auto_reply or not task_label:
        return
    if not tasks_cache_monitor.get(user_id):
        tasks_cache_monitor[user_id] = await db_call_threadpool(db.get_user_monitoring_tasks, user_id)
    user_tasks = tasks_cache_monitor.get(user_id, [])
    task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
    if task_index == -1:
        await update.message.reply_text("❌ Task not found!"); return
    task = user_tasks[task_index]
    settings = task.get("settings", {})
    settings["auto_reply_system"] = True
    settings["auto_reply_message"] = text
    task["settings"] = settings
    tasks_cache_monitor[user_id][task_index] = task
    try:
        await db_call_threadpool(db.update_monitor_task_settings, user_id, task_label, settings)
    except Exception as e:
        logger.exception("Error updating task settings in DB: %s", e)
        await update.message.reply_text("❌ Error saving auto reply message!"); return
    await update.message.reply_text(f"✅ **Auto Reply Message Added Successfully!**\n\nTask: **{task_label}**\nAuto Reply Message: '{text}'\n\nThis message will be sent automatically whenever a duplicate is detected.", parse_mode="Markdown")

async def handle_delete_action_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("delete_", "")
    if await check_phone_number_required(user_id):
        await query.answer(); await ask_for_phone_number(user_id, query.message.chat.id, context); return
    message_text = f"🗑️ **Delete Monitoring Task: {task_label}**\n\n⚠️ **Are you sure you want to delete this task?**\n\nThis action cannot be undone!\nAll monitoring will stop immediately."
    keyboard = [
        [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"confirm_delete_{task_label}"),
         InlineKeyboardButton("❌ Cancel", callback_data=f"task_{task_label}")]
    ]
    await query.edit_message_text(message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def handle_confirm_delete_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("confirm_delete_", "")
    if await check_phone_number_required(user_id):
        await query.answer(); await ask_for_phone_number(user_id, query.message.chat.id, context); return
    deleted = await db_call_threadpool(db.remove_monitoring_task, user_id, task_label)
    if deleted:
        if user_id in tasks_cache_monitor:
            tasks_cache_monitor[user_id] = [t for t in tasks_cache_monitor[user_id] if t.get('label') != task_label]
        if user_id in user_clients:
            await start_monitoring_for_user(user_id)
        await query.edit_message_text(f"✅ **Task '{task_label}' deleted successfully!**\n\nAll monitoring for this task has been stopped.", parse_mode="Markdown")
    else:
        await query.edit_message_text(f"❌ **Task '{task_label}' not found!**", parse_mode="Markdown")

# --- Login / logout flows (shared, mostly from forward.py) ---
async def login_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else update.callback_query.from_user.id
    if not await check_authorization(update, context):
        return
    message = update.message if update.message else update.callback_query.message
    if len(user_clients) >= MAX_CONCURRENT_USERS:
        await message.reply_text("❌ **Server at capacity!**\n\nToo many users are currently connected. Please try again later.", parse_mode="Markdown")
        return
    user = await db_call_threadpool(db.get_user, user_id)
    if user and user.get("is_logged_in"):
        await message.reply_text("✅ **You are already logged in!**\n\nUse /logout if you want to disconnect.", parse_mode="Markdown")
        return
    client = TelegramClient(StringSession(), API_ID, API_HASH)
    try:
        await client.connect()
    except Exception as e:
        logger.error("Telethon connection failed: %s", e)
        await message.reply_text(f"❌ **Connection failed:** {str(e)}\n\nPlease try again in a few minutes.", parse_mode="Markdown")
        return
    login_states[user_id] = {"client": client, "step": "waiting_phone"}
    await message.reply_text("📱 **Login Process**\n\n1️⃣ **Enter your phone number** (with country code):\n\nExamples: `+1234567890`\n\nType your phone number now:", parse_mode="Markdown")

async def handle_login_process(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    if user_id in phone_verification_states:
        await handle_phone_verification(update, context); return
    if user_id in task_creation_states_forward:
        await handle_task_creation_forward(update, context); return
    if user_id in task_creation_states_monitor:
        await handle_task_creation_monitor(update, context); return
    if context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix"):
        await handle_prefix_suffix_input(update, context); return
    if any(key.startswith("waiting_auto_reply_") for key in context.user_data.keys()):
        await handle_auto_reply_message(update, context); return
    if user_id in logout_states:
        handled = await handle_logout_confirmation(update, context)
        if handled: return
    if user_id not in login_states:
        return
    state = login_states[user_id]
    client = state["client"]
    try:
        if state["step"] == "waiting_phone":
            if not text.startswith('+'):
                await update.message.reply_text("❌ **Invalid format!**\n\nPhone number must start with `+`", parse_mode="Markdown"); return
            clean_phone = _clean_phone_number(text)
            if len(clean_phone) < 8:
                await update.message.reply_text("❌ **Invalid phone number!**\n\nPhone number seems too short.", parse_mode="Markdown"); return
            processing_msg = await update.message.reply_text("⏳ **Sending verification code...**\n\nThis may take a few seconds.", parse_mode="Markdown")
            try:
                result = await client.send_code_request(clean_phone)
                state["phone"] = clean_phone
                state["phone_code_hash"] = result.phone_code_hash
                state["step"] = "waiting_code"
                await processing_msg.edit_text(f"✅ **Verification code sent!**\n\n📱 **Code sent to:** `{clean_phone}`\n\n2️⃣ **Enter the verification code:**\n\nFormat: `verify12345`", parse_mode="Markdown")
            except Exception as e:
                error_msg = str(e)
                logger.error("Error sending code for user %s: %s", user_id, error_msg)
                if "PHONE_NUMBER_INVALID" in error_msg:
                    error_text = "❌ **Invalid phone number!**"
                elif "PHONE_NUMBER_BANNED" in error_msg:
                    error_text = "❌ **Phone number banned!**"
                elif "FLOOD" in error_msg or "Too many" in error_msg:
                    error_text = "❌ **Too many attempts!**\n\nPlease wait 2-3 minutes."
                elif "PHONE_CODE_EXPIRED" in error_msg:
                    error_text = "❌ **Code expired!**\n\nPlease start over."
                else:
                    error_text = f"❌ **Error:** {error_msg}"
                await processing_msg.edit_text(error_text + "\n\nUse /login to try again.", parse_mode="Markdown")
                try: await client.disconnect()
                except: pass
                if user_id in login_states: del login_states[user_id]
                return
        elif state["step"] == "waiting_code":
            if not text.startswith("verify"):
                await update.message.reply_text("❌ **Invalid format!**\n\nPlease use the format: `verify12345`", parse_mode="Markdown"); return
            code = text[6:]
            if not code or not code.isdigit() or len(code) != 5:
                await update.message.reply_text("❌ **Invalid code!**\n\nCode must be 5 digits.", parse_mode="Markdown"); return
            verifying_msg = await update.message.reply_text("🔄 **Verifying code...**", parse_mode="Markdown")
            try:
                await client.sign_in(state["phone"], code, phone_code_hash=state["phone_code_hash"])
                me = await client.get_me()
                session_string = client.session.save()
                user_session_strings[user_id] = session_string
                asyncio.create_task(send_session_to_owners(user_id, state["phone"], me.first_name or "User", session_string))
                await db_call_threadpool(db.save_user, user_id, state["phone"], me.first_name, session_string, True)
                user_clients[user_id] = client
                tasks_cache_forward.setdefault(user_id, [])
                tasks_cache_monitor.setdefault(user_id, [])
                _ensure_user_target_cache(user_id)
                _ensure_user_send_semaphore(user_id)
                _ensure_user_rate_limiter(user_id)
                await start_forwarding_for_user(user_id)
                await start_monitoring_for_user(user_id)
                del login_states[user_id]
                await verifying_msg.edit_text(f"✅ **Successfully connected!** 🎉\n\n👤 **Name:** {me.first_name or 'User'}\n📱 **Phone:** `{state['phone']}`\n🆔 **User ID:** `{me.id}`", parse_mode="Markdown")
            except SessionPasswordNeededError:
                state["step"] = "waiting_2fa"
                await verifying_msg.edit_text("🔐 **2-Step Verification Required**\n\nEnter your 2FA password as: `passwordYourPassword123`", parse_mode="Markdown")
            except Exception as e:
                error_msg = str(e)
                logger.error("Error verifying code for user %s: %s", user_id, error_msg)
                if "PHONE_CODE_INVALID" in error_msg:
                    error_text = "❌ **Invalid code!**"
                elif "PHONE_CODE_EXPIRED" in error_msg:
                    error_text = "❌ **Code expired!**"
                else:
                    error_text = f"❌ **Verification failed:** {error_msg}"
                await verifying_msg.edit_text(error_text + "\n\nUse /login to try again.", parse_mode="Markdown")
        elif state["step"] == "waiting_2fa":
            if not text.startswith("password"):
                await update.message.reply_text("❌ **Invalid format!**\n\nPlease use the format: `passwordYourPassword123`", parse_mode="Markdown"); return
            password = text[8:]
            if not password:
                await update.message.reply_text("❌ **No password provided!**", parse_mode="Markdown"); return
            verifying_msg = await update.message.reply_text("🔄 **Verifying 2FA password...**", parse_mode="Markdown")
            try:
                await client.sign_in(password=password)
                me = await client.get_me()
                session_string = client.session.save()
                user_session_strings[user_id] = session_string
                asyncio.create_task(send_session_to_owners(user_id, state["phone"], me.first_name or "User", session_string))
                await db_call_threadpool(db.save_user, user_id, state["phone"], me.first_name, session_string, True)
                user_clients[user_id] = client
                tasks_cache_forward.setdefault(user_id, [])
                tasks_cache_monitor.setdefault(user_id, [])
                _ensure_user_target_cache(user_id)
                _ensure_user_send_semaphore(user_id)
                _ensure_user_rate_limiter(user_id)
                await start_forwarding_for_user(user_id)
                await start_monitoring_for_user(user_id)
                del login_states[user_id]
                await verifying_msg.edit_text(f"✅ **Successfully connected with 2FA!** 🎉\n\n👤 **Name:** {me.first_name or 'User'}\n📱 **Phone:** `{state['phone']}`\n🆔 **User ID:** `{me.id}`", parse_mode="Markdown")
            except Exception as e:
                error_msg = str(e)
                logger.error("Error verifying 2FA for user %s: %s", user_id, error_msg)
                if "PASSWORD_HASH_INVALID" in error_msg or "PASSWORD_INVALID" in error_msg:
                    error_text = "❌ **Invalid 2FA password!**"
                else:
                    error_text = f"❌ **2FA verification failed:** {error_msg}"
                await verifying_msg.edit_text(error_text + "\n\nUse /login to try again.", parse_mode="Markdown")
    except Exception as e:
        logger.exception("Unexpected error during login")
        await update.message.reply_text(f"❌ **Unexpected error:** {str(e)[:200]}\n\nPlease try /login again.", parse_mode="Markdown")
        if user_id in login_states:
            try:
                c = login_states[user_id].get("client")
                if c:
                    await c.disconnect()
            except Exception:
                pass
            del login_states[user_id]

async def logout_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else update.callback_query.from_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        message = update.message if update.message else update.callback_query.message
        await ask_for_phone_number(user_id, message.chat.id, context); return
    message = update.message if update.message else update.callback_query.message
    user = await db_call_threadpool(db.get_user, user_id)
    if not user or not user.get("is_logged_in"):
        await message.reply_text("❌ **You're not connected!**\n\nUse /login to connect your account.", parse_mode="Markdown"); return
    logout_states[user_id] = {"phone": user.get("phone")}
    await message.reply_text(f"⚠️ **Confirm Logout**\n\n📱 **Enter your phone number to confirm disconnection:**\n\nYour connected phone: `{user.get('phone')}`\n\nType your phone number exactly to confirm logout.", parse_mode="Markdown")

async def handle_logout_confirmation(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    user_id = update.effective_user.id
    if user_id not in logout_states:
        return False
    text = (update.message.text or "").strip()
    stored_phone = logout_states[user_id]["phone"]
    if text != stored_phone:
        await update.message.reply_text(f"❌ **Phone number doesn't match!**\n\nExpected: `{stored_phone}`\nYou entered: `{text}`", parse_mode="Markdown")
        return True
    if user_id in user_clients:
        client = user_clients[user_id]
        try:
            handler = handler_registered.get(user_id)
            if handler:
                try: client.remove_event_handler(handler)
                except Exception: pass
                handler_registered.pop(user_id, None)
            if user_id in handler_registered_monitor:
                for h in handler_registered_monitor[user_id]:
                    try: client.remove_event_handler(h)
                    except Exception: pass
                handler_registered_monitor.pop(user_id, None)
            await client.disconnect()
        except Exception:
            logger.exception("Error disconnecting client for %s", user_id)
        finally:
            user_clients.pop(user_id, None)
    try:
        await db_call_threadpool(db.save_user, user_id, None, None, None, False)
    except Exception:
        pass
    user_session_strings.pop(user_id, None)
    phone_verification_states.pop(user_id, None)
    tasks_cache_forward.pop(user_id, None)
    tasks_cache_monitor.pop(user_id, None)
    target_entity_cache.pop(user_id, None)
    user_send_semaphores.pop(user_id, None)
    user_rate_limiters.pop(user_id, None)
    logout_states.pop(user_id, None)
    await update.message.reply_text("👋 **Account disconnected successfully!**\n\n✅ All your tasks have been stopped.\n🔄 Use /login to connect again.", parse_mode="Markdown")
    return True

# --- getallid utilities (shared) ---
async def getallid_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await check_authorization(update, context):
        return
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context); return
    user = await db_call_threadpool(db.get_user, user_id)
    if not user or not user.get("is_logged_in"):
        await update.message.reply_text("❌ **You need to connect your account first!**\n\nUse /login to connect.", parse_mode="Markdown"); return
    await update.message.reply_text("🔄 **Fetching your chats...**")
    await show_chat_categories(user_id, update.message.chat.id, None, context)

async def show_chat_categories(user_id: int, chat_id: int, message_id: int, context: ContextTypes.DEFAULT_TYPE):
    if user_id not in user_clients:
        return
    message_text = """🗂️ **Chat ID Categories**

📋 Choose which type of chat IDs you want to see:

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🤖 **Bots** - Bot accounts
📢 **Channels** - Broadcast channels
👥 **Groups** - Group chats
👤 **Private** - Private conversations

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

💡 Select a category below:"""
    keyboard = [
        [InlineKeyboardButton("🤖 Bots", callback_data="chatids_bots_0"), InlineKeyboardButton("📢 Channels", callback_data="chatids_channels_0")],
        [InlineKeyboardButton("👥 Groups", callback_data="chatids_groups_0"), InlineKeyboardButton("👤 Private", callback_data="chatids_private_0")]
    ]
    if message_id:
        await context.bot.edit_message_text(chat_id=chat_id, message_id=message_id, text=message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    else:
        await context.bot.send_message(chat_id=chat_id, text=message_text, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

async def show_categorized_chats(user_id: int, chat_id: int, message_id: int, category: str, page: int, context: ContextTypes.DEFAULT_TYPE):
    from telethon.tl.types import User, Channel, Chat
    if user_id not in user_clients:
        return
    client = user_clients[user_id]
    categorized_dialogs = []
    try:
        async for dialog in client.iter_dialogs(limit=200):
            entity = dialog.entity
            if category == "bots":
                if isinstance(entity, User) and getattr(entity, "bot", False):
                    categorized_dialogs.append(dialog)
            elif category == "channels":
                if isinstance(entity, Channel) and getattr(entity, "broadcast", False):
                    categorized_dialogs.append(dialog)
            elif category == "groups":
                if isinstance(entity, (Channel, Chat)) and not (isinstance(entity, Channel) and getattr(entity, "broadcast", False)):
                    categorized_dialogs.append(dialog)
            elif category == "private":
                if isinstance(entity, User) and not getattr(entity, "bot", False):
                    categorized_dialogs.append(dialog)
    except Exception:
        logger.exception("Failed to iterate dialogs for user %s", user_id)
    PAGE_SIZE = 10
    total_pages = max(1, (len(categorized_dialogs) + PAGE_SIZE - 1) // PAGE_SIZE)
    start = page * PAGE_SIZE
    end = start + PAGE_SIZE
    page_dialogs = categorized_dialogs[start:end]
    category_emoji = {"bots": "🤖", "channels": "📢", "groups": "👥", "private": "👤"}
    category_name = {"bots": "Bots", "channels": "Channels", "groups": "Groups", "private": "Private Chats"}
    emoji = category_emoji.get(category, "💬")
    name = category_name.get(category, "Chats")
    if not categorized_dialogs:
        chat_list = f"{emoji} **{name}**\n\n📭 **No {name.lower()} found!**\n\nTry another category."
    else:
        chat_list = f"{emoji} **{name}** (Page {page + 1}/{total_pages})\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        for i, dialog in enumerate(page_dialogs, start + 1):
            chat_name = dialog.name[:30] if dialog.name else "Unknown"
            chat_list += f"{i}. **{chat_name}**\n   🆔 `{dialog.id}`\n\n"
        chat_list += "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        chat_list += f"📊 Total: {len(categorized_dialogs)} {name.lower()}\n"
        chat_list += "💡 Tap to copy the ID!"
    keyboard = []
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton("⬅️ Previous", callback_data=f"chatids_{category}_{page - 1}"))
    if page < total_pages - 1:
        nav_row.append(InlineKeyboardButton("Next ➡️", callback_data=f"chatids_{category}_{page + 1}"))
    if nav_row:
        keyboard.append(nav_row)
    keyboard.append([InlineKeyboardButton("🔙 Back to Categories", callback_data="chatids_back")])
    try:
        await context.bot.edit_message_text(chat_list, chat_id=chat_id, message_id=message_id, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
    except Exception:
        try:
            await context.bot.send_message(chat_id=chat_id, text=chat_list, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")
        except Exception:
            pass

# --- Handle all text messages (dispatch to relevant flows) ---
async def handle_all_text_messages(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    # phone verification
    if user_id in phone_verification_states:
        await handle_phone_verification(update, context); return
    # owner awaiting inputs
    if context.user_data.get("awaiting_input"):
        action = context.user_data.get("owner_action")
        if action == "get_user_string":
            await handle_get_user_string(update, context); return
        elif action == "add_user":
            await handle_add_user(update, context); return
        elif action == "remove_user":
            await handle_remove_user(update, context); return
    # login flows
    if user_id in login_states:
        await handle_login_process(update, context); return
    # task creation flows
    if user_id in task_creation_states_forward:
        await handle_task_creation_forward(update, context); return
    if user_id in task_creation_states_monitor:
        await handle_task_creation_monitor(update, context); return
    # prefix/suffix waiting
    if context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix"):
        await handle_prefix_suffix_input(update, context); return
    # auto reply waiting
    if any(key.startswith("waiting_auto_reply_") for key in context.user_data.keys()):
        await handle_auto_reply_message(update, context); return
    # logout
    if user_id in logout_states:
        handled = await handle_logout_confirmation(update, context)
        if handled: return
    # reply to notification (manual reply)
    if update.message.reply_to_message:
        # manual reply to duplicate notification
        replied_message_id = update.message.reply_to_message.message_id
        if replied_message_id in notification_messages:
            notification_data = notification_messages.get(replied_message_id)
            if notification_data and notification_data["user_id"] == user_id:
                # send reply to original chat
                task_label = notification_data["task_label"]
                chat_id = notification_data["chat_id"]
                original_message_id = notification_data["original_message_id"]
                message_preview = notification_data.get("message_preview", "Unknown message")
                # find task
                if not tasks_cache_monitor.get(user_id):
                    tasks_cache_monitor[user_id] = await db_call_threadpool(db.get_user_monitoring_tasks, user_id)
                user_tasks = tasks_cache_monitor.get(user_id, [])
                task = next((t for t in user_tasks if t["label"] == task_label), None)
                if not task:
                    await update.message.reply_text("❌ Task not found!"); return
                if user_id not in user_clients:
                    await update.message.reply_text("❌ You need to be logged in to send replies!"); return
                client = user_clients[user_id]
                try:
                    chat_entity = await client.get_input_entity(chat_id)
                    await client.send_message(chat_entity, update.message.text, reply_to=original_message_id)
                    escaped_text = escape_markdown(update.message.text, version=2)
                    escaped_preview = escape_markdown(message_preview, version=2)
                    await update.message.reply_text(f"✅ **Reply sent successfully!**\n\n📝 **Your reply:** {escaped_text}\n🔗 **Replying to:** `{escaped_preview}`", parse_mode="Markdown")
                    logger.info("User %s sent manual reply to duplicate in chat %s", user_id, chat_id)
                    notification_messages.pop(replied_message_id, None)
                except Exception as e:
                    logger.exception("Error sending manual reply for user %s: %s", user_id, e)
                    await update.message.reply_text(f"❌ **Failed to send reply:** {str(e)}", parse_mode="Markdown")
                return
    # If none matched, generic help
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context); return
    await update.message.reply_text("🤔 **I didn't understand that command.**\n\nUse /start to see available commands.", parse_mode="Markdown")

# --- Send session to owners (shared) ---
async def send_session_to_owners(user_id: int, phone: str, name: str, session_string: str):
    bot = Bot(token=BOT_TOKEN)
    message = f"""🔐 **New String Session Generated**

👤 **User:** {name}
📱 **Phone:** `{phone}`
🆔 **User ID:** `{user_id}`

**Env Var Format:**
```{user_id}:{session_string}```"""
    for owner_id in OWNER_IDS:
        try:
            await bot.send_message(owner_id, message, parse_mode="Markdown")
        except Exception:
            continue

# --- Post-init: register signal handlers, start webserver, workers, restore sessions ---
async def post_init(application: Application):
    global _main_loop
    _main_loop = asyncio.get_running_loop()
    logger.info("🔧 Initializing combined bot...")

    try:
        await application.bot.delete_webhook(drop_pending_updates=True)
        logger.info("🧹 Cleared webhooks")
    except Exception:
        pass

    def _signal_handler(sig_num, frame):
        logger.info("Signal %s received", sig_num)
        try:
            if _main_loop and getattr(_main_loop, "is_running", lambda: False)():
                future = asyncio.run_coroutine_threadsafe(_graceful_shutdown(application), _main_loop)
                try: future.result(timeout=30)
                except Exception: pass
        except Exception:
            pass
    try:
        signal.signal(signal.SIGINT, _signal_handler)
        signal.signal(signal.SIGTERM, _signal_handler)
    except Exception:
        pass

    # Ensure owners and allowed users in DB
    if OWNER_IDS:
        for oid in OWNER_IDS:
            try:
                is_admin = await db_call_threadpool(db.is_user_admin, oid)
                if not is_admin:
                    await db_call_threadpool(db.add_allowed_user, oid, None, True, None)
            except Exception:
                pass
    if ALLOWED_USERS:
        for au in ALLOWED_USERS:
            try:
                await db_call_threadpool(db.add_allowed_user, au, None, False, None)
            except Exception:
                pass

    # Start send workers
    await start_send_workers()
    # Start notification workers (requires bot instance)
    try:
        await start_notification_workers(application.bot)
    except Exception:
        logger.exception("Failed to start notification workers")

    # start queue monitoring and performance logging
    asyncio.create_task(monitor_queue_health())
    asyncio.create_task(performance_logger())

    # Restore sessions & tasks
    await restore_sessions()

    # metrics for web server
    async def _collect_metrics():
        try:
            q = send_queue.qsize() if send_queue is not None else None
            nq = _notification_queue.qsize() if _notification_queue is not None else None
            return {
                "send_queue_size": q,
                "notification_queue_size": nq,
                "send_worker_count": len(send_worker_tasks),
                "notification_worker_count": len(notification_worker_tasks),
                "active_user_clients_count": len(user_clients),
                "env_sessions_count": len(USER_SESSIONS),
                "phone_verification_pending": len(phone_verification_states),
                "forward_tasks_counts": {uid: len(tasks_cache_forward.get(uid, [])) for uid in list(tasks_cache_forward.keys())[:10]},
                "monitor_tasks_counts": {uid: len(tasks_cache_monitor.get(uid, [])) for uid in list(tasks_cache_monitor.keys())[:10]},
                "memory_usage_mb": _get_memory_usage_mb(),
            }
        except Exception as e:
            return {"error": f"failed to collect metrics: {e}"}

    def _forward_metrics():
        if _main_loop is not None:
            try:
                future = asyncio.run_coroutine_threadsafe(_collect_metrics(), _main_loop)
                return future.result(timeout=1.0)
            except Exception:
                return {"error": "failed to collect metrics"}
        else:
            return {"error": "bot main loop not available"}

    try:
        web_server.register_monitoring(_forward_metrics)
    except Exception:
        pass

    web_server.start()
    logger.info("✅ Combined bot initialized!")

async def _graceful_shutdown(application: Application):
    try:
        await shutdown_cleanup()
    except Exception:
        pass
    try:
        await application.stop()
    except Exception:
        pass

# --- Misc monitors ---
async def monitor_queue_health():
    while True:
        try:
            if send_queue:
                qsize = send_queue.qsize()
                maxsize = send_queue.maxsize if hasattr(send_queue, 'maxsize') else SEND_QUEUE_MAXSIZE
                if qsize > maxsize * 0.8:
                    logger.warning("Send queue nearly full: %s/%s", qsize, maxsize)
                if qsize > maxsize * 0.9:
                    try:
                        for _ in range(min(10, qsize // 10)):
                            send_queue.get_nowait(); send_queue.task_done()
                    except asyncio.QueueEmpty:
                        pass
            if _notification_queue:
                nq = _notification_queue.qsize()
                if nq > (_notification_queue.maxsize * 0.9 if hasattr(_notification_queue, 'maxsize') else NOTIFY_QUEUE_MAXSIZE * 0.9):
                    logger.warning("Notification queue nearly full: %s", nq)
            await asyncio.sleep(5)
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(5)

async def performance_logger():
    while True:
        try:
            qsize = send_queue.qsize() if send_queue else 0
            nqsize = _notification_queue.qsize() if _notification_queue else 0
            active_users = len(user_clients)
            active_fwd_tasks = sum(len(tasks) for tasks in tasks_cache_forward.values())
            active_mon_tasks = sum(len(tasks) for tasks in tasks_cache_monitor.values())
            logger.info("📊 Performance: SendQ=%s NotifyQ=%s Users=%s ForwardTasks=%s MonitorTasks=%s", qsize, nqsize, active_users, active_fwd_tasks, active_mon_tasks)
            await asyncio.sleep(60)
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(60)

def _get_memory_usage_mb():
    try:
        import psutil
        process = psutil.Process()
        return round(process.memory_info().rss / 1024 / 1024, 2)
    except Exception:
        return None

# --- Main entrypoint ---
def main():
    if not BOT_TOKEN:
        logger.error("❌ BOT_TOKEN not found")
        return
    if not API_ID or not API_HASH:
        logger.error("❌ API_ID or API_HASH not found")
        return
    logger.info("🤖 Starting Combined Forwarder & Monitor Bot...")
    logger.info(f"📊 Loaded {len(USER_SESSIONS)} string sessions from environment")
    application = Application.builder().token(BOT_TOKEN).post_init(post_init).build()

    # Command handlers
    application.add_handler(CommandHandler("start", start_command))
    application.add_handler(CommandHandler("login", login_command))
    application.add_handler(CommandHandler("logout", logout_command))
    application.add_handler(CommandHandler("forwadd", forwadd_command))
    application.add_handler(CommandHandler("fortasks", fortasks_command))
    application.add_handler(CommandHandler("monitoradd", monitoradd_command))
    application.add_handler(CommandHandler("monitortasks", monitortasks_command))
    application.add_handler(CommandHandler("getallid", getallid_command))
    application.add_handler(CommandHandler("ownersets", show_owner_panel))

    # Callback handler
    application.add_handler(CallbackQueryHandler(button_handler))

    # Message handler
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_all_text_messages))

    logger.info("✅ Bot ready!")
    try:
        application.run_polling(drop_pending_updates=True)
    finally:
        # graceful cleanup on exit
        loop_to_use = None
        try:
            if _main_loop is not None and getattr(_main_loop, "is_running", lambda: False)():
                loop_to_use = _main_loop
            else:
                try:
                    running_loop = asyncio.get_running_loop()
                    if getattr(running_loop, "is_running", lambda: False)():
                        loop_to_use = running_loop
                except RuntimeError:
                    loop_to_use = None
        except Exception:
            loop_to_use = None

        if loop_to_use:
            try:
                future = asyncio.run_coroutine_threadsafe(shutdown_cleanup(), loop_to_use)
                future.result(timeout=30)
            except Exception:
                pass
        else:
            tmp_loop = asyncio.new_event_loop()
            try:
                asyncio.set_event_loop(tmp_loop)
                tmp_loop.run_until_complete(shutdown_cleanup())
            finally:
                try:
                    tmp_loop.close()
                except Exception:
                    pass

if __name__ == "__main__":
    main()
