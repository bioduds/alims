#!/usr/bin/env python3
"""
ALims Event Persistence System

High-performance persistent storage for all captured events:
- SQLite database with optimized schema
- Batch writes for performance
- Automatic indexing and compression
- Background cleanup of old events
- Event replay and analysis capabilities
- Recovery from system restarts
"""

import asyncio
import logging
import sqlite3
import json
import gzip
import time
import threading
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime, timedelta
from pathlib import Path
from collections import deque
import hashlib


class EventDatabase:
    """High-performance SQLite database for event storage"""

    def __init__(self, db_path: str):
        self.db_path = Path(db_path)
        self.logger = logging.getLogger("EventDatabase")

        # Ensure data directory exists
        self.db_path.parent.mkdir(parents=True, exist_ok=True)

        # Connection pool for thread safety
        self._local = threading.local()

        # Initialize database
        self._initialize_database()

        # Performance settings
        self._setup_performance_optimizations()

    def _get_connection(self) -> sqlite3.Connection:
        """Get thread-local database connection"""
        if not hasattr(self._local, "connection"):
            self._local.connection = sqlite3.connect(
                self.db_path, timeout=30.0, check_same_thread=False
            )
            self._local.connection.row_factory = sqlite3.Row
        return self._local.connection

    def _initialize_database(self):
        """Initialize database schema"""
        conn = self._get_connection()

        # Main events table
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp REAL NOT NULL,
                event_type TEXT NOT NULL,
                action TEXT,
                source TEXT NOT NULL,
                data_json TEXT NOT NULL,
                data_compressed BLOB,
                hash TEXT UNIQUE,
                processed BOOLEAN DEFAULT FALSE,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """
        )

        # Patterns table for detected patterns
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS patterns (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                event_id INTEGER,
                pattern_type TEXT NOT NULL,
                confidence REAL NOT NULL,
                pattern_data TEXT NOT NULL,
                embryo_id TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY (event_id) REFERENCES events (id)
            )
        """
        )

        # System stats table
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS system_stats (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp REAL NOT NULL,
                total_events INTEGER,
                events_per_second REAL,
                active_embryos INTEGER,
                avg_fitness REAL,
                storage_mb REAL,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """
        )

        # Agent births table
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS agent_births (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                agent_id TEXT UNIQUE NOT NULL,
                embryo_id TEXT NOT NULL,
                birth_timestamp REAL NOT NULL,
                specialization TEXT,
                fitness_score REAL,
                training_events INTEGER,
                birth_data TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """
        )

        conn.commit()
        self._create_indexes()

    def _create_indexes(self):
        """Create performance indexes"""
        conn = self._get_connection()

        indexes = [
            "CREATE INDEX IF NOT EXISTS idx_events_timestamp ON events(timestamp)",
            "CREATE INDEX IF NOT EXISTS idx_events_type ON events(event_type)",
            "CREATE INDEX IF NOT EXISTS idx_events_source ON events(source)",
            "CREATE INDEX IF NOT EXISTS idx_events_hash ON events(hash)",
            "CREATE INDEX IF NOT EXISTS idx_patterns_type ON patterns(pattern_type)",
            "CREATE INDEX IF NOT EXISTS idx_patterns_embryo ON patterns(embryo_id)",
            "CREATE INDEX IF NOT EXISTS idx_stats_timestamp ON system_stats(timestamp)",
        ]

        for index_sql in indexes:
            try:
                conn.execute(index_sql)
            except sqlite3.Error as e:
                self.logger.debug(f"Index creation note: {e}")

        conn.commit()

    def _setup_performance_optimizations(self):
        """Configure SQLite for high performance"""
        conn = self._get_connection()

        # Performance pragmas
        optimizations = [
            "PRAGMA journal_mode=WAL",  # Write-Ahead Logging
            "PRAGMA synchronous=NORMAL",  # Faster than FULL
            "PRAGMA cache_size=10000",  # 10MB cache
            "PRAGMA temp_store=MEMORY",  # Use memory for temp tables
            "PRAGMA mmap_size=268435456",  # 256MB memory map
        ]

        for pragma in optimizations:
            try:
                conn.execute(pragma)
            except sqlite3.Error as e:
                self.logger.debug(f"Pragma note: {e}")

        conn.commit()

    def store_event(self, event: Dict[str, Any]) -> int:
        """Store single event (for immediate storage)"""
        return self.store_events_batch([event])[0]

    def store_events_batch(self, events: List[Dict[str, Any]]) -> List[int]:
        """Store multiple events in a single transaction"""
        conn = self._get_connection()
        event_ids = []

        try:
            conn.execute("BEGIN TRANSACTION")

            for event in events:
                # Create event hash for deduplication
                event_str = json.dumps(event, sort_keys=True)
                event_hash = hashlib.md5(event_str.encode()).hexdigest()

                # Compress large events
                data_json = json.dumps(event)
                data_compressed = None

                if len(data_json) > 1024:  # Compress events > 1KB
                    data_compressed = gzip.compress(data_json.encode())
                    data_json = None  # Store only compressed version

                # Insert event
                cursor = conn.execute(
                    """
                    INSERT OR IGNORE INTO events 
                    (timestamp, event_type, action, source, data_json, 
                     data_compressed, hash)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                    (
                        event.get("ts", time.time()),
                        event.get("type", "unknown"),
                        event.get("action"),
                        event.get("src", "unknown"),
                        data_json,
                        data_compressed,
                        event_hash,
                    ),
                )

                if cursor.lastrowid:
                    event_ids.append(cursor.lastrowid)

            conn.execute("COMMIT")

        except sqlite3.Error as e:
            conn.execute("ROLLBACK")
            self.logger.error(f"Batch storage error: {e}")
            raise

        return event_ids

    def store_pattern(self, event_id: int, pattern: Dict[str, Any], embryo_id: str):
        """Store detected pattern"""
        conn = self._get_connection()

        try:
            conn.execute(
                """
                INSERT INTO patterns 
                (event_id, pattern_type, confidence, pattern_data, embryo_id)
                VALUES (?, ?, ?, ?, ?)
            """,
                (
                    event_id,
                    pattern.get("type", "unknown"),
                    pattern.get("confidence", 0.0),
                    json.dumps(pattern),
                    embryo_id,
                ),
            )
            conn.commit()

        except sqlite3.Error as e:
            self.logger.error(f"Pattern storage error: {e}")

    def get_events(
        self,
        start_time: Optional[float] = None,
        end_time: Optional[float] = None,
        event_type: Optional[str] = None,
        limit: int = 1000,
    ) -> List[Dict[str, Any]]:
        """Retrieve events with filtering"""
        conn = self._get_connection()

        query = "SELECT * FROM events WHERE 1=1"
        params = []

        if start_time:
            query += " AND timestamp >= ?"
            params.append(start_time)

        if end_time:
            query += " AND timestamp <= ?"
            params.append(end_time)

        if event_type:
            query += " AND event_type = ?"
            params.append(event_type)

        query += " ORDER BY timestamp DESC LIMIT ?"
        params.append(limit)

        try:
            cursor = conn.execute(query, params)
            events = []

            for row in cursor.fetchall():
                # Decompress data if needed
                if row["data_compressed"]:
                    data = json.loads(gzip.decompress(row["data_compressed"]).decode())
                else:
                    data = json.loads(row["data_json"])

                events.append(
                    {
                        "id": row["id"],
                        "timestamp": row["timestamp"],
                        "event_type": row["event_type"],
                        "action": row["action"],
                        "source": row["source"],
                        "data": data,
                        "processed": row["processed"],
                    }
                )

            return events

        except sqlite3.Error as e:
            self.logger.error(f"Event retrieval error: {e}")
            return []

    def get_database_stats(self) -> Dict[str, Any]:
        """Get database statistics"""
        conn = self._get_connection()

        try:
            # Event counts
            cursor = conn.execute("SELECT COUNT(*) FROM events")
            total_events = cursor.fetchone()[0]

            cursor = conn.execute("SELECT COUNT(*) FROM patterns")
            total_patterns = cursor.fetchone()[0]

            # Database size
            cursor = conn.execute("PRAGMA page_count")
            page_count = cursor.fetchone()[0]
            cursor = conn.execute("PRAGMA page_size")
            page_size = cursor.fetchone()[0]
            db_size_mb = (page_count * page_size) / (1024 * 1024)

            # Recent activity
            one_hour_ago = time.time() - 3600
            cursor = conn.execute(
                "SELECT COUNT(*) FROM events WHERE timestamp > ?", (one_hour_ago,)
            )
            recent_events = cursor.fetchone()[0]

            return {
                "total_events": total_events,
                "total_patterns": total_patterns,
                "database_size_mb": round(db_size_mb, 2),
                "recent_events_1h": recent_events,
                "events_per_hour": recent_events if recent_events else 0,
            }

        except sqlite3.Error as e:
            self.logger.error(f"Stats retrieval error: {e}")
            return {}

    def cleanup_old_events(self, days_to_keep: int = 30):
        """Remove events older than specified days"""
        conn = self._get_connection()
        cutoff_time = time.time() - (days_to_keep * 24 * 3600)

        try:
            # Delete old patterns first (foreign key constraint)
            cursor = conn.execute(
                """
                DELETE FROM patterns WHERE event_id IN (
                    SELECT id FROM events WHERE timestamp < ?
                )
            """,
                (cutoff_time,),
            )
            patterns_deleted = cursor.rowcount

            # Delete old events
            cursor = conn.execute(
                "DELETE FROM events WHERE timestamp < ?", (cutoff_time,)
            )
            events_deleted = cursor.rowcount

            # Vacuum to reclaim space
            conn.execute("VACUUM")
            conn.commit()

            self.logger.info(
                f"Cleanup complete: {events_deleted} events, "
                f"{patterns_deleted} patterns deleted"
            )

        except sqlite3.Error as e:
            self.logger.error(f"Cleanup error: {e}")


class EventPersistenceManager:
    """High-level manager for event persistence"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("EventPersistence")

        # Database setup
        db_path = config.get("database_path", "data/events.db")
        self.database = EventDatabase(db_path)

        # Batch processing
        self.batch_size = config.get("batch_size", 100)
        self.batch_timeout = config.get("batch_timeout", 5.0)  # 5 seconds
        self.event_queue = deque(maxlen=10000)

        # Background processing
        self.is_running = False
        self.batch_processor_task = None
        self.cleanup_task = None

        # Performance tracking
        self.total_stored = 0
        self.last_batch_time = time.time()

        # Cleanup settings
        self.cleanup_interval = config.get("cleanup_interval_hours", 24)
        self.retention_days = config.get("retention_days", 30)

    async def start(self):
        """Start the persistence manager"""
        self.logger.info("🗄️ Starting Event Persistence Manager...")

        self.is_running = True

        # Start background tasks
        self.batch_processor_task = asyncio.create_task(self._batch_processor())
        self.cleanup_task = asyncio.create_task(self._cleanup_scheduler())

        # Log initial stats
        stats = self.database.get_database_stats()
        self.logger.info(
            f"📊 Database ready - {stats.get('total_events', 0)} events, "
            f"{stats.get('database_size_mb', 0)}MB"
        )

        self.logger.info("✅ Event Persistence Manager started")

    async def stop(self):
        """Stop the persistence manager"""
        self.logger.info("🛑 Stopping Event Persistence Manager...")

        self.is_running = False

        # Cancel background tasks
        if self.batch_processor_task:
            self.batch_processor_task.cancel()
        if self.cleanup_task:
            self.cleanup_task.cancel()

        # Process remaining events
        await self._flush_remaining_events()

        self.logger.info("✅ Event Persistence Manager stopped")

    def queue_event(self, event: Dict[str, Any]):
        """Queue event for batch processing"""
        self.event_queue.append(event)

    def queue_events_batch(self, events: List[Dict[str, Any]]):
        """Queue multiple events"""
        for event in events:
            self.event_queue.append(event)

    async def _batch_processor(self):
        """Background batch processor"""
        while self.is_running:
            try:
                current_time = time.time()

                # Process batch if we have events and conditions are met
                should_process = self.event_queue and (
                    len(self.event_queue) >= self.batch_size
                    or current_time - self.last_batch_time >= self.batch_timeout
                )

                if should_process:
                    await self._process_batch()

                await asyncio.sleep(0.1)  # 100ms check interval

            except Exception as e:
                self.logger.error(f"Batch processor error: {e}")
                await asyncio.sleep(1)

    async def _process_batch(self):
        """Process a batch of events"""
        if not self.event_queue:
            return

        # Extract batch
        batch = []
        batch_size = min(self.batch_size, len(self.event_queue))

        for _ in range(batch_size):
            if self.event_queue:
                batch.append(self.event_queue.popleft())

        if not batch:
            return

        try:
            # Store batch in database
            event_ids = await asyncio.get_event_loop().run_in_executor(
                None, self.database.store_events_batch, batch
            )

            self.total_stored += len(event_ids)
            self.last_batch_time = time.time()

            self.logger.debug(
                f"📝 Stored batch: {len(event_ids)} events "
                f"(Total: {self.total_stored})"
            )

        except Exception as e:
            self.logger.error(f"Batch storage error: {e}")
            # Re-queue events on error
            for event in batch:
                self.event_queue.appendleft(event)

    async def _flush_remaining_events(self):
        """Flush all remaining events before shutdown"""
        if self.event_queue:
            self.logger.info(f"Flushing {len(self.event_queue)} remaining events...")

            while self.event_queue:
                await self._process_batch()

    async def _cleanup_scheduler(self):
        """Schedule periodic cleanup"""
        while self.is_running:
            try:
                # Wait for cleanup interval
                await asyncio.sleep(self.cleanup_interval * 3600)

                if self.is_running:
                    await self._perform_cleanup()

            except Exception as e:
                self.logger.error(f"Cleanup scheduler error: {e}")

    async def _perform_cleanup(self):
        """Perform database cleanup"""
        self.logger.info("🧹 Starting database cleanup...")

        try:
            # Run cleanup in executor to avoid blocking
            await asyncio.get_event_loop().run_in_executor(
                None, self.database.cleanup_old_events, self.retention_days
            )

            # Log new stats
            stats = self.database.get_database_stats()
            self.logger.info(
                f"✅ Cleanup complete - {stats.get('total_events', 0)} events remaining, "
                f"{stats.get('database_size_mb', 0)}MB"
            )

        except Exception as e:
            self.logger.error(f"Cleanup error: {e}")

    def get_stats(self) -> Dict[str, Any]:
        """Get persistence statistics"""
        db_stats = self.database.get_database_stats()

        return {
            "total_stored": self.total_stored,
            "queue_size": len(self.event_queue),
            "database_stats": db_stats,
            "batch_size": self.batch_size,
            "retention_days": self.retention_days,
        }

    def get_events(self, **kwargs) -> List[Dict[str, Any]]:
        """Get events from database"""
        return self.database.get_events(**kwargs)

    def store_pattern(self, event_id: int, pattern: Dict[str, Any], embryo_id: str):
        """Store detected pattern"""
        self.database.store_pattern(event_id, pattern, embryo_id)


# Factory function for easy integration
def create_event_persistence(config: Dict[str, Any]) -> EventPersistenceManager:
    """Create and configure event persistence manager"""
    return EventPersistenceManager(config)
