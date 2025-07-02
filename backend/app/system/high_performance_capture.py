#!/usr/bin/env python3
"""
ALims High-Performance Event Capture System

Optimized for maximum event capture rate with minimal system impact:
- Sub-second polling intervals
- Efficient native API usage
- Batch event processing
- Asynchronous operations
- Memory-efficient event queues
"""

import asyncio
import logging
import time
import os
import subprocess
import json
import threading
from typing import Dict, List, Optional, Any, Callable, Set
from datetime import datetime
from pathlib import Path
from collections import deque, defaultdict
import concurrent.futures

try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler

    WATCHDOG_AVAILABLE = True
except ImportError:
    WATCHDOG_AVAILABLE = False

try:
    import psutil

    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False

try:
    from .event_persistence import create_event_persistence

    PERSISTENCE_AVAILABLE = True
except ImportError:
    PERSISTENCE_AVAILABLE = False


class HighPerformanceFileHandler(FileSystemEventHandler):
    """Ultra-fast file system event handler with batching"""

    def __init__(self, event_callback: Callable[[List[Dict[str, Any]]], None]):
        super().__init__()
        self.event_callback = event_callback
        self.logger = logging.getLogger("HPFileHandler")

        # High-performance event batching
        self.event_queue = deque(maxlen=10000)
        self.batch_size = 50
        self.batch_timeout = 0.1  # 100ms batching
        self.last_batch_time = time.time()

        # Optimized filtering
        self.ignore_extensions = {
            ".tmp",
            ".temp",
            ".swp",
            ".lock",
            ".log",
            ".cache",
            ".DS_Store",
            ".localized",
            ".Trash",
        }

        self.ignore_dirs = {
            "__pycache__",
            ".git",
            ".svn",
            ".hg",
            "node_modules",
            ".vscode",
            ".idea",
            ".mypy_cache",
            ".pytest_cache",
        }

        # Event deduplication with time-based cleanup
        self.recent_events = {}
        self.dedupe_window = 0.5  # 500ms deduplication window

        # Start batch processor
        self._start_batch_processor()

    def _start_batch_processor(self):
        """Start background batch processor"""

        def batch_processor():
            while True:
                try:
                    current_time = time.time()

                    # Process batch if we have events and timeout reached
                    if self.event_queue and (
                        len(self.event_queue) >= self.batch_size
                        or current_time - self.last_batch_time >= self.batch_timeout
                    ):

                        # Extract batch
                        batch = []
                        for _ in range(min(self.batch_size, len(self.event_queue))):
                            if self.event_queue:
                                batch.append(self.event_queue.popleft())

                        if batch:
                            self.event_callback(batch)
                            self.last_batch_time = current_time

                    # Cleanup old deduplication entries
                    if current_time % 10 < 0.1:  # Every ~10 seconds
                        cutoff = current_time - self.dedupe_window * 2
                        self.recent_events = {
                            k: v for k, v in self.recent_events.items() if v > cutoff
                        }

                    time.sleep(0.01)  # 10ms sleep

                except Exception as e:
                    self.logger.error(f"Batch processor error: {e}")
                    time.sleep(0.1)

        thread = threading.Thread(target=batch_processor, daemon=True)
        thread.start()

    def _should_ignore_fast(self, path: str) -> bool:
        """Ultra-fast path filtering"""
        path_lower = path.lower()

        # Quick extension check
        if any(path_lower.endswith(ext) for ext in self.ignore_extensions):
            return True

        # Quick directory check
        if any(ignore_dir in path_lower for ignore_dir in self.ignore_dirs):
            return True

        # Hidden files (starts with dot after last slash)
        filename = path_lower.split("/")[-1]
        if filename.startswith(".") and filename != ".":
            return True

        return False

    def _dedupe_event(self, event_key: str) -> bool:
        """Fast event deduplication"""
        current_time = time.time()

        if event_key in self.recent_events:
            if current_time - self.recent_events[event_key] < self.dedupe_window:
                return True  # Duplicate

        self.recent_events[event_key] = current_time
        return False

    def _create_fast_event(
        self, action: str, src_path: str, dest_path: str = None
    ) -> Dict[str, Any]:
        """Create event with minimal overhead"""
        path_obj = Path(src_path)

        event = {
            "type": "file_op",
            "action": action,
            "path": src_path,
            "name": path_obj.name,
            "ext": path_obj.suffix.lower(),
            "dir": str(path_obj.parent),
            "ts": time.time(),
            "src": "fs",
        }

        if dest_path:
            event["dest"] = dest_path

        return event

    def _queue_event(self, action: str, src_path: str, dest_path: str = None):
        """Queue event for batch processing"""
        if self._should_ignore_fast(src_path):
            return

        event_key = f"{action}:{src_path}"
        if self._dedupe_event(event_key):
            return

        event = self._create_fast_event(action, src_path, dest_path)
        self.event_queue.append(event)

    def on_created(self, event):
        if not event.is_directory:
            self._queue_event("create", event.src_path)

    def on_modified(self, event):
        if not event.is_directory:
            self._queue_event("modify", event.src_path)

    def on_deleted(self, event):
        if not event.is_directory:
            self._queue_event("delete", event.src_path)

    def on_moved(self, event):
        if not event.is_directory:
            self._queue_event("move", event.src_path, event.dest_path)


class FastApplicationMonitor:
    """High-frequency application monitoring"""

    def __init__(self, event_callback: Callable[[List[Dict[str, Any]]], None]):
        self.event_callback = event_callback
        self.logger = logging.getLogger("FastAppMonitor")

        # Fast tracking state
        self.running_apps = set()
        self.current_app = None
        self.app_start_times = {}

        # Event batching
        self.event_queue = deque(maxlen=1000)
        self.batch_interval = 0.5  # 500ms batches

        # Process cache for performance
        self.process_cache = {}
        self.cache_timeout = 1.0  # 1 second cache
        self.last_cache_update = 0

        # User app patterns (optimized lookup)
        self.user_app_patterns = {
            "safari",
            "chrome",
            "firefox",
            "edge",
            "brave",
            "code",
            "vscode",
            "xcode",
            "pycharm",
            "intellij",
            "terminal",
            "iterm",
            "warp",
            "hyper",
            "slack",
            "discord",
            "teams",
            "zoom",
            "skype",
            "photoshop",
            "illustrator",
            "figma",
            "sketch",
            "mail",
            "outlook",
            "thunderbird",
            "notes",
            "notion",
            "obsidian",
            "bear",
            "spotify",
            "music",
            "vlc",
            "quicktime",
            "finder",
            "pathfinder",
        }

    async def start_monitoring(self):
        """Start high-frequency application monitoring"""
        if not PSUTIL_AVAILABLE:
            self.logger.warning("psutil not available")
            return

        self.logger.info("Starting fast application monitoring...")

        # Start batch processor
        asyncio.create_task(self._batch_processor())

        # Main monitoring loop - much faster
        while True:
            try:
                await self._fast_app_check()
                await asyncio.sleep(0.2)  # 200ms intervals - 5x faster!
            except Exception as e:
                self.logger.error(f"Fast app monitoring error: {e}")
                await asyncio.sleep(1)

    async def _batch_processor(self):
        """Process event batches"""
        while True:
            try:
                if self.event_queue:
                    batch = []
                    for _ in range(min(20, len(self.event_queue))):
                        if self.event_queue:
                            batch.append(self.event_queue.popleft())

                    if batch:
                        self.event_callback(batch)

                await asyncio.sleep(self.batch_interval)

            except Exception as e:
                self.logger.error(f"App batch processor error: {e}")
                await asyncio.sleep(1)

    async def _fast_app_check(self):
        """Fast application state checking"""
        current_time = time.time()

        # Update process cache if needed
        if current_time - self.last_cache_update > self.cache_timeout:
            await self._update_process_cache()

        # Quick app detection from cache
        current_apps = set()
        for proc_name in self.process_cache:
            if self._is_user_app_fast(proc_name):
                current_apps.add(proc_name)

        # Detect changes
        new_apps = current_apps - self.running_apps
        closed_apps = self.running_apps - current_apps

        # Queue events
        for app in new_apps:
            self._queue_app_event("launch", app)
            self.app_start_times[app] = current_time

        for app in closed_apps:
            duration = current_time - self.app_start_times.get(app, current_time)
            self._queue_app_event("close", app, {"duration": duration})
            self.app_start_times.pop(app, None)

        self.running_apps = current_apps

        # Check active app (less frequently)
        if current_time % 2 < 0.5:  # Every ~2 seconds
            await self._check_active_app()

    async def _update_process_cache(self):
        """Update process cache efficiently"""
        try:
            new_cache = {}
            for proc in psutil.process_iter(["name"]):
                try:
                    proc_name = proc.info["name"]
                    new_cache[proc_name] = True
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue

            self.process_cache = new_cache
            self.last_cache_update = time.time()

        except Exception as e:
            self.logger.error(f"Process cache update error: {e}")

    def _is_user_app_fast(self, app_name: str) -> bool:
        """Fast user app detection"""
        app_lower = app_name.lower()
        return any(pattern in app_lower for pattern in self.user_app_patterns)

    async def _check_active_app(self):
        """Check active application with timeout"""
        try:
            # Use faster AppleScript with timeout
            script = 'tell app "System Events" to get name of first process whose frontmost is true'

            proc = await asyncio.create_subprocess_exec(
                "osascript",
                "-e",
                script,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )

            stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=1.0)

            if proc.returncode == 0:
                active_app = stdout.decode().strip()
                if active_app != self.current_app and self._is_user_app_fast(
                    active_app
                ):
                    self._queue_app_event("focus", active_app)
                    self.current_app = active_app

        except asyncio.TimeoutError:
            self.logger.debug("Active app check timeout")
        except Exception as e:
            self.logger.debug(f"Active app check error: {e}")

    def _queue_app_event(self, action: str, app_name: str, extra_data: Dict = None):
        """Queue application event"""
        event = {
            "type": "app",
            "action": action,
            "app": app_name,
            "ts": time.time(),
            "src": "app_mon",
        }

        if extra_data:
            event.update(extra_data)

        self.event_queue.append(event)


class SystemActivityMonitor:
    """Monitor system-wide activity patterns"""

    def __init__(self, event_callback: Callable[[List[Dict[str, Any]]], None]):
        self.event_callback = event_callback
        self.logger = logging.getLogger("SystemActivityMonitor")

        # Activity tracking
        self.last_activity_time = time.time()
        self.activity_threshold = 30  # seconds of inactivity
        self.is_idle = False

        # Network activity
        self.last_network_stats = None
        self.network_threshold = 1024 * 1024  # 1MB threshold

        # Event queue
        self.event_queue = deque(maxlen=500)

    async def start_monitoring(self):
        """Start system activity monitoring"""
        self.logger.info("Starting system activity monitoring...")

        # Start batch processor
        asyncio.create_task(self._batch_processor())

        while True:
            try:
                await self._check_system_activity()
                await asyncio.sleep(1)  # 1 second intervals
            except Exception as e:
                self.logger.error(f"System activity error: {e}")
                await asyncio.sleep(5)

    async def _batch_processor(self):
        """Process activity event batches"""
        while True:
            try:
                if self.event_queue:
                    batch = list(self.event_queue)
                    self.event_queue.clear()
                    if batch:
                        self.event_callback(batch)

                await asyncio.sleep(2)  # 2 second batches

            except Exception as e:
                self.logger.error(f"Activity batch error: {e}")
                await asyncio.sleep(5)

    async def _check_system_activity(self):
        """Check various system activity indicators"""
        current_time = time.time()

        # Check for user activity indicators
        activity_detected = await self._detect_user_activity()

        if activity_detected:
            if self.is_idle:
                self._queue_activity_event("active", "user_returned")
                self.is_idle = False
            self.last_activity_time = current_time
        else:
            # Check for idle state
            idle_time = current_time - self.last_activity_time
            if idle_time > self.activity_threshold and not self.is_idle:
                self._queue_activity_event(
                    "idle", "user_away", {"idle_time": idle_time}
                )
                self.is_idle = True

        # Check network activity
        await self._check_network_activity()

    async def _detect_user_activity(self) -> bool:
        """Detect if user is actively using the system"""
        try:
            # Check CPU usage as activity indicator
            cpu_percent = psutil.cpu_percent(interval=0.1)
            if cpu_percent > 20:  # Significant CPU activity
                return True

            # Check if any user apps are using CPU
            for proc in psutil.process_iter(["name", "cpu_percent"]):
                try:
                    if proc.info["cpu_percent"] > 5:  # App using CPU
                        app_name = proc.info["name"].lower()
                        if any(
                            pattern in app_name
                            for pattern in ["safari", "chrome", "code", "terminal"]
                        ):
                            return True
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue

            return False

        except Exception as e:
            self.logger.debug(f"Activity detection error: {e}")
            return False

    async def _check_network_activity(self):
        """Monitor network activity"""
        try:
            if not PSUTIL_AVAILABLE:
                return

            net_stats = psutil.net_io_counters()

            if self.last_network_stats:
                bytes_sent = net_stats.bytes_sent - self.last_network_stats.bytes_sent
                bytes_recv = net_stats.bytes_recv - self.last_network_stats.bytes_recv

                total_bytes = bytes_sent + bytes_recv

                if total_bytes > self.network_threshold:
                    self._queue_activity_event(
                        "network",
                        "high_activity",
                        {
                            "bytes_sent": bytes_sent,
                            "bytes_recv": bytes_recv,
                            "total": total_bytes,
                        },
                    )

            self.last_network_stats = net_stats

        except Exception as e:
            self.logger.debug(f"Network activity error: {e}")

    def _queue_activity_event(
        self, activity_type: str, action: str, extra_data: Dict = None
    ):
        """Queue system activity event"""
        event = {
            "type": "system_activity",
            "activity": activity_type,
            "action": action,
            "ts": time.time(),
            "src": "sys_mon",
        }

        if extra_data:
            event.update(extra_data)

        self.event_queue.append(event)


class HighPerformanceEventCapture:
    """Main high-performance event capture coordinator"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("HPEventCapture")

        # Performance metrics
        self.total_events = 0
        self.events_per_second = 0
        self.start_time = time.time()
        self.last_stats_time = time.time()
        self.last_event_count = 0

        # Event callback
        self.event_callback = None

        # Monitors
        self.file_handler = None
        self.app_monitor = None
        self.observer = None

        # Event processing
        self.event_processor = None

        # Persistence
        self.persistence_manager = None
        if PERSISTENCE_AVAILABLE and config.get("enable_persistence", True):
            persistence_config = config.get("persistence", {})
            self.persistence_manager = create_event_persistence(persistence_config)

    def set_event_callback(self, callback: Callable[[Dict[str, Any]], None]):
        """Set callback for individual events"""
        self.event_callback = callback

    async def start_capture(self):
        """Start high-performance event capture"""
        self.logger.info("🚀 Starting High-Performance Event Capture...")

        # Start persistence manager
        if self.persistence_manager:
            await self.persistence_manager.start()

        # Start event processor
        self.event_processor = asyncio.create_task(self._process_events())

        # Start file system monitoring
        await self._start_filesystem_monitoring()

        # Start application monitoring
        asyncio.create_task(self._start_app_monitoring())

        # Start performance monitoring
        asyncio.create_task(self._monitor_performance())

        self.logger.info("✅ High-Performance Event Capture started")

    async def _start_filesystem_monitoring(self):
        """Start optimized filesystem monitoring"""
        if not WATCHDOG_AVAILABLE:
            self.logger.warning("Watchdog not available")
            return

        self.file_handler = HighPerformanceFileHandler(self._handle_event_batch)
        self.observer = Observer()

        # Monitor configured paths
        watch_paths = self.config.get("watch_paths", [os.path.expanduser("~")])

        for path in watch_paths:
            if os.path.exists(path):
                self.observer.schedule(self.file_handler, path, recursive=True)
                self.logger.info(f"HP Monitoring: {path}")

        self.observer.start()

    async def _start_app_monitoring(self):
        """Start fast application monitoring"""
        self.app_monitor = FastApplicationMonitor(self._handle_event_batch)
        await self.app_monitor.start_monitoring()

    async def _start_activity_monitoring(self):
        """Start system activity monitoring"""
        self.activity_monitor = SystemActivityMonitor(self._handle_event_batch)
        await self.activity_monitor.start_monitoring()

    def _handle_event_batch(self, events: List[Dict[str, Any]]):
        """Handle batch of events"""
        # Update metrics
        self.total_events += len(events)

        # Persist events to database
        if self.persistence_manager:
            self.persistence_manager.queue_events_batch(events)

        # Process each event through callback
        if self.event_callback:
            for event in events:
                try:
                    # Handle both sync and async callbacks
                    import inspect

                    if inspect.iscoroutinefunction(self.event_callback):
                        # Schedule async callback without waiting
                        try:
                            loop = asyncio.get_event_loop()
                            loop.create_task(self.event_callback(event))
                        except RuntimeError:
                            # No event loop, skip
                            pass
                    else:
                        # Synchronous callback
                        self.event_callback(event)
                except Exception as e:
                    self.logger.error(f"Event callback error: {e}")

    async def _process_events(self):
        """Background event processing"""
        while True:
            try:
                # Any additional event processing can go here
                await asyncio.sleep(1)
            except Exception as e:
                self.logger.error(f"Event processing error: {e}")
                await asyncio.sleep(5)

    async def _monitor_performance(self):
        """Monitor capture performance"""
        while True:
            try:
                current_time = time.time()
                time_diff = current_time - self.last_stats_time

                if time_diff >= 5:  # Every 5 seconds
                    event_diff = self.total_events - self.last_event_count
                    self.events_per_second = event_diff / time_diff

                    self.logger.info(
                        f"🚀 HP Capture - "
                        f"Total: {self.total_events}, "
                        f"Rate: {self.events_per_second:.1f}/sec"
                    )

                    self.last_stats_time = current_time
                    self.last_event_count = self.total_events

                await asyncio.sleep(5)

            except Exception as e:
                self.logger.error(f"Performance monitoring error: {e}")
                await asyncio.sleep(30)

    async def stop_capture(self):
        """Stop event capture"""
        self.logger.info("Stopping high-performance event capture...")

        if self.observer:
            self.observer.stop()
            self.observer.join()

        if self.event_processor:
            self.event_processor.cancel()

        # Stop persistence manager
        if self.persistence_manager:
            await self.persistence_manager.stop()

        self.logger.info("✅ High-performance event capture stopped")

    def get_capture_stats(self) -> Dict[str, Any]:
        """Get capture performance statistics"""
        uptime = time.time() - self.start_time

        return {
            "total_events": self.total_events,
            "events_per_second": self.events_per_second,
            "uptime_seconds": uptime,
            "average_rate": self.total_events / uptime if uptime > 0 else 0,
        }
