#!/usr/bin/env python3
"""
ALims macOS System Event Capture

Captures real system events from macOS for feeding to the embryo pool:
- File system events (create, modify, delete, move)
- Application launches and switches
- Network activity patterns
- User interaction patterns
- System resource usage
"""

import asyncio
import logging
import time
import os
import subprocess
import json
from typing import Dict, List, Optional, Any, Callable
from datetime import datetime
from pathlib import Path

try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler

    WATCHDOG_AVAILABLE = True
except ImportError:
    WATCHDOG_AVAILABLE = False
    print("Warning: watchdog not available. Install with: pip install watchdog")
    
    # Create a dummy base class if watchdog is not available
    class FileSystemEventHandler:
        def __init__(self):
            pass

try:
    import psutil

    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("Warning: psutil not available. Install with: pip install psutil")


class AlimsFileSystemEventHandler(FileSystemEventHandler):
    """Handles file system events"""

    def __init__(self, event_callback: Callable[[Dict[str, Any]], None]):
        super().__init__()
        self.event_callback = event_callback
        self.logger = logging.getLogger("FileSystemEventHandler")

        # Filter out system and temporary files
        self.ignored_patterns = {
            ".DS_Store",
            ".Trash",
            ".cache",
            ".tmp",
            "__pycache__",
            ".git",
            ".svn",
            ".hg",
            "node_modules",
            ".vscode",
            ".idea",
        }

        # Track recent events to avoid duplicates
        self.recent_events = {}
        self.event_timeout = 2.0  # seconds

    def _should_ignore_path(self, path: str) -> bool:
        """Check if path should be ignored"""
        path_obj = Path(path)

        # Ignore hidden files and system files
        if any(part.startswith(".") for part in path_obj.parts):
            return True

        # Ignore specific patterns
        if any(pattern in path for pattern in self.ignored_patterns):
            return True

        # Ignore temporary files
        if path_obj.suffix in {".tmp", ".temp", ".swp", ".lock"}:
            return True

        return False

    def _deduplicate_event(self, event_type: str, path: str) -> bool:
        """Check if this is a duplicate recent event"""
        event_key = f"{event_type}:{path}"
        current_time = time.time()

        if event_key in self.recent_events:
            if current_time - self.recent_events[event_key] < self.event_timeout:
                return True  # Duplicate

        self.recent_events[event_key] = current_time

        # Clean old events
        self.recent_events = {
            k: v
            for k, v in self.recent_events.items()
            if current_time - v < self.event_timeout
        }

        return False

    def _create_file_event(
        self, event_type: str, src_path: str, dest_path: str = None
    ) -> Dict[str, Any]:
        """Create standardized file event"""
        path_obj = Path(src_path)

        event = {
            "type": "file_operation",
            "action": event_type,
            "path": src_path,
            "filename": path_obj.name,
            "extension": path_obj.suffix.lower(),
            "directory": str(path_obj.parent),
            "size": 0,
            "timestamp": time.time(),
            "source": "filesystem",
        }

        # Add file size if file exists
        try:
            if path_obj.exists() and path_obj.is_file():
                event["size"] = path_obj.stat().st_size
        except (OSError, PermissionError):
            pass

        # Add destination for move events
        if dest_path:
            event["dest_path"] = dest_path
            event["dest_directory"] = str(Path(dest_path).parent)

        return event

    def on_created(self, event):
        """Handle file/directory creation"""
        if event.is_directory or self._should_ignore_path(event.src_path):
            return

        if self._deduplicate_event("create", event.src_path):
            return

        file_event = self._create_file_event("create", event.src_path)
        self.event_callback(file_event)

    def on_modified(self, event):
        """Handle file/directory modification"""
        if event.is_directory or self._should_ignore_path(event.src_path):
            return

        if self._deduplicate_event("modify", event.src_path):
            return

        file_event = self._create_file_event("modify", event.src_path)
        self.event_callback(file_event)

    def on_deleted(self, event):
        """Handle file/directory deletion"""
        if event.is_directory or self._should_ignore_path(event.src_path):
            return

        if self._deduplicate_event("delete", event.src_path):
            return

        file_event = self._create_file_event("delete", event.src_path)
        self.event_callback(file_event)

    def on_moved(self, event):
        """Handle file/directory move"""
        if event.is_directory or self._should_ignore_path(event.src_path):
            return

        if self._deduplicate_event("move", f"{event.src_path}->{event.dest_path}"):
            return

        file_event = self._create_file_event("move", event.src_path, event.dest_path)
        self.event_callback(file_event)


class ApplicationMonitor:
    """Monitors application launches and switches"""

    def __init__(self, event_callback: Callable[[Dict[str, Any]], None]):
        self.event_callback = event_callback
        self.logger = logging.getLogger("ApplicationMonitor")

        # Track running applications
        self.running_apps = set()
        self.current_app = None
        self.last_check = time.time()

    async def start_monitoring(self):
        """Start monitoring application events"""
        if not PSUTIL_AVAILABLE:
            self.logger.warning(
                "psutil not available - application monitoring disabled"
            )
            return

        self.logger.info("Starting application monitoring...")

        while True:
            try:
                await self._check_applications()
                await asyncio.sleep(5)  # Check every 5 seconds
            except Exception as e:
                self.logger.error(f"Application monitoring error: {e}")
                await asyncio.sleep(10)

    async def _check_applications(self):
        """Check for application changes"""
        try:
            current_apps = set()

            # Get currently running applications
            for proc in psutil.process_iter(["pid", "name", "create_time"]):
                try:
                    proc_info = proc.info
                    app_name = proc_info["name"]

                    # Filter out system processes
                    if self._is_user_application(app_name):
                        current_apps.add(app_name)

                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue

            # Detect new applications
            new_apps = current_apps - self.running_apps
            for app in new_apps:
                self._create_app_event("launch", app)

            # Detect closed applications
            closed_apps = self.running_apps - current_apps
            for app in closed_apps:
                self._create_app_event("close", app)

            self.running_apps = current_apps

            # Check for active application (simplified)
            await self._check_active_application()

        except Exception as e:
            self.logger.error(f"Error checking applications: {e}")

    def _is_user_application(self, app_name: str) -> bool:
        """Check if this is a user application worth tracking"""
        # Filter out system processes and common daemons
        system_processes = {
            "kernel_task",
            "launchd",
            "kextd",
            "mds",
            "mdworker",
            "WindowServer",
            "loginwindow",
            "SystemUIServer",
            "Dock",
            "Finder",
            "cfprefsd",
            "distnoted",
        }

        if app_name.lower() in system_processes:
            return False

        # Include applications that typically indicate user activity
        user_apps = {
            "Safari",
            "Chrome",
            "Firefox",
            "Code",
            "Terminal",
            "Xcode",
            "Photoshop",
            "Figma",
            "Slack",
            "Discord",
            "Mail",
            "Messages",
            "Calendar",
            "Notes",
            "TextEdit",
        }

        return any(user_app.lower() in app_name.lower() for user_app in user_apps)

    async def _check_active_application(self):
        """Check which application is currently active"""
        try:
            # Use AppleScript to get frontmost application
            script = """
            tell application "System Events"
                set frontApp to name of first application process whose frontmost is true
                return frontApp
            end tell
            """

            result = subprocess.run(
                ["osascript", "-e", script], capture_output=True, text=True, timeout=5
            )

            if result.returncode == 0:
                active_app = result.stdout.strip()
                if active_app != self.current_app and self._is_user_application(
                    active_app
                ):
                    self._create_app_event("switch", active_app)
                    self.current_app = active_app

        except (subprocess.TimeoutExpired, subprocess.SubprocessError) as e:
            self.logger.debug(f"Could not get active application: {e}")

    def _create_app_event(self, action: str, app_name: str):
        """Create application event"""
        event = {
            "type": "app_launch" if action in ["launch", "switch"] else "app_close",
            "action": action,
            "app": app_name,
            "timestamp": time.time(),
            "source": "application_monitor",
        }

        self.event_callback(event)


class SystemResourceMonitor:
    """Monitors system resource usage patterns"""

    def __init__(self, event_callback: Callable[[Dict[str, Any]], None]):
        self.event_callback = event_callback
        self.logger = logging.getLogger("SystemResourceMonitor")

        # Resource tracking
        self.last_cpu_percent = 0
        self.last_memory_percent = 0
        self.last_disk_usage = {}

    async def start_monitoring(self):
        """Start monitoring system resources"""
        if not PSUTIL_AVAILABLE:
            self.logger.warning("psutil not available - resource monitoring disabled")
            return

        self.logger.info("Starting system resource monitoring...")

        while True:
            try:
                await self._check_resources()
                await asyncio.sleep(60)  # Check every minute
            except Exception as e:
                self.logger.error(f"Resource monitoring error: {e}")
                await asyncio.sleep(120)

    async def _check_resources(self):
        """Check system resource usage"""
        try:
            # CPU usage
            cpu_percent = psutil.cpu_percent(interval=1)
            if abs(cpu_percent - self.last_cpu_percent) > 20:  # Significant change
                self._create_resource_event("cpu_usage", cpu_percent)
                self.last_cpu_percent = cpu_percent

            # Memory usage
            memory = psutil.virtual_memory()
            if (
                abs(memory.percent - self.last_memory_percent) > 15
            ):  # Significant change
                self._create_resource_event("memory_usage", memory.percent)
                self.last_memory_percent = memory.percent

            # Disk usage (for main disk only)
            disk = psutil.disk_usage("/")
            disk_percent = (disk.used / disk.total) * 100
            last_disk_percent = self.last_disk_usage.get("/", 0)

            if abs(disk_percent - last_disk_percent) > 5:  # Significant change
                self._create_resource_event("disk_usage", disk_percent)
                self.last_disk_usage["/"] = disk_percent

        except Exception as e:
            self.logger.error(f"Error checking resources: {e}")

    def _create_resource_event(self, resource_type: str, value: float):
        """Create resource usage event"""
        event = {
            "type": "system_maintenance",
            "action": "resource_change",
            "resource": resource_type,
            "value": value,
            "timestamp": time.time(),
            "source": "resource_monitor",
        }

        self.event_callback(event)


class SystemEventCapture:
    """Main system event capture coordinator"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("SystemEventCapture")

        # Event callback
        self.event_callback: Optional[Callable[[Dict[str, Any]], None]] = None

        # Monitoring components
        self.file_observer: Optional[Observer] = None
        self.app_monitor: Optional[ApplicationMonitor] = None
        self.resource_monitor: Optional[SystemResourceMonitor] = None

        # Event statistics
        self.events_captured = 0
        self.start_time = datetime.now()

        # Monitoring paths
        self.watch_paths = config.get(
            "watch_paths",
            [
                str(Path.home()),  # User home directory
                "/Applications",  # Applications folder
            ],
        )

    def set_event_callback(self, callback: Callable[[Dict[str, Any]], None]):
        """Set the callback for captured events"""
        self.event_callback = callback

    async def start_capture(self):
        """Start all event capture systems"""
        if not self.event_callback:
            raise ValueError("Event callback must be set before starting capture")

        self.logger.info("🎯 Starting ALims System Event Capture...")

        # Start file system monitoring
        await self._start_filesystem_monitoring()

        # Start application monitoring
        await self._start_application_monitoring()

        # Start resource monitoring
        await self._start_resource_monitoring()

        self.logger.info("✅ System Event Capture started successfully")

    async def stop_capture(self):
        """Stop all event capture systems"""
        self.logger.info("🛑 Stopping System Event Capture...")

        # Stop file system monitoring
        if self.file_observer:
            self.file_observer.stop()
            self.file_observer.join()

        self.logger.info("✅ System Event Capture stopped")

    async def _start_filesystem_monitoring(self):
        """Start file system event monitoring"""
        if not WATCHDOG_AVAILABLE:
            self.logger.warning(
                "watchdog not available - filesystem monitoring disabled"
            )
            return

        try:
            event_handler = AlimsFileSystemEventHandler(self._handle_event)
            self.file_observer = Observer()

            # Watch specified paths
            for path in self.watch_paths:
                if os.path.exists(path):
                    self.file_observer.schedule(event_handler, path, recursive=True)
                    self.logger.info(f"Watching filesystem path: {path}")

            self.file_observer.start()
            self.logger.info("Filesystem monitoring started")

        except Exception as e:
            self.logger.error(f"Failed to start filesystem monitoring: {e}")

    async def _start_application_monitoring(self):
        """Start application monitoring"""
        try:
            self.app_monitor = ApplicationMonitor(self._handle_event)

            # Start monitoring in background task
            asyncio.create_task(self.app_monitor.start_monitoring())

            self.logger.info("Application monitoring started")

        except Exception as e:
            self.logger.error(f"Failed to start application monitoring: {e}")

    async def _start_resource_monitoring(self):
        """Start system resource monitoring"""
        try:
            self.resource_monitor = SystemResourceMonitor(self._handle_event)

            # Start monitoring in background task
            asyncio.create_task(self.resource_monitor.start_monitoring())

            self.logger.info("Resource monitoring started")

        except Exception as e:
            self.logger.error(f"Failed to start resource monitoring: {e}")

    def _handle_event(self, event: Dict[str, Any]):
        """Handle captured system event"""
        try:
            # Add metadata
            event["capture_time"] = time.time()
            event["event_id"] = f"evt_{self.events_captured}"

            # Update statistics
            self.events_captured += 1

            # Log event (debug level to avoid spam)
            self.logger.debug(
                f"Captured event: {event['type']} - {event.get('action', 'N/A')}"
            )

            # Forward to callback (handle async callbacks properly)
            if self.event_callback:
                try:
                    # If callback is async, schedule it properly
                    import asyncio
                    import inspect

                    if inspect.iscoroutinefunction(self.event_callback):
                        # Create a task to run the async callback
                        try:
                            loop = asyncio.get_event_loop()
                            loop.create_task(self.event_callback(event))
                        except RuntimeError:
                            # No event loop running, skip this event
                            self.logger.debug(
                                "No event loop available for async callback"
                            )
                    else:
                        # Synchronous callback
                        self.event_callback(event)
                except Exception as callback_error:
                    self.logger.error(f"Error in event callback: {callback_error}")

        except Exception as e:
            self.logger.error(f"Error handling event: {e}")

    def get_capture_stats(self) -> Dict[str, Any]:
        """Get event capture statistics"""
        uptime = datetime.now() - self.start_time

        return {
            "events_captured": self.events_captured,
            "uptime": str(uptime),
            "events_per_minute": self.events_captured
            / max(uptime.total_seconds() / 60, 1),
            "filesystem_monitoring": self.file_observer is not None
            and self.file_observer.is_alive(),
            "application_monitoring": self.app_monitor is not None,
            "resource_monitoring": self.resource_monitor is not None,
            "watch_paths": self.watch_paths,
        }
