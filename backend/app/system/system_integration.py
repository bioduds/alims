#!/usr/bin/env python3
"""
ALims System Integration - Phase 3

Main coordinator for macOS system integration:
- Orchestrates tray app, event capture, and agent interfaces
- Manages system permissions and security
- Handles graceful startup and shutdown
- Provides unified system status and control
"""

import asyncio
import logging
import signal
import sys
import os
from typing import Dict, List, Optional, Any
from datetime import datetime
from pathlib import Path

from ..core.agent_manager import AgentManager
from ..core.embryo_pool import EmbryoPool
from .macos_tray import create_macos_tray, MacOSTray
from .event_capture import SystemEventCapture
from .high_performance_capture import HighPerformanceEventCapture
from .agent_interface import create_agent_interface, AgentChatInterface
from .permissions import check_system_permissions, request_permissions


class ALimsSystemIntegration:
    """
    Central integration hub for the ALims system.
    
    This class coordinates all major system components:
    - Event capture and processing
    - Agent management and lifecycle
    - AI brain and learning systems
    - System monitoring and health checks
    - Tray integration and user interface
    """

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("ALimsSystem")

        # Core components
        self.embryo_pool: Optional[EmbryoPool] = None
        self.agent_manager: Optional[AgentManager] = None

        # System integration components
        self.tray_app: Optional[MacOSTray] = None
        self.event_capture: Optional[SystemEventCapture] = None
        self.agent_interface: Optional[AgentChatInterface] = None

        # System state
        self.is_running = False
        self.start_time: Optional[datetime] = None
        self.shutdown_requested = False

        # Setup signal handlers
        self._setup_signal_handlers()

    def _setup_signal_handlers(self):
        """Setup graceful shutdown signal handlers"""
        try:

            def signal_handler(signum, frame):
                self.logger.info(
                    f"Received signal {signum}, initiating graceful shutdown..."
                )
                self.shutdown_requested = True

            signal.signal(signal.SIGINT, signal_handler)
            signal.signal(signal.SIGTERM, signal_handler)
        except ValueError as e:
            # Signal handlers can only be set in main thread
            self.logger.debug(f"Signal handlers not set (not main thread): {e}")

    async def initialize(self) -> bool:
        """Initialize all system components"""
        try:
            self.logger.info("🚀 Initializing ALims System Integration...")

            # Check system permissions
            if not await self._check_permissions():
                self.logger.error("❌ Required system permissions not available")
                return False

            # Initialize core components
            if not await self._initialize_core_components():
                self.logger.error("❌ Failed to initialize core components")
                return False

            # Initialize system integration components
            if not await self._initialize_system_components():
                self.logger.error("❌ Failed to initialize system components")
                return False

            self.logger.info("✅ ALims System Integration initialized successfully")
            return True

        except Exception as e:
            self.logger.error(f"❌ System initialization failed: {e}")
            return False

    async def start(self):
        """Start the ALims system"""
        try:
            if self.is_running:
                self.logger.warning("System is already running")
                return

            self.logger.info("🎯 Starting ALims System...")
            self.start_time = datetime.now()

            # Start core components
            await self._start_core_components()

            # Start system integration components
            await self._start_system_components()

            self.is_running = True
            self.logger.info("✅ ALims System started successfully")

            # Run main loop
            await self._run_main_loop()

        except Exception as e:
            self.logger.error(f"❌ System startup failed: {e}")
            await self.shutdown()

    async def shutdown(self):
        """Gracefully shutdown the ALims system"""
        try:
            if not self.is_running:
                return

            self.logger.info("🛑 Shutting down ALims System...")
            self.is_running = False

            # Stop system integration components
            await self._stop_system_components()

            # Stop core components
            await self._stop_core_components()

            uptime = datetime.now() - self.start_time if self.start_time else None
            self.logger.info(f"✅ ALims System shutdown complete. Uptime: {uptime}")

        except Exception as e:
            self.logger.error(f"❌ Error during shutdown: {e}")

    async def _check_permissions(self) -> bool:
        """Check and request necessary system permissions"""
        try:
            self.logger.info("🔐 Checking system permissions...")

            # Check current permissions
            permissions = check_system_permissions()

            missing_permissions = []
            if not permissions.get("accessibility", False):
                missing_permissions.append("accessibility")
            if not permissions.get("full_disk_access", False):
                missing_permissions.append("full_disk_access")

            if missing_permissions:
                self.logger.warning(f"Missing permissions: {missing_permissions}")

                # Request permissions
                if await request_permissions(missing_permissions):
                    self.logger.info("✅ Permissions granted")
                    return True
                else:
                    self.logger.error("❌ Required permissions denied")
                    return False

            self.logger.info("✅ All required permissions available")
            return True

        except Exception as e:
            self.logger.error(f"Error checking permissions: {e}")
            return False

    async def _initialize_core_components(self) -> bool:
        """Initialize core ALims components"""
        try:
            self.logger.info("Initializing core components...")

            # Initialize agent manager (which creates its own embryo pool)
            agent_config = self.config.get("agent_manager", {})
            # Merge embryo pool config into agent manager config
            agent_config.update(self.config.get("embryo_pool", {}))

            self.agent_manager = AgentManager(agent_config)

            # Get reference to the embryo pool from agent manager
            self.embryo_pool = self.agent_manager.embryo_pool

            self.logger.info("✅ Core components initialized")
            return True

        except Exception as e:
            self.logger.error(f"Error initializing core components: {e}")
            return False

    async def _initialize_system_components(self) -> bool:
        """Initialize system integration components"""
        try:
            self.logger.info("Initializing system integration components...")

            # Initialize high-performance event capture with persistence
            use_hp_capture = self.config.get("use_high_performance", True)
            if use_hp_capture:
                capture_config = self.config.get("event_capture", {})
                # Enable persistence by default
                capture_config.setdefault("enable_persistence", True)
                capture_config.setdefault(
                    "persistence",
                    {
                        "database_path": "data/events.db",
                        "batch_size": 100,
                        "batch_timeout": 5.0,
                        "retention_days": 30,
                        "cleanup_interval_hours": 24,
                    },
                )

                self.event_capture = HighPerformanceEventCapture(capture_config)
                self.logger.info(
                    "Using High-Performance Event Capture with Persistence"
                )
            else:
                self.event_capture = SystemEventCapture(
                    self.config.get("event_capture", {})
                )

            # Initialize agent interface
            self.agent_interface = create_agent_interface(self.agent_manager)

            # Initialize tray app
            self.tray_app = create_macos_tray(
                self.agent_manager, self.config.get("tray_app", {})
            )

            if not self.tray_app:
                self.logger.warning("⚠️ Tray app not available (rumps not installed)")

            self.logger.info("✅ System integration components initialized")
            return True

        except Exception as e:
            self.logger.error(f"Error initializing system components: {e}")
            return False

    async def _start_core_components(self):
        """Start core ALims components"""
        try:
            self.logger.info("Starting core components...")

            # Start embryo pool first (managed by system integration)
            await self.embryo_pool.start()

            # Start agent manager WITHOUT starting its embryo pool
            # (since we're managing it at the system level)
            await self.agent_manager.start_without_embryo_pool()

            self.logger.info("✅ Core components started")

        except Exception as e:
            self.logger.error(f"Error starting core components: {e}")
            raise

    async def _start_system_components(self):
        """Start system integration components"""
        try:
            self.logger.info("Starting system integration components...")

            # Connect event capture to embryo pool
            # Use sync wrapper for high-performance capture
            if hasattr(self.embryo_pool, "process_event_sync"):
                self.event_capture.set_event_callback(
                    self.embryo_pool.process_event_sync
                )
            else:
                self.event_capture.set_event_callback(self.embryo_pool.process_event)

            # Start event capture
            await self.event_capture.start_capture()

            # Start tray app (if available)
            if self.tray_app:
                try:
                    # Note: Tray app should be started on main thread
                    # For now, we'll log that it's available but needs main thread
                    self.logger.info("🎯 Tray app initialized and ready")
                    tray_msg = (
                        "💡 Use 'python alims_tray.py' for full tray integration"
                    )
                    self.logger.info(tray_msg)
                except Exception as e:
                    self.logger.warning(f"⚠️ Tray app initialization issue: {e}")
            else:
                self.logger.info("⚠️ Tray app not available (rumps not installed)")

            self.logger.info("✅ System integration components started")

        except Exception as e:
            self.logger.error(f"Error starting system components: {e}")
            raise

    async def _stop_core_components(self):
        """Stop core ALims components"""
        try:
            self.logger.info("Stopping core components...")

            if self.agent_manager:
                await self.agent_manager.stop()

            if self.embryo_pool:
                await self.embryo_pool.stop()

            self.logger.info("✅ Core components stopped")

        except Exception as e:
            self.logger.error(f"Error stopping core components: {e}")

    async def _stop_system_components(self):
        """Stop system integration components"""
        try:
            self.logger.info("Stopping system integration components...")

            if self.event_capture:
                await self.event_capture.stop_capture()

            # Tray app will stop when main process exits

            self.logger.info("✅ System integration components stopped")

        except Exception as e:
            self.logger.error(f"Error stopping system components: {e}")

    async def _run_main_loop(self):
        """Main system loop"""
        self.logger.info("🔄 Entering main system loop...")

        try:
            while self.is_running and not self.shutdown_requested:
                # Perform periodic system maintenance
                await self._system_maintenance()

                # Sleep for a bit
                await asyncio.sleep(30)  # Check every 30 seconds

        except Exception as e:
            self.logger.error(f"Error in main loop: {e}")

        self.logger.info("🔄 Exiting main system loop")

    async def _system_maintenance(self):
        """Perform periodic system maintenance"""
        try:
            # Check system health
            await self._check_system_health()

            # Log system statistics periodically
            if hasattr(self, "_last_stats_log"):
                time_since_last = datetime.now() - self._last_stats_log
                if time_since_last.total_seconds() > 300:  # Every 5 minutes
                    await self._log_system_stats()
            else:
                await self._log_system_stats()

        except Exception as e:
            self.logger.error(f"Error in system maintenance: {e}")

    async def _check_system_health(self):
        """Check overall system health"""
        try:
            # Check if core components are running
            if not self.embryo_pool or not self.agent_manager:
                self.logger.warning("⚠️ Core components not running")
                return

            # Check embryo pool health (use sync method)
            pool_status = self.embryo_pool.get_pool_status()
            if pool_status.get("active_embryos", 0) == 0:
                self.logger.debug("No active embryos - system learning")

            # Check agent manager health
            system_status = await self.agent_manager.get_system_status()
            if system_status.get("system", {}).get("active_agents", 0) == 0:
                self.logger.debug("No active agents - waiting for births")

        except Exception as e:
            self.logger.error(f"Error checking system health: {e}")

    async def _log_system_stats(self):
        """Log system statistics"""
        try:
            # Get system status
            if self.agent_manager:
                status = await self.agent_manager.get_system_status()
                system_info = status.get("system", {})
                embryo_info = status.get("embryo_pool", {})

                self.logger.info(
                    f"📊 System Stats - Agents: {system_info.get('active_agents', 0)}, "
                    f"Embryos: {embryo_info.get('active_embryos', 0)}, "
                    f"Events: {embryo_info.get('events_processed', 0)}"
                )

            # Get event capture stats
            if self.event_capture:
                capture_stats = self.event_capture.get_capture_stats()
                self.logger.info(
                    f"📊 Event Capture - Events: {capture_stats.get('events_captured', 0)}, "
                    f"Rate: {capture_stats.get('events_per_minute', 0):.1f}/min"
                )

            self._last_stats_log = datetime.now()

        except Exception as e:
            self.logger.error(f"Error logging system stats: {e}")

    async def get_system_status(self) -> Dict[str, Any]:
        """Get comprehensive system status"""
        try:
            status = {
                "system_integration": {
                    "is_running": self.is_running,
                    "start_time": (
                        self.start_time.isoformat() if self.start_time else None
                    ),
                    "uptime": (
                        str(datetime.now() - self.start_time)
                        if self.start_time
                        else None
                    ),
                    "components": {
                        "embryo_pool": self.embryo_pool is not None,
                        "agent_manager": self.agent_manager is not None,
                        "event_capture": self.event_capture is not None,
                        "agent_interface": self.agent_interface is not None,
                        "tray_app": self.tray_app is not None,
                    },
                }
            }

            # Add core system status
            if self.agent_manager:
                core_status = await self.agent_manager.get_system_status()
                status.update(core_status)

            # Add event capture stats
            if self.event_capture:
                status["event_capture"] = self.event_capture.get_capture_stats()

            return status

        except Exception as e:
            self.logger.error(f"Error getting system status: {e}")
            return {"error": str(e)}

    async def chat_with_agents(
        self, message: str, session_id: str = None
    ) -> Dict[str, Any]:
        """Chat with agents through the interface"""
        try:
            if not self.agent_interface:
                return {"error": "Agent interface not available"}

            # Start session if needed
            if not session_id:
                session_id = await self.agent_interface.start_chat_session()

            # Create user message
            from .agent_interface import UserMessage, InteractionType

            user_message = UserMessage(
                content=message, message_type=InteractionType.CHAT
            )

            # Send message and get response
            response = await self.agent_interface.send_message(session_id, user_message)

            return {
                "session_id": session_id,
                "response": {
                    "content": response.content,
                    "agent_name": response.agent_name,
                    "specialization": response.agent_specialization,
                    "confidence": response.confidence,
                    "suggested_actions": response.suggested_actions,
                },
            }

        except Exception as e:
            self.logger.error(f"Error in chat: {e}")
            return {"error": str(e)}


async def main():
    """Main entry point for ALims system integration"""
    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    logger = logging.getLogger("ALimsMain")
    logger.info("🚀 Starting ALims - The Self-Creating AI Operating System")

    # Load configuration
    config = {
        "embryo_pool": {
            "max_embryos": 15,
            "mutation_rate": 0.1,
            "competition_intensity": 0.8,
        },
        "agent_manager": {
            "max_agents": 5,
            "birth_threshold": 0.7,
            "retirement_threshold": 0.3,
        },
        "event_capture": {"watch_paths": [str(Path.home()), "/Applications"]},
        "tray_app": {},
    }

    # Create and run system
    system = ALimsSystemIntegration(config)

    try:
        # Initialize system
        if await system.initialize():
            # Start system
            await system.start()
        else:
            logger.error("❌ System initialization failed")
            sys.exit(1)

    except KeyboardInterrupt:
        logger.info("🛑 Keyboard interrupt received")
    except Exception as e:
        logger.error(f"❌ System error: {e}")
    finally:
        # Ensure clean shutdown
        await system.shutdown()
        logger.info("👋 ALims shutdown complete")


if __name__ == "__main__":
    asyncio.run(main())
