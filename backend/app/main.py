#!/usr/bin/env python3
"""
ALims - Self-Evolving AI Operating System Layer

The main entry point for the ALims system.
This module coordinates all system components including:
- Event capture and monitoring
- Agent management and evolution
- Pattern detection and learning
- System tray integration
- Privacy-first data handling
"""

import asyncio
import logging
import signal
import sys
from pathlib import Path
from typing import Optional

from backend.app.core.data_stream import DataStreamMonitor
from backend.app.core.embryo_pool import EmbryoPool
from backend.app.system.permissions import PermissionManager
from backend.app.system.tray_icon import AlimsTrayIcon


class AlimsApp:
    """
    Main ALIMS application that coordinates all components.

    This is the central orchestrator that manages:
    - System initialization and shutdown
    - Component lifecycle management
    - Inter-component communication
    - Error handling and recovery
    """

    def __init__(self):
        self.logger = logging.getLogger("AlimsApp")
        self.running = False

        # Core components
        self.embryo_pool: Optional[EmbryoPool] = None
        self.data_stream: Optional[DataStreamMonitor] = None
        self.permission_manager: Optional[PermissionManager] = None
        self.tray_icon: Optional[AlimsTrayIcon] = None

        # Configuration
        self.config = {
            'max_embryos': 15,
            'data_buffer_limit_mb': 10.0,
            'privacy_mode': True,
            'enable_tray': True,
            'log_level': 'INFO'
        }

        # Setup signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

    async def initialize(self):
        """Initialize all ALims components"""
        try:
            self.logger.info("Initializing ALIMS...")

            # Initialize permission manager first
            self.permission_manager = PermissionManager()
            if not await self.permission_manager.request_permissions():
                self.logger.error("Failed to obtain required permissions")
                return False

            # Initialize embryo pool
            self.embryo_pool = EmbryoPool(
                max_embryos=self.config['max_embryos'],
                data_buffer_limit_mb=self.config['data_buffer_limit_mb']
            )

            # Initialize data stream monitor
            self.data_stream = DataStreamMonitor(
                embryo_pool=self.embryo_pool,
                privacy_mode=self.config['privacy_mode']
            )

            # Initialize system tray if enabled
            if self.config['enable_tray']:
                self.tray_icon = AlimsTrayIcon()
                await self.tray_icon.initialize()

            self.logger.info("ALIMS initialization complete")
            return True

        except Exception as e:
            self.logger.error(f"Failed to initialize ALims: {e}")
            return False

    async def start(self):
        """Start the ALIMS system"""
        try:
            if not await self.initialize():
                return False

            self.running = True
            self.logger.info("Starting ALIMS system...")

            # Start core components
            if self.data_stream:
                await self.data_stream.start()

            if self.embryo_pool:
                await self.embryo_pool.start()

            # Show system tray notification
            if self.tray_icon:
                await self.tray_icon.show_notification(
                    "ALIMS Started", "AI Operating System is now active"
                )

            self.logger.info("ALIMS system started successfully")

            # Run main loop
            await self._main_loop()

        except Exception as e:
            self.logger.error(f"Error starting ALIMS: {e}")
            return False

    async def _main_loop(self):
        """Main application loop"""
        while self.running:
            try:
                # Monitor system health
                await self._health_check()

                # Brief sleep to prevent CPU spinning
                await asyncio.sleep(1)

            except Exception as e:
                self.logger.error(f"Error in main loop: {e}")
                await asyncio.sleep(5)

    async def _health_check(self):
        """Perform system health checks"""
        # Check component health
        if self.embryo_pool and not self.embryo_pool.is_healthy():
            self.logger.warning("Embryo pool health check failed")

        if self.data_stream and not self.data_stream.is_healthy():
            self.logger.warning("Data stream health check failed")

    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully"""
        self.logger.info(f"Received signal {signum}, shutting down...")
        self.running = False

    async def stop(self):
        """Stop the ALIMS system gracefully"""
        self.logger.info("Shutting down ALIMS...")
        self.running = False

        # Stop components in reverse order
        if self.tray_icon:
            await self.tray_icon.cleanup()

        if self.data_stream:
            await self.data_stream.stop()

        if self.embryo_pool:
            await self.embryo_pool.stop()

        self.logger.info("ALIMS shutdown complete")


def setup_logging(level: str = 'INFO'):
    """Setup logging configuration"""
    logging.basicConfig(
        level=getattr(logging, level.upper()),
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        handlers=[logging.FileHandler("logs/alims.log"), logging.StreamHandler()],
    )


async def main():
    """Main entry point"""
    setup_logging()

    app = AlimsApp()

    try:
        await app.start()
    except KeyboardInterrupt:
        logging.info("Received keyboard interrupt")
    except Exception as e:
        logging.error(f"Application error: {e}")
    finally:
        await app.stop()


if __name__ == "__main__":
    asyncio.run(main()) 
