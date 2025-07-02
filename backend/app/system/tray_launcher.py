#!/usr/bin/env python3
"""
ALims Tray App Launcher

Runs the macOS system tray app on the main thread while keeping
the core ALims system running in the background.
"""

import asyncio
import threading
import logging
from typing import Dict, Any, Optional

from app.system.macos_tray import create_tray_app, EnhancedAlimsTrayApp
from app.system.system_integration import ALimsSystemIntegration


class TrayLauncher:
    """
    Launches ALims with proper thread management for macOS tray integration
    """

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.logger = logging.getLogger("TrayLauncher")

        # System components
        self.system_integration: Optional[ALimsSystemIntegration] = None
        self.tray_app: Optional[EnhancedAlimsTrayApp] = None

        # Threading
        self.system_thread: Optional[threading.Thread] = None
        self.system_ready = threading.Event()

    def run(self):
        """Run ALims with tray app on main thread"""
        try:
            self.logger.info("🚀 Starting ALims with Tray Integration...")

            # Start the core system in a background thread
            self._start_system_thread()

            # Wait for system to be ready
            self.logger.info("⏳ Waiting for core system to initialize...")
            if not self.system_ready.wait(timeout=30):
                self.logger.error("❌ System initialization timeout")
                return

            self.logger.info("✅ Core system ready, starting tray app...")

            # Create and run tray app on main thread
            system_ready = (
                self.system_integration and self.system_integration.agent_manager
            )
            if system_ready:
                self.tray_app = create_tray_app(
                    self.system_integration.agent_manager,
                    self.config.get("tray_app", {}),
                )

                if self.tray_app:
                    self.logger.info("🎯 Starting macOS system tray...")
                    # This runs on the main thread and blocks
                    self.tray_app.run()
                else:
                    self.logger.error("❌ Failed to create tray app")
            else:
                self.logger.error("❌ System integration not ready")

        except KeyboardInterrupt:
            self.logger.info("🛑 Tray launcher interrupted")
        except Exception as e:
            self.logger.error(f"❌ Tray launcher error: {e}")
        finally:
            self._cleanup()

    def _start_system_thread(self):
        """Start the core ALims system in a background thread"""

        def run_system():
            try:
                # Create system integration
                self.system_integration = ALimsSystemIntegration(self.config)

                # Run the async system
                asyncio.run(self._run_system_async())

            except Exception as e:
                self.logger.error(f"System thread error: {e}")

        self.system_thread = threading.Thread(
            target=run_system, daemon=True, name="ALimsSystem"
        )
        self.system_thread.start()

    async def _run_system_async(self):
        """Run the async system components"""
        try:
            # Initialize system
            if await self.system_integration.initialize():
                self.logger.info("✅ System initialized successfully")

                # Signal that system is ready
                self.system_ready.set()

                # Start the system (this will run the main loop)
                await self.system_integration.start()
            else:
                self.logger.error("❌ System initialization failed")

        except Exception as e:
            self.logger.error(f"Async system error: {e}")

    def _cleanup(self):
        """Clean up resources"""
        self.logger.info("🧹 Cleaning up...")

        if self.system_integration:
            # Run cleanup in a new event loop since main loop might be closed
            try:
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                loop.run_until_complete(self.system_integration.shutdown())
                loop.close()
            except Exception as e:
                self.logger.error(f"Cleanup error: {e}")


def run_alims_with_tray(config: Dict[str, Any]):
    """
    Main entry point for running ALims with tray integration
    """
    launcher = TrayLauncher(config)
    launcher.run()


if __name__ == "__main__":
    # Example configuration
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
        "event_capture": {"watch_paths": ["/Users/capanema", "/Applications"]},
        "tray_app": {},
    }

    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    run_alims_with_tray(config)
