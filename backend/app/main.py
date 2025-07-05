#!/usr/bin/env python3
"""
ALIMS - Agentic Laboratory Information Management System

The main entry point for the ALIMS system.
This module coordinates all laboratory management components including:
- Sample tracking and lifecycle management  
- Agentic laboratory workflow automation
- Intelligent instrument data integration
- AI-powered quality control and compliance
- Multi-agent protocol management and validation
"""

import asyncio
import logging
import signal
import sys
from pathlib import Path
from typing import Optional

from .core.sample_manager import SampleManager
from .core.laboratory_workflow import LaboratoryWorkflow
from .system.permissions import PermissionManager
from .system.lims_interface import LIMSInterface
from .intelligence.main_interface_service import LIMSMainInterfaceService


class ALIMSApp:
    """
    Main ALIMS application that coordinates all agentic laboratory management components.

    This is the central orchestrator that manages:
    - Sample lifecycle and tracking with AI agents
    - Agentic laboratory workflow automation
    - Intelligent instrument data integration
    - AI-powered quality control processes  
    - Multi-agent protocol management and compliance
    """

    def __init__(self):
        self.logger = logging.getLogger("ALIMSApp")
        self.running = False

        # Core LIMS components
        self.sample_manager: Optional[SampleManager] = None
        self.laboratory_workflow: Optional[LaboratoryWorkflow] = None
        self.permission_manager: Optional[PermissionManager] = None
        self.lims_interface: Optional[LIMSInterface] = None
        self.main_interface_service: Optional[LIMSMainInterfaceService] = None

        # LIMS Configuration
        self.config = {
            'max_samples': 1000,
            'data_retention_days': 2555,  # 7 years for regulatory compliance
            'compliance_mode': 'FDA_21CFR11',
            'enable_interface': True,
            'log_level': 'INFO'
        }

        # Setup signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

    async def initialize(self):
        """Initialize all ALIMS components"""
        try:
            self.logger.info("Initializing ALIMS...")

            # Initialize permission manager first
            self.permission_manager = PermissionManager()
            if not await self.permission_manager.request_permissions():
                self.logger.error("Failed to obtain required permissions")
                return False

            # Initialize sample manager
            self.sample_manager = SampleManager(
                max_samples=self.config['max_samples'],
                retention_days=self.config['data_retention_days']
            )

            # Initialize laboratory workflow engine
            self.laboratory_workflow = LaboratoryWorkflowEngine(self.config)

            # Initialize LIMS interface
            if self.config['enable_interface']:
                self.lims_interface = LIMSInterface(
                    self.sample_manager,
                    self.laboratory_workflow,
                    self.config
                )
                await self.lims_interface.initialize()

            # Initialize enhanced main interface service (TLA+ validated)
            from .intelligence.enhanced_main_interface_service import EnhancedLIMSMainInterfaceService
            self.main_interface_service = EnhancedLIMSMainInterfaceService(
                self.config)
            await self.main_interface_service.initialize()

            self.logger.info("ALIMS initialization complete")
            return True

        except Exception as e:
            self.logger.error(f"Failed to initialize ALIMS: {e}")
            return False

    async def start(self):
        """Start the ALIMS system"""
        try:
            if not await self.initialize():
                return False

            self.running = True
            self.logger.info("Starting ALIMS system...")

            # Start core LIMS components
            if self.laboratory_workflow:
                # Workflow engine starts automatically

                # Show interface notification
            if self.lims_interface:
                await self.lims_interface._add_notification(
                    "success", "ALIMS Started", "Laboratory Information Management System is now active"
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
        if self.sample_manager and not self.sample_manager.is_healthy():
            self.logger.warning("Sample manager health check failed")

        if self.laboratory_workflow and not self.laboratory_workflow.is_healthy():
            self.logger.warning("Laboratory workflow health check failed")

        if self.lims_interface and not self.lims_interface.is_healthy():
            self.logger.warning("LIMS interface health check failed")

        if self.main_interface_service and not self.main_interface_service.is_healthy():
            self.logger.warning("Main interface service health check failed")

    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully"""
        self.logger.info(f"Received signal {signum}, shutting down...")
        self.running = False

    async def stop(self):
        """Stop the ALIMS system gracefully"""
        self.logger.info("Shutting down ALIMS...")
        self.running = False

        # Stop components in reverse order
        if self.lims_interface:
            await self.lims_interface.cleanup()

        if self.main_interface_service:
            await self.main_interface_service.cleanup()

        if self.laboratory_workflow:
            # Workflow engine cleanup if needed
            pass

        if self.sample_manager:
            # Sample manager cleanup if needed
            pass

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
