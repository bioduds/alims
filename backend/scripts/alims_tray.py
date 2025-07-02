#!/usr/bin/env python3
"""
ALims with macOS System Tray Integration

This launcher runs ALims with full macOS system tray integration.
The tray app runs on the main thread while the core system runs in background.
"""

import logging
import sys
import os

# Add the project root to Python path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Import after path setup
from app.system.tray_launcher import run_alims_with_tray


def main():
    """Main entry point for ALims with tray integration"""

    # Setup logging
    log_format = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    logging.basicConfig(
        level=logging.INFO,
        format=log_format,
        handlers=[logging.StreamHandler(), logging.FileHandler("alims_tray.log")],
    )

    logger = logging.getLogger("AlimsTrayMain")
    logger.info("🚀 Starting ALims with macOS Tray Integration")

    # Configuration
    config = {
        "embryo_pool": {
            "max_embryos": 30,
            "mutation_rate": 0.1,
            "competition_intensity": 0.8,
            "fitness_threshold": 0.7,
        },
        "agent_manager": {
            "max_agents": 5,
            "birth_threshold": 0.7,
            "retirement_threshold": 0.3,
        },
        "event_capture": {
            "watch_paths": [
                os.path.expanduser("~"),  # User home directory
                "/Applications",
            ],
            "ignore_patterns": [
                "*.DS_Store",
                "*.cache",
                "__pycache__",
                ".git",
                "node_modules",
                ".vscode",
            ],
        },
        "agent_interface": {"max_sessions": 10, "session_timeout": 3600},  # 1 hour
        "tray_app": {"phase_duration_weeks": 4, "notification_enabled": True},
        "system_integration": {"health_check_interval": 30, "log_level": "INFO"},
    }

    try:
        # Run ALims with tray integration
        run_alims_with_tray(config)

    except KeyboardInterrupt:
        logger.info("🛑 ALims interrupted by user")
    except Exception as e:
        logger.error(f"❌ ALims error: {e}")
        raise
    finally:
        logger.info("👋 ALims shutdown complete")


if __name__ == "__main__":
    main()
