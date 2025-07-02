#!/usr/bin/env python3
"""
ALims Tauri-Integrated Tray Launcher

Launches the enhanced system tray with beautiful Tauri desktop app integration.
"""

import logging
import sys
from pathlib import Path

# Add the project root to Python path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

from backend.app.system.tauri_integrated_tray import (
    create_tauri_integrated_tray
)


def main():
    """Main launcher function"""
    
    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler('logs/tauri_tray.log'),
            logging.StreamHandler()
        ]
    )
    
    logger = logging.getLogger(__name__)
    logger.info("🧬 Starting ALims Tauri-Integrated Tray...")
    
    try:
        # Create the tray application
        tray_app = create_tauri_integrated_tray()
        
        if tray_app:
            logger.info("✅ Tray application created successfully")
            logger.info("🖥️ Desktop app can be launched from the tray menu")
            logger.info("🧬 ALims tray is now running in your menu bar")
            
            # Run the tray application
            tray_app.run()
        else:
            logger.error("❌ Failed to create tray application")
            sys.exit(1)
            
    except KeyboardInterrupt:
        logger.info("🛑 Tray application stopped by user")
    except Exception as e:
        logger.error(f"❌ Error running tray application: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main() 