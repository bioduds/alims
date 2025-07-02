#!/usr/bin/env python3
"""
Launch ALims System Tray

Simple launcher for the ALims system tray app.
Run this in a separate terminal while the main system is running.
"""

import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

try:
    from backend.app.system.macos_tray import create_tray_app
    from backend.app.core.agent_manager import AgentManager

    print("🎭 Launching ALims System Tray...")

    # Create a minimal agent manager for tray integration
    config = {"max_agents": 20}
    agent_manager = AgentManager(config)

    # Create and run tray app
    tray_app = create_tray_app(agent_manager, {})

    if tray_app:
        print("✅ System Tray launched successfully!")
        print("🎯 Look for the ALims icon in your menu bar")
        tray_app.run()
    else:
        print("❌ Failed to create tray app (rumps not installed?)")

except ImportError as e:
    print(f"❌ Import error: {e}")
    print("💡 Make sure you're in the virtual environment:")
    print("   source alims_env/bin/activate")
except Exception as e:
    print(f"❌ Error launching tray: {e}")
