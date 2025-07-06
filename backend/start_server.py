#!/usr/bin/env python3

import os
import sys
import uvicorn
from pathlib import Path

# Add project root to path
ROOT_DIR = Path(__file__).parent.parent
sys.path.insert(0, str(ROOT_DIR))
sys.path.insert(0, str(ROOT_DIR / 'backend'))

# Import after path setup
from main_interface_standalone import app

if __name__ == "__main__":
    try:
        print("Starting ALIMS Main Interface Agent API...")
        print(f"Python path: {sys.path}")
        uvicorn.run(
            app,
            host="127.0.0.1",  # Only allow local connections
            port=8001,
            log_level="info"
        )
    except Exception as e:
        print(f"Failed to start server: {e}", file=sys.stderr)
        sys.exit(1)
