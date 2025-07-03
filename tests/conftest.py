"""Test configuration for LIMS tests."""

import sys
from pathlib import Path

# Add the backend/app directory to Python path so we can import lims modules
backend_app_path = Path(__file__).parent.parent / "backend" / "app"
sys.path.insert(0, str(backend_app_path))
