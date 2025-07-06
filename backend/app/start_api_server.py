"""
Start the FastAPI server for the Main Interface Agent API
"""

import os
import sys
import uvicorn
from pathlib import Path

def main():
    # Add backend path to PYTHONPATH
    backend_path = str(Path(__file__).parent.parent)
    sys.path.append(backend_path)
    
    # Start FastAPI server
    uvicorn.run(
        "app.intelligence.main_interface_api:app",
        host="127.0.0.1",
        port=3000,
        reload=True,  # Enable auto-reload during development
        log_level="info"
    )

if __name__ == "__main__":
    main()
