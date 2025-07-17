#!/usr/bin/env python3
"""
TLA+ Verified Chat Server Startup Script

Starts the ALIMS chat API server using the formally verified Main Interface Agent.
"""

import os
import sys
import logging
from pathlib import Path

# Add project root to path
ROOT_DIR = Path(__file__).parent.parent.parent
sys.path.insert(0, str(ROOT_DIR))
sys.path.insert(0, str(ROOT_DIR / 'backend'))

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

def start_tla_chat_server():
    """Start the TLA+ verified chat server"""
    try:
        import uvicorn
        
        # Import the TLA+ verified chat API
        from backend.app.intelligence.chat_api import app
        
        logger.info("🚀 Starting TLA+ Verified ALIMS Chat Server...")
        logger.info("📋 Features:")
        logger.info("   ✅ TLA+ Formally Verified Main Interface Agent")
        logger.info("   ✅ Type-safe conversation management")
        logger.info("   ✅ Resource bounds enforcement")
        logger.info("   ✅ Real-time WebSocket support")
        logger.info("   ✅ Safety property guarantees")
        logger.info("")
        logger.info("📡 Server will be available at:")
        logger.info("   🌐 HTTP API: http://localhost:8000")
        logger.info("   🔗 WebSocket: ws://localhost:8000/ws/chat")
        logger.info("   📊 Status: http://localhost:8000/status")
        logger.info("   🏥 Health: http://localhost:8000/health")
        
        # Start the server
        uvicorn.run(
            app,
            host="0.0.0.0",
            port=8000,
            log_level="info",
            reload=False  # Disable reload for production stability
        )
        
    except KeyboardInterrupt:
        logger.info("🛑 Server shutdown requested")
    except Exception as e:
        logger.error(f"❌ Failed to start server: {e}")
        sys.exit(1)

if __name__ == "__main__":
    start_tla_chat_server()
