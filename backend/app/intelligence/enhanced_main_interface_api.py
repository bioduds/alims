"""
Enhanced Main Interface Agent FastAPI Application
Standalone FastAPI server for the TLA+ validated Main Interface Agent system.
"""

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
import logging
import uvicorn
import asyncio

from enhanced_api import router as enhanced_router
from enhanced_main_interface_service import EnhancedLIMSMainInterfaceService

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)

logger = logging.getLogger(__name__)

# Create FastAPI app
app = FastAPI(
    title="ALIMS Enhanced Main Interface Agent API",
    description="TLA+ validated central orchestration API for LIMS conversations and agent management",
    version="2.0.0"
)

# Add CORS middleware for Tauri frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "tauri://localhost", 
        "http://localhost:1420", 
        "http://127.0.0.1:1420",
        "http://localhost:3000",  # Development frontend
        "http://localhost:8080"   # Alternative development port
    ],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include enhanced router
app.include_router(enhanced_router)

# Include legacy compatibility router
from enhanced_api import legacy_router
app.include_router(legacy_router)

# Root endpoint
@app.get("/")
async def root():
    """Root endpoint with API information."""
    return {
        "name": "ALIMS Enhanced Main Interface Agent API",
        "version": "2.0.0",
        "status": "running",
        "architecture": "TLA+ validated",
        "features": [
            "Formal verification guarantees",
            "PredicateLogic-style logical reasoning",
            "Robust error handling and recovery",
            "Comprehensive audit trails",
            "Resource monitoring and optimization"
        ],
        "docs_url": "/docs",
        "enhanced_api_prefix": "/enhanced-intelligence"
    }

@app.get("/health")
async def health_check():
    """Health check endpoint."""
    try:
        # Import here to avoid circular imports
        from enhanced_api import enhanced_service
        
        if enhanced_service and enhanced_service.is_initialized():
            status = await enhanced_service.get_system_status()
            return {
                "status": "healthy",
                "agent_system": status.get("status", "unknown"),
                "active_conversations": status.get("active_conversations", 0),
                "registered_agents": status.get("registered_agents", 0)
            }
        else:
            return {
                "status": "initializing",
                "agent_system": "not_ready",
                "message": "Enhanced agent system is starting up"
            }
    except Exception as e:
        logger.error(f"Health check failed: {e}")
        return {
            "status": "unhealthy",
            "error": str(e)
        }

@app.on_event("startup")
async def startup_event():
    """Initialize the enhanced agent system on startup."""
    logger.info("Starting Enhanced Main Interface Agent API...")
    
    # Initialize with default configuration
    config = {
        'max_conversations': 100,
        'max_agents': 20,
        'max_queries': 500,
        'query_timeout': 30.0,
        'agent_timeout': 60.0,
        'enable_audit': True,
        'enable_monitoring': True
    }
    
    try:
        # Import and initialize here to avoid issues
        from enhanced_api import initialize_enhanced_service
        await initialize_enhanced_service(config)
        logger.info("Enhanced agent system initialized successfully")
    except Exception as e:
        logger.error(f"Failed to initialize enhanced agent system: {e}")
        # Don't fail startup, allow system to start and initialize on first request

@app.on_event("shutdown")
async def shutdown_event():
    """Shutdown the enhanced agent system."""
    logger.info("Shutting down Enhanced Main Interface Agent API...")
    
    try:
        from enhanced_api import enhanced_service
        if enhanced_service:
            await enhanced_service.shutdown()
        logger.info("Enhanced agent system shutdown completed")
    except Exception as e:
        logger.error(f"Error during shutdown: {e}")

# Error handlers
@app.exception_handler(HTTPException)
async def http_exception_handler(request, exc):
    """Handle HTTP exceptions with detailed logging."""
    logger.error(f"HTTP {exc.status_code}: {exc.detail} - Path: {request.url.path}")
    return {"error": exc.detail, "status_code": exc.status_code}

@app.exception_handler(Exception)
async def general_exception_handler(request, exc):
    """Handle general exceptions."""
    logger.error(f"Unhandled exception: {exc} - Path: {request.url.path}")
    return {"error": "Internal server error", "status_code": 500}

if __name__ == "__main__":
    """Run the enhanced API server directly."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Enhanced ALIMS Main Interface Agent API")
    parser.add_argument("--host", default="127.0.0.1", help="Host to bind to")
    parser.add_argument("--port", type=int, default=8001, help="Port to bind to")
    parser.add_argument("--reload", action="store_true", help="Enable auto-reload")
    parser.add_argument("--debug", action="store_true", help="Enable debug mode")
    
    args = parser.parse_args()
    
    if args.debug:
        logging.getLogger().setLevel(logging.DEBUG)
    
    print(f"Starting Enhanced ALIMS Main Interface Agent API...")
    print(f"Server will be available at: http://{args.host}:{args.port}")
    print(f"API documentation: http://{args.host}:{args.port}/docs")
    print(f"Enhanced endpoints: http://{args.host}:{args.port}/enhanced-intelligence")
    
    uvicorn.run(
        "enhanced_main_interface_api:app",
        host=args.host,
        port=args.port,
        reload=args.reload,
        log_level="info" if not args.debug else "debug"
    )
