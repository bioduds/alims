"""
Main Interface Agent FastAPI Application

Standalone FastAPI server for the Main Interface Agent that can be used
by the Tauri frontend to interact with the LIMS conversation system.
"""

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
import logging
import uvicorn

from main_interface_router import router as interface_router

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)

logger = logging.getLogger(__name__)

# Create FastAPI app
app = FastAPI(
    title="ALIMS Main Interface Agent API",
    description="Central orchestration API for LIMS conversations and agent management",
    version="1.0.0"
)

# Add CORS middleware for Tauri frontend
app.add_middleware(
    CORSMiddleware,
    allow_origins=["tauri://localhost", "http://localhost:1420", "http://127.0.0.1:1420"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Include routers
app.include_router(interface_router)

# Root endpoint
@app.get("/")
async def root():
    """Root endpoint with API information."""
    return {
        "name": "ALIMS Main Interface Agent API",
        "version": "1.0.0",
        "status": "running",
        "docs_url": "/docs"
    }

# Health check
@app.get("/health")
async def health():
    """Simple health check."""
    return {"status": "healthy"}

if __name__ == "__main__":
    uvicorn.run(
        "app.intelligence.main_interface_api:app",
        host="127.0.0.1",
        port=8001,
        reload=True,
        log_level="info"
    )
