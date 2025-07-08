#!/bin/bash

# Launch script for ALIMS Main Interface Agent API
# This script starts the FastAPI server for the Main Interface Agent

echo "🚀 Starting ALIMS Main Interface Agent API..."

# Set the Python path to include the implementation
export PYTHONPATH="${PYTHONPATH}:$(pwd)/plans/feature-2025010301-main-interface-agent/implementation"

# Activate virtual environment if it exists
if [ -d "alims_env" ]; then
    echo "📦 Activating virtual environment..."
    source alims_env/bin/activate
fi

# Navigate to the backend directory
cd backend

# Install required dependencies if needed
echo "📋 Checking dependencies..."
pip install fastapi uvicorn pydantic > /dev/null 2>&1

# Start the FastAPI server
echo "🎯 Starting Main Interface Agent API on http://127.0.0.1:8001"
echo "📚 API Documentation available at http://127.0.0.1:8001/docs"
echo "💬 Main Interface Agent ready for conversations!"
echo ""
echo "Press Ctrl+C to stop the server"
echo ""

python main_interface_standalone.py
