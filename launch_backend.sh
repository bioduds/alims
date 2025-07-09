#!/bin/bash

# Activate Python virtual environment
source alims_env/bin/activate

# Kill any existing Python processes (optional - uncomment if needed)
# pkill -f "python.*api_server"

# Start the simplified FastAPI server
cd backend && python simple_api_server.py
