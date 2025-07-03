#!/bin/bash

# ALims Desktop Launcher
# This script directly launches the ALims desktop app

# Get the directory where the script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Change to the script directory
cd "$SCRIPT_DIR"

echo "Launching ALims Desktop..."

# Navigate to desktop directory
cd frontend/desktop

# Launch Tauri app
echo "Starting Tauri desktop app..."
npm run tauri:dev -- --no-watch

echo "Desktop app exited." 