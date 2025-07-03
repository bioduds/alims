#!/bin/bash

# Direct Desktop Launcher for ALims
# This script forcefully stops all existing processes and launches the desktop app directly

# Get the directory where the script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Change to the script directory
cd "$SCRIPT_DIR"

echo "Stopping any existing ALims processes..."

# Kill any existing processes
pkill -f "python.*alims"
pkill -f "tauri dev"
pkill -f "npm run tauri"
pkill -f "node.*tauri"
pkill -f "ALims Desktop"

# Kill any processes using port 3000
echo "Freeing port 3000..."
lsof -ti:3000 | xargs kill -9 2>/dev/null || true

# Wait a moment for processes to terminate
sleep 2

# Navigate to desktop directory
cd frontend/desktop

echo "Launching ALims Desktop directly..."

# Launch Tauri app with no watch mode for immediate startup
npm run tauri:dev -- --no-watch

echo "Desktop app exited." 