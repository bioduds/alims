#!/bin/bash

# ALIMS Launch Script
# This script manages the ALIMS system components

# Get the directory where the script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Change to the script directory
cd "$SCRIPT_DIR"

# Function to check if a process is running
check_process() {
    local pid_file=$1
    if [ -f "$pid_file" ]; then
        local pid=$(cat "$pid_file")
        if ps -p "$pid" > /dev/null; then
            return 0  # Process is running
        fi
    fi
    return 1  # Process is not running
}

# Function to stop a process
stop_process() {
    local pid_file=$1
    local process_name=$2
    
    if [ -f "$pid_file" ]; then
        local pid=$(cat "$pid_file")
        if ps -p "$pid" > /dev/null; then
            echo "Stopping $process_name (PID: $pid)..."
            kill "$pid"
            sleep 2
            if ps -p "$pid" > /dev/null; then
                echo "Force stopping $process_name..."
                kill -9 "$pid"
            fi
        fi
        rm -f "$pid_file"
    fi
}

# Function to check and start Ollama
check_start_ollama() {
    echo "Checking Ollama service..."
    
    # Check if Ollama is installed
    if ! command -v ollama &> /dev/null; then
        echo "❌ Ollama is not installed. Please install it first:"
        echo "   Visit: https://ollama.ai"
        return 1
    fi
    
    # Check if Ollama service is running
    if ! curl -s http://localhost:11434/api/tags &> /dev/null; then
        echo "Starting Ollama service..."
        ollama serve > /dev/null 2>&1 &
        echo $! > "$SCRIPT_DIR/ollama.pid"
        
        # Wait for Ollama to start
        echo "Waiting for Ollama to initialize..."
        sleep 5
        
        # Check if it's running now
        if ! curl -s http://localhost:11434/api/tags &> /dev/null; then
            echo "❌ Failed to start Ollama service"
            return 1
        fi
    fi
    
    echo "✅ Ollama service is running"
    
    # Check if Gemma 3:4b model is available
    if ! ollama list | grep -q "gemma3:4b"; then
        echo "📥 Downloading Gemma 3:4b model (this may take a while)..."
        ollama pull gemma3:4b
        if [ $? -ne 0 ]; then
            echo "❌ Failed to download Gemma 3:4b model"
            return 1
        fi
    fi
    
    echo "✅ Gemma 3:4b model is ready"
    return 0
}

# Function to check Tauri dependencies
check_tauri_deps() {
    # Check Node.js
    if ! command -v node &> /dev/null; then
        echo "Node.js is not installed. Please install it first."
        return 1
    fi

    # Check npm
    if ! command -v npm &> /dev/null; then
        echo "npm is not installed. Please install it first."
        return 1
    fi

    # Check Rust
    if ! command -v rustc &> /dev/null; then
        echo "Rust is not installed. Please install it first."
        return 1
    fi

    # Check Tauri CLI
    if ! cargo tauri --version &> /dev/null; then
        echo "Tauri CLI is not installed. Installing..."
        cargo install tauri-cli
        if [ $? -ne 0 ]; then
            echo "Failed to install Tauri CLI"
            return 1
        fi
    fi

    return 0
}

# Function to start the Tauri tray
start_tauri_tray() {
    echo "Starting Tauri tray..."
    
    # Check dependencies
    if ! check_tauri_deps; then
        echo "Missing Tauri dependencies. Please install them first."
        return 1
    fi
    
    # Kill any processes using port 3000
    echo "Freeing port 3000..."
    lsof -ti:3000 | xargs kill -9 2>/dev/null || true
    
    # Start the Tauri tray
    cd frontend/desktop
    echo "Launching desktop app - please wait..."
    npm run tauri:dev -- --no-watch > /dev/null 2>&1 &
    echo $! > "$SCRIPT_DIR/tauri_tray.pid"
    cd "$SCRIPT_DIR"
    
    # Give it more time to initialize (desktop app needs more time)
    echo "Waiting for desktop app to initialize (5 seconds)..."
    sleep 5
    
    echo "Tauri tray and desktop app started"
}

# Function to start the system tray icon separately
start_system_tray() {
    echo "Starting system tray icon..."
    
    # Start the Python-based system tray
    python3 backend/scripts/launch_tauri_tray.py > /dev/null 2>&1 &
    echo $! > "$SCRIPT_DIR/system_tray.pid"
    
    echo "System tray icon started"
}

# Function to start the main system
start_main_system() {
    echo "Starting ALIMS main system components..."
    
    # Activate virtual environment
    if [ -d "alims_env" ]; then
        source alims_env/bin/activate
        echo "Virtual environment activated"
    else
        echo "Creating virtual environment..."
        python3 -m venv alims_env
        source alims_env/bin/activate
        echo "Installing dependencies..."
        pip install -r backend/requirements/base.txt
    fi
    
    # Start AI API Server first
    echo "Starting ALIMS AI API Server..."
    cd backend
    python -m app.web.ai_api_server > ../logs/ai_api_server.log 2>&1 &
    AI_API_PID=$!
    echo $AI_API_PID > "$SCRIPT_DIR/ai_api_server.pid"
    cd ..
    
    # Wait a moment for AI API to start
    sleep 5
    
    # Start main ALIMS system
    echo "Starting main ALIMS system..."
    python backend/scripts/run_alims_live.py > logs/main_system.log 2>&1 &
    MAIN_PID=$!
    echo $MAIN_PID > "$SCRIPT_DIR/main_system.pid"
    
    # Start tray application  
    echo "Starting system tray..."
    python backend/scripts/alims_tray.py > logs/tray.log 2>&1 &
    TRAY_PID=$!
    echo $TRAY_PID > "$SCRIPT_DIR/tray.pid"
    
    echo "✅ Main system components started"
    echo "AI API Server PID: $AI_API_PID"
    echo "Main System PID: $MAIN_PID"
    echo "Tray PID: $TRAY_PID"
}

# Function to stop all components
stop_all() {
    echo "Stopping ALIMS components..."
    
    # Stop Tauri tray
    stop_process "tauri_tray.pid" "Tauri tray"
    
    # Stop system tray
    stop_process "system_tray.pid" "System tray"
    
    # Stop AI API server
    stop_process "ai_api_server.pid" "AI API Server"
    
    # Stop main system
    stop_process "main_system.pid" "Main system"
    
    # Stop tray
    stop_process "tray.pid" "System Tray"
    
    # Stop Ollama service
    stop_process "ollama.pid" "Ollama service"
    
    # Kill any remaining processes
    echo "Cleaning up any remaining processes..."
    pkill -f "python.*$SCRIPT_DIR"
    pkill -f "python.*ai_api_server"
    pkill -f "tauri dev"
    pkill -f "npm run tauri"
    pkill -f "node.*tauri"
    pkill -f "ALIMS Desktop"
    pkill -f "ollama serve"
    
    # Kill processes on ports 3000, 8000, and 11434
    lsof -ti:3000 | xargs kill -9 2>/dev/null || true
    lsof -ti:8000 | xargs kill -9 2>/dev/null || true
    lsof -ti:11434 | xargs kill -9 2>/dev/null || true
    
    echo "All components stopped"
}

# Function to start all components
start_all() {
    echo "Starting ALIMS..."
    
    # Start Ollama service first (required for AI)
    if ! check_start_ollama; then
        echo "❌ Failed to start Ollama. ALIMS AI features will not work."
        echo "Please install Ollama from https://ollama.ai and try again."
        return 1
    fi
    
    # Start Tauri tray
    start_tauri_tray
    
    # Start system tray icon
    start_system_tray
    
    # Give it a moment to initialize
    echo "Waiting for desktop app to initialize..."
    sleep 2
    
    # Start main system
    start_main_system
    
    echo "ALIMS started"
    
    # Show running processes
    echo -e "\nRunning processes:"
    ps aux | grep -E "python.*$SCRIPT_DIR|tauri|ollama" | grep -v grep
}

# Function to restart the system
restart_system() {
    echo "Restarting ALIMS..."
    stop_all
    sleep 2
    start_all
}

# Command processing
case "$1" in
    start)
        start_all
        ;;
    stop)
        stop_all
        ;;
    restart)
        restart_system
        ;;
    *)
        echo "Usage: $0 {start|stop|restart}"
        exit 1
        ;;
esac

exit 0 