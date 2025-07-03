#!/bin/bash

# 🔬 ALIMS - Agentic Laboratory Information Management System
# Control script for all ALIMS components

set -e

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# PID files
AI_PID_FILE="ai_api_server.pid"
MAIN_PID_FILE="main_system.pid"
TRAY_PID_FILE="tray.pid"
TAURI_PID_FILE="tauri_tray.pid"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Utility functions
log() { echo -e "${BLUE}[ALIMS]${NC} $1"; }
success() { echo -e "${GREEN}✅${NC} $1"; }
error() { echo -e "${RED}❌${NC} $1"; }
warn() { echo -e "${YELLOW}⚠️${NC} $1"; }

# Check if process is running
is_running() {
    local pid_file=$1
    [ -f "$pid_file" ] && ps -p "$(cat "$pid_file")" > /dev/null 2>&1
}

# Stop process safely
stop_process() {
    local pid_file=$1
    local name=$2
    
    if is_running "$pid_file"; then
        local pid=$(cat "$pid_file")
        log "Stopping $name (PID: $pid)..."
        kill "$pid" 2>/dev/null || true
        sleep 2
        if ps -p "$pid" > /dev/null 2>&1; then
            kill -9 "$pid" 2>/dev/null || true
        fi
    fi
    rm -f "$pid_file"
}

# Check Ollama service
check_ollama() {
    if ! command -v ollama >/dev/null 2>&1; then
        error "Ollama not installed. Install from https://ollama.ai"
        return 1
    fi
    
    if ! pgrep -f "ollama serve" >/dev/null; then
        log "Starting Ollama service..."
        ollama serve >/dev/null 2>&1 &
        sleep 3
    fi
    
    if ! ollama list | grep -q "gemma2:2b\|gemma:3\|gemma.*3.*4b"; then
        warn "Gemma model not found. Installing gemma2:2b..."
        ollama pull gemma2:2b
    fi
    
    success "Ollama service ready"
}

# Start AI API server
start_ai_server() {
    if is_running "$AI_PID_FILE"; then
        warn "AI server already running"
        return 0
    fi
    
    log "Starting ALIMS AI server..."
    source alims_env/bin/activate 2>/dev/null || {
        error "Virtual environment not found. Run: python -m venv alims_env && source alims_env/bin/activate && pip install -r backend/requirements/base.txt"
        return 1
    }
    
    cd backend
    python -m app.main >/dev/null 2>&1 &
    echo $! > "../$AI_PID_FILE"
    cd ..
    
    success "AI server started"
}

# Start main system
start_main_system() {
    if is_running "$MAIN_PID_FILE"; then
        warn "Main system already running"
        return 0
    fi
    
    log "Starting ALIMS main system..."
    source alims_env/bin/activate
    python backend/scripts/alims.py >/dev/null 2>&1 &
    echo $! > "$MAIN_PID_FILE"
    
    success "Main system started"
}

# Start desktop interface
start_desktop() {
    if is_running "$TAURI_PID_FILE"; then
        warn "Desktop app already running"
        return 0
    fi
    
    # Check dependencies
    if ! command -v node >/dev/null 2>&1; then
        error "Node.js not installed"
        return 1
    fi
    
    if ! command -v cargo >/dev/null 2>&1; then
        error "Rust/Cargo not installed"
        return 1
    fi
    
    # Free port 3000
    lsof -ti:3000 | xargs kill -9 2>/dev/null || true
    
    log "Starting ALIMS desktop interface..."
    cd frontend/desktop
    npm run tauri:dev -- --no-watch >/dev/null 2>&1 &
    echo $! > "../../$TAURI_PID_FILE"
    cd ../..
    
    success "Desktop interface started"
}

# Start system tray
start_tray() {
    if is_running "$TRAY_PID_FILE"; then
        warn "System tray already running"
        return 0
    fi
    
    log "Starting system tray..."
    source alims_env/bin/activate
    python backend/app/system/macos_tray.py >/dev/null 2>&1 &
    echo $! > "$TRAY_PID_FILE"
    
    success "System tray started"
}

# Show status
status() {
    log "ALIMS System Status:"
    echo
    
    local services=("AI Server:$AI_PID_FILE" "Main System:$MAIN_PID_FILE" "Desktop App:$TAURI_PID_FILE" "System Tray:$TRAY_PID_FILE")
    
    for service in "${services[@]}"; do
        local name="${service%:*}"
        local pid_file="${service#*:}"
        
        if is_running "$pid_file"; then
            local pid=$(cat "$pid_file")
            success "$name (PID: $pid)"
        else
            error "$name (Not running)"
        fi
    done
    
    echo
    if command -v ollama >/dev/null 2>&1 && pgrep -f "ollama serve" >/dev/null; then
        success "Ollama service (Running)"
    else
        error "Ollama service (Not running)"
    fi
}

# Start all services
start() {
    log "🔬 Starting ALIMS - Agentic Laboratory Information Management System"
    echo
    
    # Check and start dependencies
    check_ollama || return 1
    
    # Start core services
    start_ai_server || return 1
    sleep 2
    
    start_main_system || return 1
    sleep 1
    
    # Start UI components
    start_desktop || return 1
    sleep 2
    
    start_tray || return 1
    
    echo
    success "ALIMS system started successfully!"
    echo
    log "Access the laboratory interface through the desktop app or system tray"
}

# Stop all services
stop() {
    log "Stopping ALIMS services..."
    
    stop_process "$TRAY_PID_FILE" "System Tray"
    stop_process "$TAURI_PID_FILE" "Desktop App"
    stop_process "$MAIN_PID_FILE" "Main System"
    stop_process "$AI_PID_FILE" "AI Server"
    
    # Clean up any remaining processes
    pkill -f "python.*backend" 2>/dev/null || true
    lsof -ti:8000 | xargs kill -9 2>/dev/null || true
    lsof -ti:3000 | xargs kill -9 2>/dev/null || true
    
    success "ALIMS stopped"
}

# Restart services
restart() {
    log "Restarting ALIMS..."
    stop
    sleep 3
    start
}

# Health check
health() {
    log "ALIMS Health Check:"
    echo
    
    # Check environment
    if [ -d "alims_env" ]; then
        success "Virtual environment exists"
    else
        error "Virtual environment missing"
    fi
    
    # Check Ollama
    if command -v ollama >/dev/null 2>&1; then
        success "Ollama installed"
        if pgrep -f "ollama serve" >/dev/null; then
            success "Ollama service running"
        else
            warn "Ollama service not running"
        fi
    else
        error "Ollama not installed"
    fi
    
    # Check services
    status
    
    # Check ports
    if lsof -i:8000 >/dev/null 2>&1; then
        success "AI API port (8000) active"
    else
        warn "AI API port (8000) not in use"
    fi
}

# Setup environment
setup() {
    log "Setting up ALIMS environment..."
    
    # Create virtual environment
    if [ ! -d "alims_env" ]; then
        log "Creating virtual environment..."
        python3 -m venv alims_env
    fi
    
    # Activate and install dependencies
    source alims_env/bin/activate
    log "Installing dependencies..."
    pip install -r backend/requirements/base.txt
    
    # Install frontend dependencies
    if [ -d "frontend/desktop" ]; then
        log "Installing frontend dependencies..."
        cd frontend/desktop
        npm install
        cd ../..
    fi
    
    success "Environment setup complete!"
    echo
    log "You can now run: ./alims.sh start"
}

# Show help
help() {
    echo "🔬 ALIMS - Agentic Laboratory Information Management System"
    echo
    echo "Usage: $0 [COMMAND]"
    echo
    echo "Commands:"
    echo "  start    Start all ALIMS services"
    echo "  stop     Stop all ALIMS services"
    echo "  restart  Restart all ALIMS services"
    echo "  status   Show service status"
    echo "  health   Run health check"
    echo "  setup    Setup environment"
    echo "  help     Show this help message"
    echo
    echo "Examples:"
    echo "  $0 start         # Start ALIMS"
    echo "  $0 status        # Check status"
    echo "  $0 setup         # First-time setup"
}

# Main command handler
case "${1:-help}" in
    start)   start ;;
    stop)    stop ;;
    restart) restart ;;
    status)  status ;;
    health)  health ;;
    setup)   setup ;;
    help|*)  help ;;
esac
