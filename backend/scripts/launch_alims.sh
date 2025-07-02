#!/bin/bash

# ALims Complete System Launcher
# This script launches the complete ALims system with all components

set -e  # Exit on any error

# Change to project root directory (two levels up from backend/scripts/)
cd "$(dirname "$0")/../.."

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    echo -e "${BLUE}[ALims]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[ALims]${NC} ✅ $1"
}

print_warning() {
    echo -e "${YELLOW}[ALims]${NC} ⚠️  $1"
}

print_error() {
    echo -e "${RED}[ALims]${NC} ❌ $1"
}

print_header() {
    echo -e "${PURPLE}"
    echo "🎭 ======================================================== 🎭"
    echo "                 ALims System Launcher"
    echo "🎭 ======================================================== 🎭"
    echo -e "${NC}"
}

# Function to check if virtual environment exists
check_venv() {
    if [ ! -d "environments/alims_env" ]; then
        print_error "Virtual environment 'environments/alims_env' not found!"
        print_status "Please create it with: python3 -m venv environments/alims_env"
        exit 1
    fi
    print_success "Virtual environment found"
}

# Function to activate virtual environment
activate_venv() {
    print_status "Activating virtual environment..."
    source environments/alims_env/bin/activate
    print_success "Virtual environment activated"
}

# Function to kill existing processes
cleanup_processes() {
    print_status "Cleaning up existing ALims processes..."
    
    # First, try to stop processes gracefully using PID files
    if [ -f "logs/alims_main.pid" ]; then
        MAIN_PID=$(cat logs/alims_main.pid)
        if kill -0 $MAIN_PID 2>/dev/null; then
            print_status "Stopping main system (PID: $MAIN_PID)..."
            kill $MAIN_PID 2>/dev/null || true
            sleep 2
            # Force kill if still running
            if kill -0 $MAIN_PID 2>/dev/null; then
                kill -9 $MAIN_PID 2>/dev/null || true
            fi
        fi
        rm -f logs/alims_main.pid
    fi
    
    if [ -f "logs/alims_tray.pid" ]; then
        TRAY_PID=$(cat logs/alims_tray.pid)
        if kill -0 $TRAY_PID 2>/dev/null; then
            print_status "Stopping system tray (PID: $TRAY_PID)..."
            kill $TRAY_PID 2>/dev/null || true
            sleep 2
            # Force kill if still running
            if kill -0 $TRAY_PID 2>/dev/null; then
                kill -9 $TRAY_PID 2>/dev/null || true
            fi
        fi
        rm -f logs/alims_tray.pid
    fi
    
    if [ -f "logs/tauri_tray.pid" ]; then
        TAURI_TRAY_PID=$(cat logs/tauri_tray.pid)
        if kill -0 $TAURI_TRAY_PID 2>/dev/null; then
            print_status "Stopping Tauri tray (PID: $TAURI_TRAY_PID)..."
            kill $TAURI_TRAY_PID 2>/dev/null || true
            sleep 2
            # Force kill if still running
            if kill -0 $TAURI_TRAY_PID 2>/dev/null; then
                kill -9 $TAURI_TRAY_PID 2>/dev/null || true
            fi
        fi
        rm -f logs/tauri_tray.pid
    fi
    
    # Kill any remaining ALims processes by name patterns (excluding this script)
    print_status "Killing remaining ALims processes..."
    ps aux | grep -E "(alims|ALims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray|test_chat)" | grep -v grep | grep -v "launch_alims.sh" | awk '{print $2}' | xargs -r kill 2>/dev/null || true
    sleep 1
    
    # Force kill any stubborn processes
    ps aux | grep -E "(alims|ALims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray|test_chat)" | grep -v grep | grep -v "launch_alims.sh" | awk '{print $2}' | xargs -r kill -9 2>/dev/null || true
    sleep 1
    
    # Kill any Python processes running ALims scripts (excluding this script)
    ps aux | grep -E "(python|Python).*(alims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray)" | grep -v grep | grep -v "launch_alims.sh" | awk '{print $2}' | xargs -r kill -9 2>/dev/null || true
    
    # Additional cleanup for any Python processes in the project directory (excluding this script)
    CURRENT_DIR=$(pwd)
    ps aux | grep "$CURRENT_DIR" | grep -v grep | grep -v "launch_alims.sh" | grep -E "(python|Python)" | awk '{print $2}' | xargs -r kill -9 2>/dev/null || true
    
    sleep 2
    
    # Verify cleanup - show any remaining ALims processes (excluding this script)
    REMAINING=$(ps aux | grep -E "(alims|ALims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray)" | grep -v grep | grep -v "launch_alims.sh" | wc -l)
    if [ "$REMAINING" -gt 0 ]; then
        print_warning "Found $REMAINING remaining ALims processes:"
        ps aux | grep -E "(alims|ALims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray)" | grep -v grep | grep -v "launch_alims.sh" | awk '{print "  PID " $2 ": " $11 " " $12 " " $13}'
        print_status "Force killing remaining processes..."
        ps aux | grep -E "(alims|ALims|run_alims|launch_tray|launch_tauri_tray|macos_tray|tauri_integrated_tray)" | grep -v grep | grep -v "launch_alims.sh" | awk '{print $2}' | xargs -r kill -9 2>/dev/null || true
        sleep 1
    fi
    
    print_success "Cleanup complete - all ALims processes terminated"
}

# Function to check system status
check_system() {
    print_status "Checking system status..."
    
    # Check database
    if [ -f "data/events.db" ]; then
        DB_SIZE=$(du -h data/events.db | cut -f1)
        print_success "Database found: $DB_SIZE"
    else
        print_warning "No database found - will be created"
    fi
    
    # Check if we have agents
    if [ -f "check_agents.py" ]; then
        AGENT_COUNT=$(python3 check_agents.py 2>/dev/null | grep "Agents Born:" | cut -d: -f2 | tr -d ' ' || echo "0")
        if [ "$AGENT_COUNT" != "0" ]; then
            print_success "Found $AGENT_COUNT existing agents"
        else
            print_status "No existing agents - system will birth new ones"
        fi
    fi
}

# Function to start the main system
start_main_system() {
    print_status "Starting main ALims system..."
    
    # Create log directory
    mkdir -p logs
    
    # Start main system in background with logging using virtual environment
    nohup bash -c "source environments/alims_env/bin/activate && PYTHONPATH=$(pwd):$(pwd)/backend python3 backend/scripts/run_alims_live.py" > logs/alims_main.log 2>&1 &
    MAIN_PID=$!
    
    print_success "Main system started (PID: $MAIN_PID)"
    
    # Wait a moment for initialization
    sleep 3
    
    # Check if it's still running
    if kill -0 $MAIN_PID 2>/dev/null; then
        print_success "Main system running successfully"
        echo $MAIN_PID > logs/alims_main.pid
    else
        print_error "Main system failed to start"
        return 1
    fi
}

# Function to start the system tray
start_tray() {
    print_status "Starting system tray..."
    
    # Start tray in background using virtual environment with correct Python path
    nohup bash -c "source environments/alims_env/bin/activate && PYTHONPATH=$(pwd):$(pwd)/backend python3 backend/scripts/launch_tray.py" > logs/alims_tray.log 2>&1 &
    TRAY_PID=$!
    
    print_success "System tray started (PID: $TRAY_PID)"
    echo $TRAY_PID > logs/alims_tray.pid
    
    # Wait a moment
    sleep 2
    
    # Check if it's running
    if kill -0 $TRAY_PID 2>/dev/null; then
        print_success "System tray running - check your menu bar!"
    else
        print_warning "System tray may have failed (check logs/alims_tray.log)"
    fi
}

# Function to check and install Tauri dependencies
check_tauri_deps() {
    print_status "Checking Tauri dependencies..."
    
    # Check if Node.js is installed
    if ! command -v node >/dev/null 2>&1; then
        print_error "Node.js not found. Please install Node.js first."
        return 1
    fi
    
    # Check if npm is installed
    if ! command -v npm >/dev/null 2>&1; then
        print_error "npm not found. Please install npm first."
        return 1
    fi
    
    # Check if Rust is installed
    if ! command -v rustc >/dev/null 2>&1; then
        print_status "Installing Rust..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
        source "$HOME/.cargo/env"
    fi
    
    # Install Tauri CLI if not installed
    if ! cargo tauri --version >/dev/null 2>&1; then
        print_status "Installing Tauri CLI..."
        cargo install tauri-cli
    fi
    
    # Install frontend dependencies if needed
    if [ ! -d "frontend/desktop/node_modules" ]; then
        print_status "Installing frontend dependencies..."
        cd frontend/desktop && npm install && cd ../..
    fi
    
    print_success "Tauri dependencies checked and installed"
    return 0
}

# Function to start the Tauri-integrated tray
start_tauri_tray() {
    print_status "Starting Tauri-integrated system tray..."
    
    # Check Tauri dependencies first
    if ! check_tauri_deps; then
        print_warning "Skipping Tauri tray due to missing dependencies"
        return 1
    fi
    
    # Start Tauri tray in background using virtual environment with correct Python path
    nohup bash -c "source environments/alims_env/bin/activate && PYTHONPATH=$(pwd) python3 backend/scripts/launch_tauri_tray.py" > logs/tauri_tray.log 2>&1 &
    TRAY_PID=$!
    
    print_success "Tauri-integrated tray started (PID: $TRAY_PID)"
    echo $TRAY_PID > logs/tauri_tray.pid
    
    # Wait a moment
    sleep 2
    
    # Check if it's running
    if kill -0 $TRAY_PID 2>/dev/null; then
        print_success "Tauri-integrated tray running - check your menu bar!"
        print_status "🖥️ You can now launch the beautiful desktop app from the tray!"
    else
        print_warning "Tauri-integrated tray may have failed (check logs/tauri_tray.log)"
    fi
}

# Function to show system status
show_status() {
    print_status "System Status:"
    echo ""
    
    # Check main system
    if [ -f "logs/alims_main.pid" ]; then
        MAIN_PID=$(cat logs/alims_main.pid)
        if kill -0 $MAIN_PID 2>/dev/null; then
            print_success "Main System: Running (PID: $MAIN_PID)"
        else
            print_error "Main System: Not running"
        fi
    else
        print_error "Main System: Not started"
    fi
    
    # Check tray
    if [ -f "logs/alims_tray.pid" ]; then
        TRAY_PID=$(cat logs/alims_tray.pid)
        if kill -0 $TRAY_PID 2>/dev/null; then
            print_success "System Tray: Running (PID: $TRAY_PID)"
        else
            print_warning "System Tray: Not running"
        fi
    else
        print_warning "System Tray: Not started"
    fi
    
    # Check Tauri tray
    if [ -f "logs/tauri_tray.pid" ]; then
        TAURI_TRAY_PID=$(cat logs/tauri_tray.pid)
        if kill -0 $TAURI_TRAY_PID 2>/dev/null; then
            print_success "Tauri Tray: Running (PID: $TAURI_TRAY_PID) 🖥️"
        else
            print_warning "Tauri Tray: Not running"
        fi
    else
        print_warning "Tauri Tray: Not started"
    fi
    
    echo ""
}

# Function to monitor logs
monitor_logs() {
    print_status "Monitoring system logs (Ctrl+C to stop)..."
    echo ""
    
    # Show recent logs
    if [ -f "logs/alims_main.log" ]; then
        echo -e "${CYAN}=== Recent Main System Logs ===${NC}"
        tail -n 10 logs/alims_main.log
        echo ""
    fi
    
    # Follow logs
    if [ -f "logs/alims_main.log" ]; then
        print_status "Following main system logs..."
        tail -f logs/alims_main.log
    else
        print_error "No logs found"
    fi
}

# Function to restart just the tray
restart_tray() {
    print_status "Restarting system tray..."
    
    # Stop tray if running
    if [ -f "logs/alims_tray.pid" ]; then
        TRAY_PID=$(cat logs/alims_tray.pid)
        if kill -0 $TRAY_PID 2>/dev/null; then
            kill $TRAY_PID
            print_success "System tray stopped"
        fi
        rm -f logs/alims_tray.pid
    fi
    
    # Kill any remaining tray processes
    pkill -f "launch_tray|macos_tray" 2>/dev/null || true
    sleep 2
    
    # Start tray again
    start_tray
}

# Function to stop all processes
stop_system() {
    print_status "Stopping ALims system..."
    
    # Use the comprehensive cleanup function
    cleanup_processes
    
    print_success "ALims system stopped"
}

# Main script logic
main() {
    print_header
    
    case "${1:-start}" in
        "start")
            check_venv
            activate_venv
            cleanup_processes
            check_system
            start_main_system
            start_tauri_tray
            show_status
            echo ""
            print_success "ALims system launched successfully!"
            print_status "Use './launch_alims.sh status' to check status"
            print_status "Use './launch_alims.sh logs' to monitor logs"
            print_status "Use './launch_alims.sh stop' to stop the system"
            ;;
        "stop")
            stop_system
            ;;
        "status")
            show_status
            ;;
        "logs")
            monitor_logs
            ;;
        "restart")
            stop_system
            sleep 2
            main start
            ;;
        "tray")
            restart_tray
            show_status
            ;;
        "tauri")
            check_venv
            activate_venv
            cleanup_processes
            check_system
            start_main_system
            start_tauri_tray
            show_status
            echo ""
            print_success "ALims system with Tauri-integrated tray launched!"
            print_status "🖥️ Click the tray icon and select 'Launch Desktop App'"
            print_status "Use './launch_alims.sh status' to check status"
            ;;
        "desktop")
            print_status "Launching desktop app directly..."
            if [ -f "frontend/desktop/package.json" ]; then
                cd frontend/desktop && npm run tauri:dev
            else
                print_error "frontend/desktop/package.json not found. Please run 'npm install' first."
            fi
            ;;
        *)
            echo "Usage: $0 {start|stop|status|logs|restart|tray|tauri|desktop}"
            echo ""
            echo "Commands:"
            echo "  start   - Start the complete ALims system"
            echo "  stop    - Stop all ALims processes"
            echo "  status  - Show system status"
            echo "  logs    - Monitor system logs"
            echo "  restart - Restart the system"
            echo "  tray    - Restart just the system tray"
            echo "  tauri   - Start system with Tauri-integrated tray"
            echo "  desktop - Launch desktop app directly"
            exit 1
            ;;
    esac
}

# Run main function with all arguments
main "$@" 