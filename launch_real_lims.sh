#!/bin/bash

# 🔬 Real Agentic LIMS Launcher - No Bullshit Version
# Launches the working agentic LIMS system

set -e

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

log() { echo -e "${BLUE}[REAL-LIMS]${NC} $1"; }
success() { echo -e "${GREEN}✅${NC} $1"; }
error() { echo -e "${RED}❌${NC} $1"; }
warn() { echo -e "${YELLOW}⚠️${NC} $1"; }

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$PROJECT_ROOT"

# Check if Ollama is running
check_ollama() {
    log "Checking Ollama service..."
    if curl -s http://localhost:11434/api/tags > /dev/null 2>&1; then
        success "Ollama is running and has models available"
        return 0
    else
        error "Ollama not running on localhost:11434"
        log "Please start Ollama with: ollama serve"
        return 1
    fi
}

# Load environment variables
setup_environment() {
    log "Setting up environment..."
    log "Looking for .env at: $PROJECT_ROOT/.env"
    if [ -f "$PROJECT_ROOT/.env" ]; then
        set -a  # automatically export all variables
        source "$PROJECT_ROOT/.env"
        set +a
        success "Environment variables loaded"
    else
        warn "No .env file found at $PROJECT_ROOT/.env, continuing without environment variables"
    fi
}

# Start the real agentic LIMS
start_real_lims() {
    log "🧪 Starting Real Agentic LIMS..."
    
    # Check dependencies
    check_ollama || return 1
    setup_environment || return 1
    
    # Start the real LIMS
    log "Launching intelligent LIMS system..."
    python "$PROJECT_ROOT/real_agentic_lims.py"
}

# Interactive mode
interactive_mode() {
    log "🔬 Real Agentic LIMS - Interactive Mode"
    echo
    echo "Available commands:"
    echo "  demo    - Run the demo"
    echo "  server  - Start as web server"
    echo "  chat    - Interactive chat mode"
    echo "  test    - Run system tests"
    echo
    
    read -p "Enter command: " cmd
    
    case $cmd in
        demo)
            start_real_lims
            ;;
        server)
            log "Web server mode not implemented yet"
            ;;
        chat)
            log "Chat mode not implemented yet"
            ;;
        test)
            log "Running system tests..."
            python -m pytest tests/ -v
            ;;
        *)
            error "Unknown command: $cmd"
            ;;
    esac
}

# Main function
main() {
    case ${1:-interactive} in
        start|demo)
            start_real_lims
            ;;
        interactive)
            interactive_mode
            ;;
        check)
            check_ollama
            setup_environment
            success "All checks passed"
            ;;
        *)
            echo "Usage: $0 [start|demo|interactive|check]"
            echo
            echo "  start/demo     - Run the agentic LIMS demo"
            echo "  interactive    - Interactive mode (default)"
            echo "  check          - Check system requirements"
            exit 1
            ;;
    esac
}

main "$@"
