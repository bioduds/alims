#!/bin/bash
"""
SearXNG Setup for CelFlow Web Search Integration

This script helps set up SearXNG as a privacy-focused search engine
for CelFlow's intelligent web search capabilities.
"""

# SearXNG Setup Instructions for CelFlow
echo "🔍 Setting up SearXNG for CelFlow Web Search"
echo "==========================================="

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "❌ Docker is required but not installed."
    echo "Please install Docker first: https://docs.docker.com/get-docker/"
    exit 1
fi

echo "✅ Docker found"

# Create SearXNG directory
mkdir -p searxng
cd searxng

# Download SearXNG docker-compose configuration
echo "📥 Downloading SearXNG configuration..."
curl -o docker-compose.yaml https://raw.githubusercontent.com/searxng/searxng-docker/master/docker-compose.yaml

# Create basic configuration
echo "⚙️  Creating SearXNG configuration..."
mkdir -p searxng
cat > searxng/settings.yml << 'EOF'
# SearXNG Configuration for CelFlow
use_default_settings: true

server:
  port: 8080
  bind_address: "0.0.0.0"
  secret_key: "$(openssl rand -hex 16)"
  base_url: "http://localhost:8080/"
  image_proxy: true

ui:
  static_use_hash: true
  default_theme: simple
  default_locale: ""
  theme_args:
    simple_style: auto

search:
  safe_search: 1
  autocomplete: "google"
  default_lang: "en"
  max_page: 0

engines:
  - name: google
    engine: google
    use_mobile_ui: false
    
  - name: bing
    engine: bing
    
  - name: duckduckgo
    engine: duckduckgo
    
  - name: startpage
    engine: startpage
    
  - name: wikipedia
    engine: wikipedia
    
  - name: github
    engine: github
    
  - name: stackoverflow
    engine: stackoverflow

enabled_plugins:
  - 'Hash plugin'
  - 'Search on category select'
  - 'Self Information'
  - 'Tracker URL remover'
  - 'Ahmia blacklist'
EOF

# Create environment file
cat > .env << 'EOF'
# SearXNG Environment Configuration
SEARXNG_BASE_URL=http://localhost:8080/
SEARXNG_PORT=8080
SEARXNG_BIND_ADDRESS=0.0.0.0
EOF

echo "🚀 Starting SearXNG..."

# Start SearXNG with Docker Compose
docker-compose up -d

# Wait for SearXNG to start
echo "⏳ Waiting for SearXNG to initialize..."
sleep 10

# Test SearXNG
echo "🧪 Testing SearXNG installation..."
if curl -s http://localhost:8080/ > /dev/null; then
    echo "✅ SearXNG is running successfully!"
    echo "🌐 Access SearXNG at: http://localhost:8080"
    echo ""
    echo "📋 SearXNG API endpoints:"
    echo "   Search: http://localhost:8080/search?q=YOUR_QUERY&format=json"
    echo "   Health: http://localhost:8080/"
    echo ""
    echo "🔧 CelFlow Integration:"
    echo "   The web search is now ready for CelFlow integration"
    echo "   Gemma can now search the web when needed!"
else
    echo "❌ SearXNG failed to start. Check logs with:"
    echo "   docker-compose logs"
fi

echo ""
echo "🛠️  Management Commands:"
echo "   Stop:    docker-compose down"
echo "   Restart: docker-compose restart"
echo "   Logs:    docker-compose logs -f"
echo "   Update:  docker-compose pull && docker-compose up -d"
