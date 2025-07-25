#!/bin/bash

# ALIMS Monitoring Setup Script
# This script helps you configure monitoring for your ALIMS system

set -e

echo "🔍 ALIMS Monitoring Setup"
echo "========================="
echo ""

# Check if .env exists
if [ -f ".env" ]; then
    echo "📁 Found existing .env file"
    source .env
else
    echo "📁 Creating new .env file"
    touch .env
fi

echo ""
echo "Choose your monitoring setup:"
echo "1) Langfuse Cloud (Managed, requires API keys)"
echo "2) Self-hosted Langfuse (Open source, local)"
echo "3) OpenTelemetry + Jaeger (Pure open source)"
echo "4) All of the above"
echo ""

read -p "Enter choice (1-4): " choice

case $choice in
    1|4)
        echo ""
        echo "🌐 Setting up Langfuse Cloud"
        echo "----------------------------"
        echo "1. Go to https://cloud.langfuse.com"
        echo "2. Sign up for free account"
        echo "3. Create a project"
        echo "4. Go to Settings → API Keys"
        echo ""
        
        if [ -z "$LANGFUSE_PUBLIC_KEY" ]; then
            read -p "Enter your Langfuse Public Key (pk-lf-...): " pub_key
            echo "LANGFUSE_PUBLIC_KEY=$pub_key" >> .env
        else
            echo "✅ Langfuse Public Key already set"
        fi
        
        if [ -z "$LANGFUSE_SECRET_KEY" ]; then
            read -p "Enter your Langfuse Secret Key (sk-lf-...): " sec_key
            echo "LANGFUSE_SECRET_KEY=$sec_key" >> .env
        else
            echo "✅ Langfuse Secret Key already set"
        fi
        
        if [ -z "$LANGFUSE_HOST" ]; then
            echo "LANGFUSE_HOST=https://cloud.langfuse.com" >> .env
        fi
        ;;
esac

case $choice in
    2|4)
        echo ""
        echo "🏠 Setting up Self-hosted Langfuse"
        echo "----------------------------------"
        
        if ! command -v docker-compose &> /dev/null; then
            echo "❌ Docker Compose not found. Please install Docker first."
            exit 1
        fi
        
        echo "Starting self-hosted Langfuse..."
        docker-compose -f docker-compose.langfuse.yml up -d
        
        echo "✅ Langfuse started on http://localhost:3000"
        echo "   1. Open http://localhost:3000"
        echo "   2. Create account and project"
        echo "   3. Get API keys and run this script again with option 1"
        ;;
esac

case $choice in
    3|4)
        echo ""
        echo "📊 Setting up OpenTelemetry + Jaeger"
        echo "------------------------------------"
        
        if ! command -v docker &> /dev/null; then
            echo "❌ Docker not found. Please install Docker first."
            exit 1
        fi
        
        echo "Starting Jaeger..."
        docker run -d --name alims-jaeger \
            -p 16686:16686 \
            -p 14268:14268 \
            jaegertracing/all-in-one:latest 2>/dev/null || echo "Jaeger already running"
        
        echo "JAEGER_ENDPOINT=http://localhost:14268/api/traces" >> .env
        echo "✅ Jaeger started on http://localhost:16686"
        ;;
esac

echo ""
echo "🧪 Testing setup..."
echo "-------------------"

# Source the .env file
source .env

# Test Langfuse if configured
if [ -n "$LANGFUSE_PUBLIC_KEY" ] && [ -n "$LANGFUSE_SECRET_KEY" ]; then
    echo "Testing Langfuse connection..."
    python3 -c "
import os
os.environ['LANGFUSE_PUBLIC_KEY'] = '${LANGFUSE_PUBLIC_KEY}'
os.environ['LANGFUSE_SECRET_KEY'] = '${LANGFUSE_SECRET_KEY}'
os.environ['LANGFUSE_HOST'] = '${LANGFUSE_HOST:-https://cloud.langfuse.com}'

try:
    from langfuse import Langfuse
    client = Langfuse()
    print('✅ Langfuse connection successful')
except Exception as e:
    print(f'❌ Langfuse connection failed: {e}')
" 2>/dev/null || echo "⚠️  Langfuse test requires langfuse package"
fi

echo ""
echo "🎉 Setup complete!"
echo "=================="
echo ""
echo "Configuration saved to .env file:"
cat .env
echo ""
echo "Next steps:"
echo "1. Install monitoring dependencies:"
echo "   pip install langfuse opentelemetry-api opentelemetry-sdk opentelemetry-exporter-jaeger"
echo ""
echo "2. Start your ALIMS system:"
echo "   ./start-dev.sh"
echo ""
echo "3. View monitoring:"
if [ -n "$LANGFUSE_HOST" ]; then
    echo "   - Langfuse: $LANGFUSE_HOST"
fi
echo "   - Jaeger: http://localhost:16686"
echo ""
echo "4. Run a test workflow:"
echo "   python demos/demo_langfuse_monitoring.py"
