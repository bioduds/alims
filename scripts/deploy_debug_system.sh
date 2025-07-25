#!/bin/bash
# ALIMS Debug System Deployment Script
# Quick deployment of debugging infrastructure

set -e

echo "🔍 Deploying ALIMS Debug System..."

# Create debug logs directory
mkdir -p logs/debug
echo "✅ Created debug logs directory"

# Install any missing dependencies
echo "📦 Checking dependencies..."
cd backend
pip install websockets

# Restart main-interface service with new debugging
echo "🔄 Restarting main-interface service with debugging..."
cd ..
docker-compose restart main-interface

# Wait for service to be healthy
echo "⏳ Waiting for main-interface to be healthy..."
sleep 10

# Test debugging endpoints
echo "🧪 Testing debug endpoints..."
curl -s http://localhost:8003/api/v1/debug/status | python3 -m json.tool
echo ""

echo "🎯 Debug system deployment complete!"
echo ""
echo "🔍 Debug Dashboard: http://localhost:8003/debug"
echo "📊 Debug API: http://localhost:8003/api/v1/debug/status"
echo "🔄 Real-time Events: ws://localhost:8003/ws/debug"
echo ""
echo "To see what's happening in the chat issue:"
echo "1. Visit: http://localhost:8003/debug"
echo "2. Start a conversation"
echo "3. Watch the real-time trace in the dashboard"
echo ""
echo "For conversation-specific debugging:"
echo "curl http://localhost:8003/api/v1/debug/conversation/{conversation_id}"
