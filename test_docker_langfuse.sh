#!/bin/bash

# Test Langfuse in Docker environment

echo "🐳 Testing Langfuse in Docker environment"
echo "=========================================="

# Load environment variables
source .env

echo "🔍 Environment check:"
echo "   LANGFUSE_PUBLIC_KEY: ${LANGFUSE_PUBLIC_KEY:0:20}..."
echo "   LANGFUSE_SECRET_KEY: ${LANGFUSE_SECRET_KEY:0:20}..."
echo "   LANGFUSE_HOST: $LANGFUSE_HOST"

# Test with a simple Docker container
echo ""
echo "🧪 Testing Langfuse connection from Docker container..."

docker run --rm \
  -e LANGFUSE_PUBLIC_KEY="$LANGFUSE_PUBLIC_KEY" \
  -e LANGFUSE_SECRET_KEY="$LANGFUSE_SECRET_KEY" \
  -e LANGFUSE_HOST="$LANGFUSE_HOST" \
  -v "$(pwd):/workspace" \
  -w /workspace \
  python:3.11-slim \
  bash -c "
    pip install langfuse requests > /dev/null 2>&1 && 
    python -c '
import os
from langfuse import Langfuse

print(\"🔍 Docker container environment:\")
print(f\"   LANGFUSE_PUBLIC_KEY: {os.getenv(\"LANGFUSE_PUBLIC_KEY\", \"Not set\")[:20]}...\")
print(f\"   LANGFUSE_HOST: {os.getenv(\"LANGFUSE_HOST\", \"Not set\")}\")

try:
    client = Langfuse()
    print(\"✅ Langfuse client created in Docker!\")
    
    # Create test event
    client.create_event(
        name=\"docker_container_test\",
        metadata={
            \"source\": \"docker_test\",
            \"system\": \"ALIMS\",
            \"test\": True,
            \"timestamp\": \"2025-07-21\"
        }
    )
    print(\"✅ Created test event from Docker container\")
    
    client.flush()
    print(\"📤 Flushed data from Docker to Langfuse\")
    print(\"🎉 Docker Langfuse test successful!\")
    
except Exception as e:
    print(f\"❌ Docker test failed: {e}\")
    exit(1)
'"

echo ""
echo "✅ Docker Langfuse integration test complete!"
echo "📊 View your data at: $LANGFUSE_HOST"
