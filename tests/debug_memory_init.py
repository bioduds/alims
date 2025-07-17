#!/usr/bin/env python3
"""
Debug script to test memory system initialization
"""

import os
import asyncio
import sys
import logging

# Add the backend path to sys.path
sys.path.append('backend')

from backend.app.tensor_calendar.unified_memory_tensor import UnifiedMemoryTensorEngine
from backend.app.tensor_calendar.memory_models import MemoryTensorConfiguration

# Setup logging
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)

async def test_memory_init():
    """Test memory system initialization with Docker Qdrant"""
    
    print("🧠 TESTING MEMORY SYSTEM INITIALIZATION")
    print("=" * 50)
    
    # Use the same config as the main API
    memory_config = MemoryTensorConfiguration(
        collection_name="alims_unified_memory",
        max_memories=10000,
        embedding_dimension=384,
        auto_consolidation=True,
        enable_insight_generation=True
    )
    
    print(f"Memory config: {memory_config}")
    
    try:
        print("Creating UnifiedMemoryTensorEngine...")
        memory_system = UnifiedMemoryTensorEngine(memory_config)
        
        print("Initializing memory system...")
        await memory_system.initialize()
        
        print("✅ Memory system initialized successfully!")
        return True
        
    except Exception as e:
        print(f"❌ Memory system initialization failed: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    # Set the same environment variables as the Docker container
    os.environ['VECTOR_DB_URL'] = 'http://localhost:6333'  # Use localhost for local testing
    
    result = asyncio.run(test_memory_init())
    
    if result:
        print("\n🎉 Memory system is working correctly!")
    else:
        print("\n💥 Memory system needs debugging!")
