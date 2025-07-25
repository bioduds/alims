#!/usr/bin/env python3
"""Debug Langfuse initialization"""

import os
import sys
from dotenv import load_dotenv

# Load environment
load_dotenv()

print("=== Environment Check ===")
print(f"LANGFUSE_PUBLIC_KEY: {bool(os.getenv('LANGFUSE_PUBLIC_KEY'))}")
print(f"LANGFUSE_SECRET_KEY: {bool(os.getenv('LANGFUSE_SECRET_KEY'))}")
print(f"LANGFUSE_HOST: {os.getenv('LANGFUSE_HOST', 'Not set')}")

# Try importing Langfuse
try:
    from langfuse import Langfuse
    print("✅ Langfuse import successful")
    
    # Try creating client
    client = Langfuse()
    print("✅ Langfuse client created")
    
    # Try creating a test trace
    trace = client.trace(name="debug_test", metadata={"test": True})
    print("✅ Test trace created")
    
    # Flush
    client.flush()
    print("✅ Client flushed")
    
except Exception as e:
    print(f"❌ Error: {e}")
    import traceback
    traceback.print_exc()
