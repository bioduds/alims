"""
Langfuse monitoring configuration and setup for ALIMS
"""

import os
from typing import Optional

# Langfuse configuration
LANGFUSE_PUBLIC_KEY = os.getenv("LANGFUSE_PUBLIC_KEY")
LANGFUSE_SECRET_KEY = os.getenv("LANGFUSE_SECRET_KEY") 
LANGFUSE_HOST = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")

# Monitoring settings
ENABLE_MONITORING = os.getenv("ENABLE_LANGFUSE_MONITORING", "true").lower() == "true"
WORKFLOW_SESSION_PREFIX = "alims_lims_workflow"

def get_langfuse_config() -> dict:
    """Get Langfuse configuration"""
    return {
        "public_key": LANGFUSE_PUBLIC_KEY,
        "secret_key": LANGFUSE_SECRET_KEY,
        "host": LANGFUSE_HOST,
        "enabled": ENABLE_MONITORING and bool(LANGFUSE_PUBLIC_KEY and LANGFUSE_SECRET_KEY)
    }
