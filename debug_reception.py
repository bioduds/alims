#!/usr/bin/env python3
"""
Debug reception agent issue
"""

import asyncio
import sys
from pathlib import Path

# Add backend to path
backend_path = Path(__file__).parent / "backend" / "app"
sys.path.insert(0, str(backend_path))

from lims.models import LIMSSystemState
from lims.agents.sample_reception import receive_sample, SampleReceptionRequest


async def debug_reception():
    """Debug reception agent"""
    print("=== DEBUG RECEPTION AGENT ===")
    
    lims = LIMSSystemState()
    
    # Simple request
    request = SampleReceptionRequest(
        sample_type="blood",
        patient_id="DEBUG001",
        collection_site="Debug Lab",
        priority="ROUTINE"
    )
    
    print(f"Making request: {request}")
    
    try:
        response = await receive_sample(request, lims)
        print(f"Response: {response}")
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    asyncio.run(debug_reception())
