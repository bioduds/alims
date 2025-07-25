#!/usr/bin/env python3
"""Simulate ALIMS workflow with Langfuse monitoring"""

import os
import time
import uuid
from datetime import datetime
from langfuse import Langfuse

def simulate_alims_workflow():
    """Simulate a complete ALIMS workflow with monitoring"""
    
    print("🧪 Simulating ALIMS Workflow with Langfuse Monitoring")
    print("=" * 55)
    
    # Initialize Langfuse
    client = Langfuse()
    workflow_id = str(uuid.uuid4())
    
    print(f"📋 Workflow ID: {workflow_id}")
    print(f"🏥 Container: {os.getenv('HOSTNAME', 'unknown')}")
    print(f"🌐 Langfuse Host: {os.getenv('LANGFUSE_HOST')}")
    
    try:
        # 1. Workflow Started
        print("\n1️⃣ Starting workflow...")
        client.create_event(
            name="workflow_started",
            metadata={
                "workflow_id": workflow_id,
                "priority": "URGENT",
                "initiated_by": "lab_tech_001",
                "system": "ALIMS",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Workflow start logged")
        time.sleep(0.5)
        
        # 2. Sample Reception
        print("2️⃣ Processing sample reception...")
        client.create_event(
            name="sample_reception",
            metadata={
                "workflow_id": workflow_id,
                "sample_id": "SAMPLE_12345",
                "status": "received",
                "step": "reception",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Sample reception logged")
        time.sleep(0.8)
        
        # 3. Quality Control
        print("3️⃣ Running quality control...")
        client.create_event(
            name="quality_control",
            metadata={
                "workflow_id": workflow_id,
                "sample_id": "SAMPLE_12345",
                "qc_result": "passed",
                "step": "quality_control",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Quality control logged")
        time.sleep(0.6)
        
        # 4. Analysis Processing
        print("4️⃣ Processing analysis...")
        client.create_event(
            name="analysis_processing",
            metadata={
                "workflow_id": workflow_id,
                "sample_id": "SAMPLE_12345",
                "analysis_type": "blood_chemistry",
                "step": "analysis",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Analysis processing logged")
        time.sleep(1.0)
        
        # 5. Results Validation
        print("5️⃣ Validating results...")
        client.create_event(
            name="results_validation",
            metadata={
                "workflow_id": workflow_id,
                "sample_id": "SAMPLE_12345",
                "validation_status": "approved",
                "step": "validation",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Results validation logged")
        time.sleep(0.4)
        
        # 6. Workflow Completed
        print("6️⃣ Completing workflow...")
        client.create_event(
            name="workflow_completed",
            metadata={
                "workflow_id": workflow_id,
                "sample_id": "SAMPLE_12345",
                "status": "completed",
                "success": True,
                "total_duration": "3.3 seconds",
                "container": os.getenv("HOSTNAME", "unknown"),
                "timestamp": datetime.now().isoformat()
            }
        )
        print("   ✅ Workflow completion logged")
        
        # Flush all data
        print("\n📤 Sending all data to Langfuse...")
        client.flush()
        
        print("\n🎉 ALIMS Workflow Simulation Complete!")
        print(f"📊 View workflow data at: {os.getenv('LANGFUSE_HOST')}")
        print(f"🔍 Search for workflow_id: {workflow_id}")
        
        return True
        
    except Exception as e:
        print(f"\n❌ Workflow simulation failed: {e}")
        return False

if __name__ == "__main__":
    simulate_alims_workflow()
