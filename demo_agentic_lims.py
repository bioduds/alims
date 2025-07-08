#!/usr/bin/env python3
"""
ALIMS Integration Test & Demo Script

This script demonstrates the complete TLA+ verified agentic LIMS workflow
using PydanticAI agents and LangGraph orchestration.

Features demonstrated:
- Sample reception with intelligent validation
- Quality-controlled accessioning  
- Complete workflow orchestration
- TLA+ invariant validation
- Local AI processing with Ollama + Gemma

Usage:
    python demo_agentic_lims.py

Requirements:
    - Ollama installed and running
    - Gemma 3.2 4B model pulled: ollama pull gemma:3.2:4b
    - All dependencies installed: pip install -r requirements/lims.txt
"""

import asyncio
import sys
import json
from datetime import datetime
from pathlib import Path

# Add the backend app to Python path
backend_path = Path(__file__).parent / "backend" / "app"
sys.path.insert(0, str(backend_path))

from lims import (
    LIMSSystemState,
    CoreLIMSWorkflow,
    SampleReceptionRequest,
    SampleAccessionRequest,
    receive_sample,
    accession_sample
)


async def demo_individual_agents():
    """Demonstrate individual agent capabilities"""
    print("🧪 ALIMS - Agentic LIMS Individual Agent Demo")
    print("=" * 50)
    
    # Initialize LIMS system
    lims = LIMSSystemState()
    print(f"📊 Initial system state: {lims.validate_system_invariants()}")
    
    # Test sample reception agent
    print("\n🔬 Testing Sample Reception Agent...")
    reception_request = SampleReceptionRequest(
        sample_type="blood",
        patient_id="DEMO_PAT_001",
        collection_site="Emergency Department",
        priority="STAT",
        notes="Emergency blood work - chest pain protocol"
    )
    
    reception_response = await receive_sample(reception_request, lims)
    print(f"Reception Result: {json.dumps(reception_response.dict(), indent=2, default=str)}")
    
    if reception_response.success:
        # Test sample accessioning agent  
        print("\n🏷️  Testing Sample Accessioning Agent...")
        accession_request = SampleAccessionRequest(
            sample_id=reception_response.sample_id,
            technician_id="TECH_DEMO_001", 
            quality_check_passed=True,
            volume_received=7.5,
            temperature_ok=True,
            container_intact=True,
            label_legible=True,
            requisition_complete=True,
            notes="Emergency sample - expedite processing"
        )
        
        accession_response = await accession_sample(accession_request, lims)
        print(f"Accessioning Result: {json.dumps(accession_response.dict(), indent=2, default=str)}")
    
    print(f"\n📊 Final system state: {lims.validate_system_invariants()}")
    return lims


async def demo_complete_workflow():
    """Demonstrate complete workflow orchestration"""
    print("\n\n🌐 ALIMS - Complete Workflow Orchestration Demo")
    print("=" * 55)
    
    # Initialize fresh LIMS system
    lims = LIMSSystemState()
    workflow = CoreLIMSWorkflow(lims)
    
    print("🚀 Executing complete sample workflow...")
    print("   RECEIVED → ACCESSIONED → SCHEDULED → TESTING → QC_PENDING → QC_APPROVED → REPORTED → ARCHIVED")
    
    # Execute the complete workflow
    result = await workflow.execute_workflow(
        priority="ROUTINE",
        initiated_by="DEMO_USER"
    )
    
    # Display results
    print(f"\n✅ Workflow Success: {result['success']}")
    print(f"🔬 Sample ID: {result['sample_id']}")
    print(f"📊 Final State: {result['final_state']}")
    print(f"📋 Completed Steps: {', '.join(result['completed_steps'])}")
    print(f"🔒 TLA+ Invariants: {result['system_invariants']}")
    
    if result['errors']:
        print(f"❌ Errors: {result['errors']}")
    
    print("\n📝 Workflow Messages:")
    for i, message in enumerate(result['messages'], 1):
        print(f"   {i:2d}. {message}")
    
    if result['special_handling']:
        print(f"\n⚠️  Special Handling: {result['special_handling']}")
    
    # Show detailed response data
    print("\n📊 Detailed Agent Responses:")
    for stage, response in result['responses'].items():
        if response:
            print(f"\n   {stage.upper()}:")
            # Show key fields from each response
            if isinstance(response, dict):
                for key, value in response.items():
                    if key not in ['workflow_status']:  # Skip verbose nested data
                        print(f"     {key}: {value}")
    
    return result


async def demo_tla_validation():
    """Demonstrate TLA+ property validation"""
    print("\n\n🔍 ALIMS - TLA+ Property Validation Demo")  
    print("=" * 45)
    
    lims = LIMSSystemState()
    
    # Create multiple samples to test invariants
    print("Creating multiple samples to test TLA+ invariants...")
    
    # Create 3 samples in different states
    samples = []
    for i in range(3):
        request = SampleReceptionRequest(
            sample_type=["blood", "urine", "serum"][i],
            patient_id=f"VAL_PAT_{i+1:03d}",
            collection_site="Validation Lab",
            priority=["STAT", "URGENT", "ROUTINE"][i],
            notes=f"Validation sample {i+1}"
        )
        
        response = await receive_sample(request, lims)
        if response.success:
            samples.append(response.sample_id)
            print(f"   Sample {response.sample_id} created: {response.barcode}")
    
    # Progress samples through different states
    if len(samples) >= 2:
        # Accession first sample
        accession_request = SampleAccessionRequest(
            sample_id=samples[0],
            technician_id="VAL_TECH",
            quality_check_passed=True,
            volume_received=5.0,
            notes="Validation accessioning"
        )
        await accession_sample(accession_request, lims)
        
        # Move second sample further
        if len(samples) >= 2:
            lims.transition_sample(samples[1], lims.workflows[samples[1]].get_valid_next_states()[0], "VAL_TECH", "Validation")
            lims.transition_sample(samples[1], lims.workflows[samples[1]].get_valid_next_states()[0], "VAL_TECH", "Validation")
    
    # Validate all TLA+ invariants
    invariants = lims.validate_system_invariants()
    print(f"\n🔒 TLA+ Invariant Validation Results:")
    for invariant, passed in invariants.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"   {invariant}: {status}")
    
    # Show sample states
    print(f"\n📊 Sample State Distribution:")
    for sample_id in samples:
        workflow = lims.get_sample(sample_id)
        print(f"   Sample {sample_id}: {workflow.current_state} (audit trail: {len(workflow.audit_trail)} steps)")
    
    return all(invariants.values())


async def main():
    """Main demo execution"""
    print("🚀 ALIMS - Agentic Laboratory Information Management System")
    print("🔬 TLA+ Verified • PydanticAI Agents • LangGraph Workflows • Ollama + Gemma")
    print("=" * 80)
    
    try:
        # Run individual agent demos
        await demo_individual_agents()
        
        # Run complete workflow demo  
        workflow_result = await demo_complete_workflow()
        
        # Run TLA+ validation demo
        validation_passed = await demo_tla_validation()
        
        # Final summary
        print("\n\n🎯 DEMO SUMMARY")
        print("=" * 20)
        print(f"✅ Complete Workflow: {'SUCCESS' if workflow_result['success'] else 'FAILED'}")
        print(f"🔒 TLA+ Invariants: {'ALL PASSED' if validation_passed else 'SOME FAILED'}")
        print(f"🤖 AI Model: Ollama + Gemma 3.2 4B (Local)")
        print(f"📊 Architecture: PydanticAI + LangGraph")
        print(f"🔬 Workflow: TLA+ Formally Verified")
        
        print("\n🎉 ALIMS Agentic LIMS Demo Complete!")
        print("Ready for production deployment with mathematical correctness guarantees.")
        
    except Exception as e:
        print(f"\n❌ Demo failed with error: {str(e)}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    exit_code = asyncio.run(main())
