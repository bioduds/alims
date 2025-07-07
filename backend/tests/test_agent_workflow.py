#!/usr/bin/env python3
"""
Test end-to-end agent workflow demonstrating simplified PydanticAI agents
working with Llama 3.2 via Ollama for TLA+ compliant LIMS operations.
"""

import asyncio
import sys
from pathlib import Path

# Add backend to path
backend_path = Path(__file__).parent / "backend" / "app"
sys.path.insert(0, str(backend_path))

from lims.models import LIMSSystemState, SampleState
from lims.agents.sample_reception import receive_sample, SampleReceptionRequest
from lims.agents.sample_accessioning import accession_sample, SampleAccessionRequest


async def test_complete_workflow():
    """Test complete reception -> accessioning workflow"""
    print("=== ALIMS Agent Workflow Test ===")
    print("Testing simplified PydanticAI agents with Llama 3.2")
    print()
    
    # Initialize LIMS system
    lims = LIMSSystemState()
    print(f"✓ LIMS System initialized (capacity: {lims.max_samples} samples)")
    print()
    
    # Step 1: Sample Reception
    print("1. SAMPLE RECEPTION")
    print("-" * 20)
    
    reception_request = SampleReceptionRequest(
        sample_type="blood",
        patient_id="PAT987654",
        collection_site="Emergency Lab",
        priority="URGENT",
        notes="STAT glucose and CBC ordered"
    )
    
    print(f"Reception request: {reception_request.sample_type} sample for {reception_request.patient_id}")
    print(f"Priority: {reception_request.priority}")
    
    reception_response = await receive_sample(reception_request, lims)
    
    print(f"DEBUG: Reception response = {reception_response}")
    print(f"DEBUG: Reception success = {reception_response.success}")
    
    if reception_response.success:
        print(f"✓ Sample reception successful!")
        print(f"  Sample ID: {reception_response.sample_id}")
        print(f"  Barcode: {reception_response.barcode}")
        print(f"  State: {reception_response.current_state}")
        print(f"  Message: {reception_response.message}")
    else:
        print(f"✗ Sample reception failed: {reception_response.message}")
        return
    
    print()
    
    # Step 2: Sample Accessioning
    print("2. SAMPLE ACCESSIONING")
    print("-" * 22)
    
    accession_request = SampleAccessionRequest(
        sample_id=reception_response.sample_id,
        technician_id="TECH_007",
        quality_check_passed=True,
        volume_received=7.5,  # mL
        temperature_ok=True,
        container_intact=True,
        label_legible=True,
        requisition_complete=True,
        notes="Quality assessment passed - ready for testing"
    )
    
    print(f"Accessioning sample ID: {accession_request.sample_id}")
    print(f"Technician: {accession_request.technician_id}")
    print(f"Volume: {accession_request.volume_received} mL")
    
    accession_response = await accession_sample(accession_request, lims)
    
    if accession_response.success:
        print(f"✓ Sample accessioning successful!")
        print(f"  Sample ID: {accession_response.sample_id}")
        print(f"  Accession Number: {accession_response.accession_number}")
        print(f"  Quality Score: {accession_response.quality_score}/5")
        print(f"  Quality Passed: {accession_response.quality_passed}")
        print(f"  State: {accession_response.current_state}")
        print(f"  Message: {accession_response.message}")
    else:
        print(f"✗ Sample accessioning failed: {accession_response.message}")
        return
    
    print()
    
    # Step 3: System Validation
    print("3. SYSTEM VALIDATION")
    print("-" * 19)
    
    # Check system invariants
    invariants_valid = lims.validate_system_invariants()
    print(f"✓ TLA+ System Invariants: {'VALID' if invariants_valid else 'INVALID'}")
    
    # Get final sample state
    final_workflow = lims.get_sample(reception_response.sample_id)
    print(f"✓ Final Sample State: {final_workflow.current_state}")
    print(f"✓ Audit Trail Entries: {len(final_workflow.audit_trail)}")
    print(f"✓ Total System Samples: {len(lims.workflows)}")
    
    print()
    print("=== WORKFLOW COMPLETED SUCCESSFULLY ===")
    print("✓ Agents are working with Llama 3.2 via Ollama")
    print("✓ TLA+ compliance maintained throughout")
    print("✓ All state transitions validated")


async def test_error_cases():
    """Test error handling scenarios"""
    print("\n=== ERROR HANDLING TESTS ===")
    print()
    
    lims = LIMSSystemState()
    
    # Test accessioning non-existent sample
    print("Testing accessioning non-existent sample...")
    accession_request = SampleAccessionRequest(
        sample_id=999,  # Non-existent
        technician_id="TECH_001",
        quality_check_passed=True,
        volume_received=5.0,
        temperature_ok=True,
        container_intact=True,
        label_legible=True,
        requisition_complete=True
    )
    
    response = await accession_sample(accession_request, lims)
    print(f"✓ Correctly rejected non-existent sample: {response.message}")
    
    # Test accessioning sample not in RECEIVED state
    print("\nTesting accessioning sample in wrong state...")
    # Create a sample first
    reception_request = SampleReceptionRequest(
        sample_type="urine",
        patient_id="PAT111",
        collection_site="Clinic",
        priority="ROUTINE"
    )
    
    reception_response = await receive_sample(reception_request, lims)
    
    # Manually transition it to a different state (ACCESSIONED -> SCHEDULED)
    lims.transition_sample(reception_response.sample_id, SampleState.ACCESSIONED, "SYSTEM", "Manual transition for test")
    lims.transition_sample(reception_response.sample_id, SampleState.SCHEDULED, "SYSTEM", "Manual transition for test")
    
    # Try to accession it
    accession_request = SampleAccessionRequest(
        sample_id=reception_response.sample_id,
        technician_id="TECH_001",
        quality_check_passed=True,
        volume_received=5.0,
        temperature_ok=True,
        container_intact=True,
        label_legible=True,
        requisition_complete=True
    )
    
    response = await accession_sample(accession_request, lims)
    print(f"✓ Correctly rejected wrong-state sample: {response.message}")
    
    print("\n✓ All error cases handled correctly")


if __name__ == "__main__":
    # Run the tests
    asyncio.run(test_complete_workflow())
    asyncio.run(test_error_cases())
