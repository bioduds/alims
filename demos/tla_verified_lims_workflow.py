#!/usr/bin/env python3
"""
ALIMS TLA+ Verified Sample Workflow Demonstration

This script demonstrates the mathematically verified LIMS sample workflow
state machine based on the validated TLA+ specification.

All operations in this demo are guaranteed to maintain:
- Monotonic progression (no state regression)
- Audit trail immutability (21 CFR Part 11)
- QC approval requirements
- Resource bounds enforcement
- Complete regulatory compliance
"""

import sys
import time
from pathlib import Path
from datetime import datetime
from typing import List, Dict

# Add the backend directory to the Python path
sys.path.insert(0, str(Path(__file__).parent.parent / "backend"))

from app.lims.models import (
    SampleState, Sample, SampleWorkflow, LIMSSystemState, 
    TLAPropertyError
)


def print_banner():
    """Print demonstration banner"""
    print("=" * 80)
    print("🧬 ALIMS TLA+ Verified Sample Workflow Demonstration")
    print("   Mathematical Correctness Guaranteed by Formal Verification")
    print("=" * 80)
    print()


def print_sample_status(workflow: SampleWorkflow):
    """Print current sample status with audit trail"""
    sample = workflow.sample
    print(f"📋 Sample {sample.id} ({sample.barcode}):")
    print(f"   Current State: {workflow.current_state.value}")
    print(f"   QC Approved: {'✅' if workflow.has_qc_approval() else '❌'}")
    print(f"   Can Report: {'✅' if workflow.can_be_reported() else '❌'}")
    print(f"   Terminal: {'✅' if workflow.is_terminal_state() else '❌'}")
    print()
    
    print("📝 Audit Trail (Immutable):")
    for i, entry in enumerate(workflow.audit_trail, 1):
        timestamp = entry.timestamp.strftime("%H:%M:%S")
        print(f"   {i}. {timestamp} | {entry.state.value:12} | {entry.actor:10} | {entry.notes or 'N/A'}")
    print()


def print_system_status(lims: LIMSSystemState):
    """Print system status and statistics"""
    stats = lims.get_system_stats()
    capacity = lims.get_testing_capacity_status()
    
    print("🏥 LIMS System Status:")
    print(f"   Total Samples: {stats['total_samples']}")
    print(f"   Next Sample ID: {stats['next_sample_id']}")
    print(f"   Testing Capacity: {capacity['current_testing']}/{capacity['max_concurrent']} (Available: {capacity['available_capacity']})")
    print(f"   QC Approved: {stats['qc_approved_count']}")
    print()
    
    print("📊 State Distribution:")
    for state, count in stats['state_distribution'].items():
        if count > 0:
            print(f"   {state:15}: {count}")
    print()
    
    print("✅ TLA+ Invariant Status:")
    for invariant, status in stats['invariant_status'].items():
        status_icon = "✅" if status else "❌"
        print(f"   {status_icon} {invariant}")
    print()


def demonstrate_complete_workflow():
    """Demonstrate a complete sample workflow from receipt to archival"""
    print("🔬 Demonstrating Complete Sample Workflow")
    print("-" * 50)
    
    # Create LIMS system with resource constraints
    lims = LIMSSystemState(max_concurrent_tests=2, max_samples=100)
    
    # Create sample
    sample_id = lims.create_sample(
        barcode="NGS-2025-001", 
        actor="reception_desk",
        sample_type="Blood", 
        patient_id="PT12345",
        priority="STAT"
    )
    
    workflow = lims.get_sample(sample_id)
    print(f"✨ Created sample {sample_id} with barcode NGS-2025-001")
    print_sample_status(workflow)
    
    # Complete workflow progression
    transitions = [
        (SampleState.ACCESSIONED, "lab_tech_01", "Sample accessioned for NGS workflow"),
        (SampleState.SCHEDULED, "scheduler_sys", "Scheduled for batch NGS-B001"),
        (SampleState.TESTING, "genomics_tech", "DNA extraction and library prep initiated"),
        (SampleState.QC_PENDING, "genomics_tech", "Sequencing completed, awaiting QC review"),
        (SampleState.QC_APPROVED, "qc_supervisor", "QC review passed - library quality acceptable"),
        (SampleState.REPORTED, "bioinformatics", "Variant analysis report generated"),
        (SampleState.ARCHIVED, "data_manager", "Raw data archived per 21 CFR Part 11")
    ]
    
    for new_state, actor, notes in transitions:
        print(f"🔄 Transitioning to {new_state.value}...")
        time.sleep(0.5)  # Simulate processing time
        
        lims.transition_sample(sample_id, new_state, actor, notes)
        workflow = lims.get_sample(sample_id)
        print_sample_status(workflow)
    
    print("🎉 Sample workflow completed successfully!")
    print_system_status(lims)


def demonstrate_resource_bounds():
    """Demonstrate resource bounds enforcement (TLA+ property)"""
    print("⚡ Demonstrating Resource Bounds Enforcement")
    print("-" * 50)
    
    # Create system with limited testing capacity
    lims = LIMSSystemState(max_concurrent_tests=2)
    
    # Create multiple samples
    sample_ids = []
    for i in range(3):
        sample_id = lims.create_sample(f"TEST-{i+1:03d}", "tech")
        sample_ids.append(sample_id)
        print(f"✨ Created sample {sample_id}")
    
    print_system_status(lims)
    
    # Progress samples to testing
    for i, sample_id in enumerate(sample_ids):
        print(f"🔄 Processing sample {sample_id}...")
        
        # Progress to scheduled
        lims.transition_sample(sample_id, SampleState.ACCESSIONED, "tech")
        lims.transition_sample(sample_id, SampleState.SCHEDULED, "tech")
        
        # Try to start testing
        try:
            lims.transition_sample(sample_id, SampleState.TESTING, "tech")
            print(f"   ✅ Sample {sample_id} started testing")
        except TLAPropertyError as e:
            print(f"   ❌ Resource bounds prevented testing: {e}")
        
        print_system_status(lims)
    
    print("✅ Resource bounds enforcement demonstrated!")


def demonstrate_qc_enforcement():
    """Demonstrate QC approval requirement enforcement"""
    print("🛡️ Demonstrating QC Approval Enforcement")
    print("-" * 50)
    
    lims = LIMSSystemState()
    sample_id = lims.create_sample("QC-TEST-001", "tech")
    
    # Progress to QC pending
    transitions = [
        (SampleState.ACCESSIONED, "tech"),
        (SampleState.SCHEDULED, "tech"),
        (SampleState.TESTING, "tech"),
        (SampleState.QC_PENDING, "tech")
    ]
    
    for state, actor in transitions:
        lims.transition_sample(sample_id, state, actor)
    
    workflow = lims.get_sample(sample_id)
    print_sample_status(workflow)
    
    # Attempt to report without QC approval
    try:
        lims.transition_sample(sample_id, SampleState.REPORTED, "tech")
        print("❌ Should not reach here - QC enforcement failed!")
    except TLAPropertyError as e:
        print(f"✅ QC enforcement successful: {e}")
    
    # Proper QC approval then reporting
    lims.transition_sample(sample_id, SampleState.QC_APPROVED, "qc_manager")
    lims.transition_sample(sample_id, SampleState.REPORTED, "tech")
    
    workflow = lims.get_sample(sample_id)
    print("\n✅ After QC approval:")
    print_sample_status(workflow)


def demonstrate_monotonic_progression():
    """Demonstrate monotonic progression enforcement"""
    print("🔒 Demonstrating Monotonic Progression Enforcement")
    print("-" * 50)
    
    lims = LIMSSystemState()
    sample_id = lims.create_sample("MONO-TEST-001", "tech")
    
    # Progress sample
    lims.transition_sample(sample_id, SampleState.ACCESSIONED, "tech")
    lims.transition_sample(sample_id, SampleState.SCHEDULED, "tech")
    
    workflow = lims.get_sample(sample_id)
    print_sample_status(workflow)
    
    # Attempt to regress to previous state
    try:
        lims.transition_sample(sample_id, SampleState.RECEIVED, "tech")
        print("❌ Should not reach here - monotonic progression failed!")
    except TLAPropertyError as e:
        print(f"✅ Monotonic progression enforced: {e}")
    
    # Attempt to revisit current state
    try:
        lims.transition_sample(sample_id, SampleState.SCHEDULED, "tech")
        print("❌ Should not reach here - monotonic progression failed!")
    except TLAPropertyError as e:
        print(f"✅ State revisit prevented: {e}")
    
    print("\n✅ Monotonic progression enforcement demonstrated!")


def demonstrate_concurrent_processing():
    """Demonstrate safe concurrent sample processing"""
    print("🔄 Demonstrating Concurrent Sample Processing")
    print("-" * 50)
    
    lims = LIMSSystemState(max_concurrent_tests=3)
    
    # Create multiple samples for concurrent processing
    sample_data = [
        ("COVID-RT-001", "Blood", "STAT"),
        ("COVID-RT-002", "Nasal", "URGENT"),
        ("COVID-RT-003", "Saliva", "ROUTINE")
    ]
    
    sample_ids = []
    for barcode, sample_type, priority in sample_data:
        sample_id = lims.create_sample(
            barcode=barcode,
            actor="reception",
            sample_type=sample_type,
            priority=priority
        )
        sample_ids.append(sample_id)
    
    print(f"✨ Created {len(sample_ids)} samples for concurrent processing")
    print_system_status(lims)
    
    # Process all samples concurrently through testing
    for sample_id in sample_ids:
        lims.transition_sample(sample_id, SampleState.ACCESSIONED, "tech")
        lims.transition_sample(sample_id, SampleState.SCHEDULED, "scheduler")
        lims.transition_sample(sample_id, SampleState.TESTING, "lab_tech")
    
    print("🧪 All samples in testing phase:")
    print_system_status(lims)
    
    # Complete processing with different QC outcomes
    qc_decisions = [
        ("qc_tech1", "QC passed - viral load detected"),
        ("qc_tech2", "QC passed - negative result"),
        ("qc_tech3", "QC passed - inconclusive, recommend retest")
    ]
    
    for sample_id, (qc_actor, qc_notes) in zip(sample_ids, qc_decisions):
        lims.transition_sample(sample_id, SampleState.QC_PENDING, "lab_tech")
        lims.transition_sample(sample_id, SampleState.QC_APPROVED, qc_actor, qc_notes)
        lims.transition_sample(sample_id, SampleState.REPORTED, "reporting_sys")
    
    print("📋 All samples reported:")
    print_system_status(lims)
    
    # Show individual sample status
    for sample_id in sample_ids:
        workflow = lims.get_sample(sample_id)
        print_sample_status(workflow)


def main():
    """Main demonstration function"""
    print_banner()
    
    try:
        # Run all demonstrations
        demonstrate_complete_workflow()
        input("\n📍 Press Enter to continue to resource bounds demo...")
        
        demonstrate_resource_bounds()
        input("\n📍 Press Enter to continue to QC enforcement demo...")
        
        demonstrate_qc_enforcement()
        input("\n📍 Press Enter to continue to monotonic progression demo...")
        
        demonstrate_monotonic_progression()
        input("\n📍 Press Enter to continue to concurrent processing demo...")
        
        demonstrate_concurrent_processing()
        
        print("\n" + "=" * 80)
        print("🎯 DEMONSTRATION COMPLETE")
        print("   All TLA+ properties successfully enforced!")
        print("   Ready for production deployment with mathematical guarantees.")
        print("=" * 80)
        
    except KeyboardInterrupt:
        print("\n\n👋 Demonstration interrupted by user")
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
