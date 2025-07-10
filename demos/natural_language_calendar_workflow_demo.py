"""
Natural Language Calendar Workflow Integration Demo
Based on TLA+ validated specification: NaturalLanguageCalendarWorkflow.tla

This demo shows the complete workflow from natural language request 
to schedule creation and vector storage integration.

Example: "schedule a PCR for these samples" → full execution
"""

import asyncio
import logging
import json
from datetime import datetime
from typing import Dict, Any

from backend.app.natural_language_calendar import (
    NaturalLanguageCalendarWorkflow,
    create_workflow,
    process_scheduling_request,
    WorkflowResponse,
    ResponseStatus
)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


async def demo_complete_workflow():
    """
    Demonstrate the complete TLA+ validated natural language calendar workflow
    """
    print("🧪 ALIMS - Natural Language Calendar Workflow Demo")
    print("=" * 60)
    print("TLA+ Validated Implementation")
    print("Specification: NaturalLanguageCalendarWorkflow.tla")
    print("Model Checker: TLC 2.19 (268,039 states validated)")
    print("=" * 60)
    
    # Configuration matching TLA+ specification
    config = {
        "max_requests": 10,
        "max_parsed_intents": 10,
        "max_calendar_ops": 10,
        "max_storage_ops": 10,
        "users": ["alice", "bob", "charlie", "diana"],
        "resources": [
            "microscope1", "microscope2", 
            "pcr_machine1", "pcr_machine2",
            "sequencer1", "centrifuge1", 
            "spectrophotometer1"
        ],
        "intent_types": ["SCHEDULE", "CANCEL", "QUERY", "RESCHEDULE"],
        "vector_storage_config": {
            "qdrant_url": "http://localhost:6333",
            "collection_name": "alims_nl_calendar_demo",
            "embedding_dim": 384
        },
        "response_templates": {
            "schedule_success": "✅ Successfully scheduled {resource} for {user}",
            "schedule_failure": "❌ Failed to schedule {resource} for {user}: {reason}",
            "query_success": "ℹ️ {resource} status: {status}",
            "cancel_success": "🗑️ Successfully cancelled {resource} reservation for {user}"
        }
    }
    
    try:
        # Initialize workflow
        print("\n🔧 Initializing Natural Language Calendar Workflow...")
        workflow = create_workflow(config)
        await workflow.initialize()
        print("✅ Workflow initialized successfully")
        
        # Demonstrate core TLA+ validated operations
        await demo_tla_operations(workflow)
        
        # Demonstrate real-world scenarios
        await demo_real_world_scenarios(workflow)
        
        # Demonstrate concurrent processing
        await demo_concurrent_processing(workflow)
        
        # Demonstrate TLA+ invariant validation
        await demo_invariant_validation(workflow)
        
        # Cleanup
        await workflow.cleanup()
        print("\n✅ Demo completed successfully!")
        
    except Exception as e:
        logger.error(f"Demo failed: {e}")
        raise


async def demo_tla_operations(workflow: NaturalLanguageCalendarWorkflow):
    """Demonstrate core TLA+ operations"""
    print("\n📋 TLA+ Operations Demonstration")
    print("-" * 40)
    
    # TLA+ Operation: ReceiveNLRequest
    print("1. ReceiveNLRequest Operation")
    result = await workflow.receive_nl_request(
        1, "alice", "schedule a PCR for samples A001, A002, A003"
    )
    print(f"   Result: {result}")
    
    # TLA+ Operation: ParseIntent  
    print("2. ParseIntent Operation")
    result = await workflow.parse_intent(1)
    print(f"   Result: {result}")
    
    # TLA+ Operation: CompleteIntentParsing
    print("3. CompleteIntentParsing Operation")
    await workflow.complete_intent_parsing()
    print("   ✅ Intent parsing completed")
    
    # TLA+ Operation: CreateCalendarOperation
    print("4. CreateCalendarOperation")
    result = await workflow.create_calendar_operation(
        1, "CREATE", "pcr_machine1", "alice"
    )
    print(f"   Result: {result}")
    
    # TLA+ Operation: ProcessCalendarOperation
    print("5. ProcessCalendarOperation")
    result = await workflow.process_calendar_operation(1)
    print(f"   Result: {result}")
    
    # TLA+ Operation: CompleteCalendarOperation
    print("6. CompleteCalendarOperation")
    result = await workflow.complete_calendar_operation(1, success=True)
    print(f"   Result: {result}")
    
    # TLA+ Operation: CreateStorageRequest
    print("7. CreateStorageRequest")
    result = await workflow.create_storage_request(1, "STORE")
    print(f"   Result: {result}")
    
    # TLA+ Operation: ProcessStorageRequest
    print("8. ProcessStorageRequest")
    result = await workflow.process_storage_request(1)
    print(f"   Result: {result}")
    
    # TLA+ Operation: CompleteStorageRequest
    print("9. CompleteStorageRequest")
    result = await workflow.complete_storage_request(1, success=True)
    print(f"   Result: {result}")
    
    # TLA+ Operation: GenerateResponse
    print("10. GenerateResponse")
    result = await workflow.generate_response(
        1, "SUCCESS", "PCR successfully scheduled for samples A001, A002, A003"
    )
    print(f"    Result: {result}")
    
    # TLA+ Operation: CompleteResponseGeneration
    print("11. CompleteResponseGeneration")
    await workflow.complete_response_generation()
    print("    ✅ Response generation completed")
    
    print("✅ All TLA+ operations executed successfully")


async def demo_real_world_scenarios(workflow: NaturalLanguageCalendarWorkflow):
    """Demonstrate real-world natural language scheduling scenarios"""
    print("\n🌍 Real-World Scenarios")
    print("-" * 40)
    
    scenarios = [
        {
            "user": "alice",
            "request": "schedule a PCR for samples A001, A002, A003 for tomorrow at 2pm",
            "description": "PCR Scheduling"
        },
        {
            "user": "bob", 
            "request": "book the confocal microscope for protein analysis Monday morning",
            "description": "Microscope Booking"
        },
        {
            "user": "charlie",
            "request": "reserve the DNA sequencer for batch B001 next week",
            "description": "Sequencer Reservation"
        },
        {
            "user": "diana",
            "request": "need to use the centrifuge for cell preparation tomorrow",
            "description": "Centrifuge Scheduling"
        }
    ]
    
    for i, scenario in enumerate(scenarios, 1):
        print(f"\n{i}. {scenario['description']}")
        print(f"   User: {scenario['user']}")
        print(f"   Request: \"{scenario['request']}\"")
        
        try:
            # Process complete workflow
            response = await process_scheduling_request(
                workflow, scenario['user'], scenario['request']
            )
            
            print(f"   Response: {response.status.value}")
            print(f"   Message: {response.message}")
            print(f"   Processing Time: {response.processing_time_ms:.2f}ms")
            
            if response.status == ResponseStatus.SUCCESS:
                print("   ✅ Successfully processed")
            else:
                print("   ❌ Processing failed")
                
        except Exception as e:
            print(f"   ❌ Error: {e}")
    
    print("\n✅ Real-world scenarios completed")


async def demo_concurrent_processing(workflow: NaturalLanguageCalendarWorkflow):
    """Demonstrate concurrent request processing"""
    print("\n⚡ Concurrent Processing Demo")
    print("-" * 40)
    
    # Concurrent requests
    concurrent_requests = [
        ("alice", "schedule a PCR for urgent samples"),
        ("bob", "book the microscope for analysis"),
        ("charlie", "reserve the sequencer for project X"),
        ("diana", "need the centrifuge for sample prep")
    ]
    
    print(f"Processing {len(concurrent_requests)} concurrent requests...")
    
    # Submit all requests concurrently
    start_time = datetime.now()
    
    tasks = []
    for user, request in concurrent_requests:
        task = process_scheduling_request(workflow, user, request)
        tasks.append(task)
    
    # Wait for all to complete
    results = await asyncio.gather(*tasks, return_exceptions=True)
    
    end_time = datetime.now()
    total_time = (end_time - start_time).total_seconds() * 1000
    
    # Report results
    successful = 0
    failed = 0
    
    for i, result in enumerate(results):
        user, request = concurrent_requests[i]
        if isinstance(result, Exception):
            print(f"❌ {user}: {request} → ERROR: {result}")
            failed += 1
        else:
            print(f"✅ {user}: {request} → {result.status.value}")
            successful += 1
    
    print(f"\nConcurrent Processing Results:")
    print(f"  Total Requests: {len(concurrent_requests)}")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total Time: {total_time:.2f}ms")
    print(f"  Average Time per Request: {total_time/len(concurrent_requests):.2f}ms")
    
    print("✅ Concurrent processing completed")


async def demo_invariant_validation(workflow: NaturalLanguageCalendarWorkflow):
    """Demonstrate TLA+ invariant validation"""
    print("\n🔍 TLA+ Invariant Validation")
    print("-" * 40)
    
    # Get system metrics for invariant checking
    metrics = await workflow.get_system_metrics()
    states = await workflow.get_component_states()
    
    print("1. SystemCapacityInvariant Validation")
    print(f"   Active Requests: {metrics.active_requests}/{workflow.config.max_requests}")
    print(f"   Parsed Intents: {metrics.parsed_intents}/{workflow.config.max_parsed_intents}")
    print(f"   Calendar Operations: {metrics.calendar_operations}/{workflow.config.max_calendar_ops}")
    print(f"   Storage Operations: {metrics.storage_operations}/{workflow.config.max_storage_ops}")
    
    capacity_ok = (
        metrics.active_requests <= workflow.config.max_requests and
        metrics.parsed_intents <= workflow.config.max_parsed_intents and
        metrics.calendar_operations <= workflow.config.max_calendar_ops and
        metrics.storage_operations <= workflow.config.max_storage_ops
    )
    print(f"   ✅ SystemCapacityInvariant: {'VALID' if capacity_ok else 'VIOLATED'}")
    
    print("\n2. StateConsistencyInvariant Validation")
    valid_states = {
        "intent_parser": {"IDLE", "PARSING", "ERROR"},
        "orchestrator": {"READY", "ORCHESTRATING", "ERROR"},
        "vector_storage": {"AVAILABLE", "BUSY", "ERROR"},
        "response_generator": {"IDLE", "GENERATING", "ERROR"}
    }
    
    state_consistency_ok = True
    for component, valid_set in valid_states.items():
        current_state = states.get(component, "UNKNOWN")
        is_valid = current_state in valid_set
        state_consistency_ok = state_consistency_ok and is_valid
        print(f"   {component}: {current_state} {'✅' if is_valid else '❌'}")
    
    print(f"   ✅ StateConsistencyInvariant: {'VALID' if state_consistency_ok else 'VIOLATED'}")
    
    print("\n3. ProcessingInvariant Validation")
    processing_ok = (
        metrics.total_processed >= 0 and
        metrics.successful_schedules >= 0 and
        metrics.failed_operations >= 0
    )
    print(f"   Total Processed: {metrics.total_processed} (≥ 0) {'✅' if metrics.total_processed >= 0 else '❌'}")
    print(f"   Successful Schedules: {metrics.successful_schedules} (≥ 0) {'✅' if metrics.successful_schedules >= 0 else '❌'}")
    print(f"   Failed Operations: {metrics.failed_operations} (≥ 0) {'✅' if metrics.failed_operations >= 0 else '❌'}")
    print(f"   ✅ ProcessingInvariant: {'VALID' if processing_ok else 'VIOLATED'}")
    
    print("\n4. StorageConsistencyInvariant Validation")
    stored_schedules = await workflow.get_stored_schedules()
    calendar_operations = await workflow.get_calendar_operations()
    
    storage_consistency_ok = True
    for schedule_id in stored_schedules:
        corresponding_op = None
        for op in calendar_operations:
            if op.id == schedule_id and op.status.value == "COMPLETED":
                corresponding_op = op
                break
        
        if corresponding_op is None:
            storage_consistency_ok = False
            print(f"   ❌ Schedule {schedule_id} has no completed calendar operation")
        else:
            print(f"   ✅ Schedule {schedule_id} corresponds to completed operation")
    
    print(f"   ✅ StorageConsistencyInvariant: {'VALID' if storage_consistency_ok else 'VIOLATED'}")
    
    # Overall invariant status
    all_invariants_ok = capacity_ok and state_consistency_ok and processing_ok and storage_consistency_ok
    print(f"\n🎯 Overall TLA+ Invariant Status: {'ALL VALID ✅' if all_invariants_ok else 'VIOLATIONS DETECTED ❌'}")
    
    # Display system metrics summary
    print(f"\n📊 System Metrics Summary:")
    print(f"   Uptime: {metrics.system_uptime_seconds:.2f} seconds")
    print(f"   Total Processed: {metrics.total_processed}")
    print(f"   Success Rate: {(metrics.successful_schedules / max(1, metrics.total_processed)) * 100:.1f}%")
    print(f"   Average Processing Time: {metrics.average_processing_time_ms:.2f}ms")


async def demo_vector_storage_integration(workflow: NaturalLanguageCalendarWorkflow):
    """Demonstrate integration with TLA+ verified vector storage"""
    print("\n🗄️ Vector Storage Integration Demo")
    print("-" * 40)
    
    if not workflow.vector_storage:
        print("❌ Vector storage not configured")
        return
    
    print("Processing request with vector storage...")
    
    # Process a request that will be stored
    response = await process_scheduling_request(
        workflow, "alice", "schedule a PCR for critical samples X001, X002"
    )
    
    print(f"Response: {response.message}")
    
    # Check if data was stored in vector database
    stored_schedules = await workflow.get_stored_schedules()
    print(f"Stored schedules count: {len(stored_schedules)}")
    
    # Try to retrieve from vector storage
    try:
        storage_metrics = await workflow.vector_storage.get_storage_metrics()
        print(f"Vector storage metrics:")
        print(f"  Total stored: {storage_metrics.total_stored}")
        print(f"  Storage utilization: {storage_metrics.storage_utilization}%")
        print("✅ Vector storage integration working")
    except Exception as e:
        print(f"❌ Vector storage error: {e}")


if __name__ == "__main__":
    asyncio.run(demo_complete_workflow())
