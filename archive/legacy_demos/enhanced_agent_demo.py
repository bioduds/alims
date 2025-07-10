#!/usr/bin/env python3
"""
Enhanced Main Interface Agent Demo
Demonstrates the TLA+ validated agent system with LIMS scenarios.
"""

import asyncio
import logging
import json
import time
from pathlib import Path

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Import our enhanced system
from backend.app.intelligence.enhanced_main_interface_service import EnhancedLIMSMainInterfaceService


async def demo_basic_functionality():
    """Demonstrate basic functionality of the enhanced system."""
    print("\n" + "="*60)
    print("ENHANCED MAIN INTERFACE AGENT SYSTEM DEMO")
    print("Based on TLA+ Validated Architecture")
    print("="*60)
    
    # Initialize the enhanced service
    config = {
        'max_conversations': 20,
        'max_agents': 10,
        'max_queries': 50,
        'query_timeout': 15.0,
        'agent_timeout': 30.0,
        'enable_audit': True,
        'enable_monitoring': True
    }
    
    service = EnhancedLIMSMainInterfaceService(config)
    print("\n1. Initializing Enhanced Main Interface Agent System...")
    
    try:
        await service.initialize()
        print("✓ System initialized successfully!")
        
        # Show system status
        status = await service.get_system_status()
        print(f"\n2. System Status:")
        print(f"   - Status: {status['status']}")
        print(f"   - Registered LIMS Agents: {len(status['lims_agents'])}")
        print(f"   - Knowledge Base Size: {status['knowledge_base_size']}")
        print(f"   - Background Tasks: {status['background_tasks']}")
        
        # Show registered agents
        print(f"\n3. Registered LIMS Agents:")
        for agent_id, agent_info in status['lims_agents'].items():
            capabilities = ', '.join(list(agent_info['capabilities'])[:3])
            if len(agent_info['capabilities']) > 3:
                capabilities += f" (+{len(agent_info['capabilities'])-3} more)"
            print(f"   - {agent_id}: {capabilities}")
        
        # Demo conversation scenarios
        await demo_sample_management_scenario(service)
        await demo_workflow_automation_scenario(service)
        await demo_compliance_verification_scenario(service)
        await demo_knowledge_base_queries(service)
        await demo_concurrent_conversations(service)
        
        # Final system status
        final_status = await service.get_system_status()
        print(f"\n8. Final System Metrics:")
        print(f"   - Active Conversations: {final_status.get('active_conversations', 0)}")
        print(f"   - Total Queries Processed: {final_status.get('system_metrics', {}).get('queries', 0)}")
        print(f"   - System Uptime: {final_status.get('uptime', 0):.2f} seconds")
        
    except Exception as e:
        logger.error(f"Demo failed: {e}")
        print(f"❌ Demo failed: {e}")
        
    finally:
        print("\n9. Shutting down system...")
        await service.shutdown()
        print("✓ System shutdown completed")


async def demo_sample_management_scenario(service):
    """Demo sample management capabilities."""
    print(f"\n4. Sample Management Scenario:")
    
    # Start conversation for sample tracking
    conv_id = await service.start_conversation(
        context={
            "sample_id": "LAB001",
            "sample_type": "blood",
            "priority": "high",
            "collection_date": "2024-01-15",
            "requested_tests": ["HPLC", "GC_MS", "UV_VIS"]
        },
        required_capability="sample_tracking"
    )
    print(f"   ✓ Started sample management conversation: {conv_id[:8]}...")
    
    # Simulate user interactions
    interactions = [
        "What is the current status of sample LAB001?",
        "Schedule HPLC analysis for this sample with high priority",
        "Update sample status to 'in_analysis'",
        "Generate a chain of custody report for this sample"
    ]
    
    for i, message in enumerate(interactions, 1):
        print(f"   User: {message}")
        response = await service.send_message(
            conversation_id=conv_id,
            message=message,
            user_id="lab_tech_001"
        )
        
        # Show abbreviated response
        response_text = response.get("response", "No response")[:80]
        if len(response.get("response", "")) > 80:
            response_text += "..."
        print(f"   Agent: {response_text}")
        
        # Small delay for realism
        await asyncio.sleep(0.2)


async def demo_workflow_automation_scenario(service):
    """Demo workflow automation capabilities."""
    print(f"\n5. Workflow Automation Scenario:")
    
    conv_id = await service.start_conversation(
        context={
            "workflow_id": "WF_ANALYSIS_001",
            "workflow_type": "sample_analysis",
            "samples": ["LAB001", "LAB002", "LAB003"],
            "target_completion": "2024-01-20"
        },
        required_capability="workflow_automation"
    )
    print(f"   ✓ Started workflow automation conversation: {conv_id[:8]}...")
    
    interactions = [
        "Create a new analysis workflow for samples LAB001, LAB002, and LAB003",
        "Optimize the workflow for maximum throughput",
        "Schedule all required resources for the workflow",
        "Set up automated notifications for workflow milestones"
    ]
    
    for message in interactions:
        print(f"   User: {message}")
        response = await service.send_message(
            conversation_id=conv_id,
            message=message,
            user_id="workflow_manager_001"
        )
        
        response_text = response.get("response", "No response")[:80]
        if len(response.get("response", "")) > 80:
            response_text += "..."
        print(f"   Agent: {response_text}")
        await asyncio.sleep(0.2)


async def demo_compliance_verification_scenario(service):
    """Demo compliance verification capabilities."""
    print(f"\n6. Compliance Verification Scenario:")
    
    conv_id = await service.start_conversation(
        context={
            "audit_id": "AUDIT_Q1_2024",
            "audit_type": "regulatory_compliance",
            "scope": "laboratory_operations",
            "regulations": ["ISO_17025", "FDA_21CFR", "GLP"]
        },
        required_capability="regulatory_compliance"
    )
    print(f"   ✓ Started compliance verification conversation: {conv_id[:8]}...")
    
    interactions = [
        "Verify compliance with ISO 17025 for all active processes",
        "Generate audit trail for the last 30 days",
        "Check documentation completeness for FDA 21 CFR Part 11",
        "Prepare compliance summary report"
    ]
    
    for message in interactions:
        print(f"   User: {message}")
        response = await service.send_message(
            conversation_id=conv_id,
            message=message,
            user_id="qa_auditor_001"
        )
        
        response_text = response.get("response", "No response")[:80]
        if len(response.get("response", "")) > 80:
            response_text += "..."
        print(f"   Agent: {response_text}")
        await asyncio.sleep(0.2)


async def demo_knowledge_base_queries(service):
    """Demo Prolog knowledge base queries."""
    print(f"\n7. Knowledge Base Queries (Prolog Reasoning):")
    
    # Test various knowledge base queries
    queries = [
        ("test_available", ["HPLC"]),
        ("test_available", ["GC_MS"]),
        ("critical_test", ["HPLC"]),
        ("sample_ready_for_testing", ["LAB001", "HPLC"]),
        ("quality_control_required", ["LAB001", "HPLC"])
    ]
    
    for predicate, args in queries:
        print(f"   Query: {predicate}({', '.join(args)})")
        
        start_time = time.time()
        results = await service.query_knowledge_base(predicate, args)
        query_time = time.time() - start_time
        
        if results:
            print(f"   Results: {len(results)} matches found (in {query_time:.3f}s)")
            for result in results[:2]:  # Show first 2 results
                print(f"     - {result}")
        else:
            print(f"   Results: No matches found (in {query_time:.3f}s)")
        
        await asyncio.sleep(0.1)


async def demo_concurrent_conversations(service):
    """Demo handling concurrent conversations."""
    print(f"\n7.5. Concurrent Conversations Test:")
    
    # Start multiple conversations concurrently
    conversation_tasks = []
    for i in range(3):
        task = service.start_conversation(
            context={
                "session_id": f"concurrent_test_{i}",
                "test_type": "load_test"
            },
            required_capability="sample_analysis"
        )
        conversation_tasks.append(task)
    
    conversation_ids = await asyncio.gather(*conversation_tasks)
    print(f"   ✓ Started {len(conversation_ids)} concurrent conversations")
    
    # Send messages to all conversations simultaneously
    message_tasks = []
    for i, conv_id in enumerate(conversation_ids):
        task = service.send_message(
            conversation_id=conv_id,
            message=f"Process sample set {i+1} with standard analysis protocol",
            user_id=f"user_{i+1}"
        )
        message_tasks.append(task)
    
    responses = await asyncio.gather(*message_tasks, return_exceptions=True)
    
    successful_responses = sum(1 for r in responses if not isinstance(r, Exception))
    print(f"   ✓ Processed {successful_responses}/{len(responses)} concurrent messages")


async def run_performance_test():
    """Run a performance test of the enhanced system."""
    print("\n" + "="*60)
    print("PERFORMANCE TEST")
    print("="*60)
    
    service = EnhancedLIMSMainInterfaceService({
        'max_conversations': 100,
        'max_agents': 20,
        'max_queries': 500,
        'query_timeout': 5.0,
        'agent_timeout': 10.0,
        'enable_audit': True,
        'enable_monitoring': True
    })
    
    try:
        print("\nInitializing system for performance test...")
        await service.initialize()
        
        # Performance metrics
        start_time = time.time()
        total_conversations = 10
        total_messages = 50
        
        print(f"Starting performance test:")
        print(f"- {total_conversations} conversations")
        print(f"- {total_messages} messages")
        
        # Create conversations
        conversation_ids = []
        for i in range(total_conversations):
            conv_id = await service.start_conversation(
                context={"perf_test": f"test_{i}"},
                required_capability="sample_analysis"
            )
            conversation_ids.append(conv_id)
        
        conversation_time = time.time() - start_time
        print(f"✓ Created {total_conversations} conversations in {conversation_time:.2f}s")
        
        # Send messages
        message_start = time.time()
        message_tasks = []
        
        for i in range(total_messages):
            conv_id = conversation_ids[i % len(conversation_ids)]
            task = service.send_message(
                conversation_id=conv_id,
                message=f"Performance test message {i}",
                user_id=f"perf_user_{i}"
            )
            message_tasks.append(task)
        
        responses = await asyncio.gather(*message_tasks, return_exceptions=True)
        message_time = time.time() - message_start
        
        successful_messages = sum(1 for r in responses if not isinstance(r, Exception))
        total_time = time.time() - start_time
        
        print(f"✓ Processed {successful_messages}/{total_messages} messages in {message_time:.2f}s")
        print(f"✓ Total test time: {total_time:.2f}s")
        print(f"✓ Messages per second: {successful_messages/message_time:.1f}")
        print(f"✓ Conversations per second: {total_conversations/conversation_time:.1f}")
        
        # Final status
        final_status = await service.get_system_status()
        print(f"✓ Final active conversations: {final_status.get('active_conversations', 0)}")
        
    except Exception as e:
        print(f"❌ Performance test failed: {e}")
        
    finally:
        await service.shutdown()


if __name__ == "__main__":
    print("Enhanced Main Interface Agent System Demo")
    print("Choose demo type:")
    print("1. Basic functionality demo")
    print("2. Performance test")
    
    choice = input("Enter choice (1 or 2): ").strip()
    
    if choice == "2":
        asyncio.run(run_performance_test())
    else:
        asyncio.run(demo_basic_functionality())
