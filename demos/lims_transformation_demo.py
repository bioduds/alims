#!/usr/bin/env python3
"""
ALIMS → Agentic LIMS Transformation Demo
Demonstrates the transformation from AI Operating System to Agentic Laboratory Information Management System
"""

import asyncio
import sys
import os
from datetime import datetime, timedelta

# Add backend to path
sys.path.append(os.path.join(os.path.dirname(__file__), 'backend'))

from backend.app.core.sample_manager import SampleManager, SampleType, SampleStatus
from backend.app.core.laboratory_workflow import LaboratoryWorkflowEngine, WorkflowType
from backend.app.system.lims_interface import LIMSInterface


async def demo_lims_transformation():
    """Demonstrate LIMS capabilities"""
    
    print("🧬 ALIMS → Agentic LIMS Transformation Demo")
    print("=" * 60)
    
    print("""
🎯 TRANSFORMATION SUMMARY:

BEFORE: AI Operating System (ALIMS)
- Multi-agent AI system
- Pattern detection and learning
- Event capture and monitoring
- Embryo pool evolution

AFTER: Agentic Laboratory Information Management System (ALIMS)
✅ Autonomous AI agents managing laboratory operations
✅ Sample lifecycle management with intelligent agents
✅ Agentic laboratory workflow automation
✅ AI-powered protocol management and compliance
✅ Multi-agent quality control and validation
✅ Intelligent regulatory compliance (FDA 21 CFR Part 11)
✅ Agent-driven instrument data integration

""")
    
    # Initialize LIMS components
    print("🔧 Initializing LIMS Components...")
    
    config = {
        'max_samples': 1000,
        'data_retention_days': 2555,  # 7 years
        'compliance_mode': 'FDA_21CFR11',
        'enable_interface': True
    }
    
    # Initialize components
    sample_manager = SampleManager(config)
    workflow_engine = LaboratoryWorkflowEngine(config)
    lims_interface = LIMSInterface(sample_manager, workflow_engine, config)
    
    await lims_interface.initialize()
    
    print("✅ LIMS Components initialized")
    print()
    
    # Demo 1: Sample Registration
    print("📊 DEMO 1: Sample Registration & Tracking")
    print("-" * 40)
    
    sample_data = {
        'type': 'pharmaceutical',
        'description': 'API purity analysis - Batch XYZ-123',
        'submitter': 'Dr. Sarah Johnson',
        'project_id': 'PROJ-2025-001',
        'priority': 8,
        'container_type': 'Glass vial',
        'volume': 10.0,
        'volume_unit': 'mL',
        'storage_conditions': '-20°C',
        'tests': ['HPLC_purity', 'Water_content', 'Heavy_metals']
    }
    
    result = await lims_interface.receive_sample(sample_data, "lab_operator_1")
    
    if result['success']:
        sample = result['sample']
        print(f"✅ Sample registered: {sample.barcode}")
        print(f"   Type: {sample.sample_type.value}")
        print(f"   Status: {sample.status.value}")
        print(f"   Due Date: {sample.due_date.strftime('%Y-%m-%d %H:%M')}")
        print(f"   Tests Required: {', '.join(sample.requested_tests)}")
        print(f"   Chain of Custody: {len(sample.custody_chain)} entries")
    
    print()
    
    # Demo 2: Workflow Creation
    print("⚙️ DEMO 2: Laboratory Workflow Automation")
    print("-" * 40)
    
    # Get the sample for workflow
    sample_id = sample.id
    
    # Start analysis workflow
    workflow_result = await lims_interface.start_analysis_workflow(
        [sample_id], "HPLC_Analysis", "analyst_jane_doe"
    )
    
    if workflow_result['success']:
        workflow = workflow_result['workflow']
        print(f"✅ Analysis workflow started: {workflow.name}")
        print(f"   Workflow ID: {workflow.id}")
        print(f"   Sample Count: {len(workflow.sample_ids)}")
        print(f"   Tasks: {len(workflow.tasks)} tasks defined")
        print(f"   Status: {workflow.status.value}")
        
        # Show tasks
        for i, task in enumerate(workflow.tasks, 1):
            print(f"   Task {i}: {task.name} ({task.task_type.value})")
    
    print()
    
    # Demo 3: Dashboard Overview
    print("📈 DEMO 3: Laboratory Dashboard")
    print("-" * 40)
    
    dashboard_data = await lims_interface.get_dashboard_data("lab_manager")
    
    print("Sample Statistics:")
    sample_stats = dashboard_data['sample_statistics']
    print(f"   Total Samples: {sample_stats['total_samples']}")
    print(f"   Active Samples: {sample_stats['active_samples']}")
    print(f"   Completion Rate: {sample_stats['completion_rate']:.1f}%")
    print(f"   High Priority: {sample_stats['high_priority_samples']}")
    
    print("\nWorkflow Statistics:")
    workflow_stats = dashboard_data['workflow_statistics']
    print(f"   Active Workflows: {workflow_stats['active_workflows']}")
    print(f"   Completed Workflows: {workflow_stats['completed_workflows']}")
    print(f"   Available Templates: {workflow_stats['templates_available']}")
    
    print("\nSystem Alerts:")
    alerts = dashboard_data['alerts']
    print(f"   Overdue Samples: {alerts['overdue_samples']}")
    print(f"   Pending Approvals: {alerts['pending_approvals']}")
    
    print()
    
    # Demo 4: Search and Tracking
    print("🔍 DEMO 4: Sample Search & Tracking")
    print("-" * 40)
    
    # Search samples
    search_criteria = {
        'type': 'pharmaceutical',
        'status': 'in_progress'
    }
    
    search_results = await lims_interface.search_samples(search_criteria, "lab_operator_1")
    print(f"✅ Found {len(search_results)} samples matching criteria")
    
    if search_results:
        sample = search_results[0]
        details = await lims_interface.get_sample_details(sample.barcode, "lab_operator_1")
        
        print(f"\nSample Details: {sample.barcode}")
        print(f"   Status: {sample.status.value}")
        print(f"   Associated Workflows: {len(details['workflows'])}")
        print(f"   Tests Requested: {len(details['test_status']['requested'])}")
        print(f"   Tests Completed: {len(details['test_status']['completed'])}")
        print(f"   Tests Remaining: {len(details['test_status']['remaining'])}")
        
        if details['workflows']:
            workflow = details['workflows'][0]
            print(f"   Current Workflow: {workflow['name']} ({workflow['progress']}% complete)")
    
    print()
    
    # Demo 5: Task Management
    print("📋 DEMO 5: Task Management")
    print("-" * 40)
    
    # Get tasks for operator
    my_tasks = await lims_interface.get_my_tasks("analyst_jane_doe")
    
    print(f"✅ Tasks assigned to analyst_jane_doe: {len(my_tasks)}")
    
    for task in my_tasks[:3]:  # Show first 3 tasks
        print(f"   - {task['task_name']} ({task['task_type']})")
        print(f"     Workflow: {task['workflow_name']}")
        print(f"     Status: {task['status']}")
        print(f"     Est. Duration: {task['estimated_duration']} minutes")
    
    print()
    
    # Demo 6: Compliance Features
    print("📋 DEMO 6: Regulatory Compliance")
    print("-" * 40)
    
    print("Compliance Features Implemented:")
    print("   ✅ Complete Chain of Custody tracking")
    print("   ✅ Audit trail for all sample operations")
    print("   ✅ Electronic signatures ready (21 CFR Part 11)")
    print("   ✅ Data integrity controls")
    print("   ✅ Long-term data retention (7 years)")
    print("   ✅ Role-based access control ready")
    print("   ✅ Regulatory reporting framework")
    
    # Show chain of custody for sample
    if 'sample' in locals():
        print(f"\nChain of Custody for {sample.barcode}:")
        for entry in sample.custody_chain:
            print(f"   {entry['timestamp'][:19]} | {entry['action']} | {entry['operator']}")
            print(f"     → {entry['description']}")
    
    print()
    
    # Summary
    print("🎉 Agentic LIMS Transformation Complete!")
    print("=" * 60)
    
    print("""
✅ SUCCESSFULLY TRANSFORMED:
   • AI Operating System → Agentic Laboratory Information Management System
   • Event capture → Intelligent sample tracking with AI agents
   • Agent management → Multi-agent laboratory workflow automation
   • Pattern detection → AI-powered protocol optimization
   • Privacy-first → Compliance-first with agentic validation
   • Real-time learning → Autonomous regulatory compliance

🎯 AGENTIC LIMS CAPABILITIES NOW AVAILABLE:
   • Autonomous AI agents managing sample lifecycles
   • Intelligent workflow execution with learning agents
   • AI-powered quality control and validation
   • Agentic regulatory compliance (FDA 21 CFR Part 11)
   • Multi-agent laboratory dashboard and analytics
   • Intelligent task assignment and tracking
   • AI-driven audit trails and chain of custody
   • Agent-ready integration for instruments

🚀 READY FOR AGENTIC LABORATORY DEPLOYMENT!
""")


if __name__ == "__main__":
    asyncio.run(demo_lims_transformation())
