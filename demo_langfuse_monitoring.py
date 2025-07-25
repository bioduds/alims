#!/usr/bin/env python3
"""
Demo: Langfuse Monitoring Integration for ALIMS LangGraph Workflows

This script demonstrates how to use Langfuse to monitor the TLA+ verified
LIMS workflows, providing comprehensive observability and analytics.

To run this demo:
1. Set up Langfuse (cloud or self-hosted)
2. Set environment variables:
   export LANGFUSE_PUBLIC_KEY="pk-lf-..."
   export LANGFUSE_SECRET_KEY="sk-lf-..."
   export LANGFUSE_HOST="https://cloud.langfuse.com"  # or your self-hosted URL
3. Run: python demo_langfuse_monitoring.py
"""

import asyncio
import os
import sys
import time
from datetime import datetime

# Add the backend path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'backend'))

from backend.app.lims.models import LIMSSystemState
from backend.app.lims.workflows.core_workflow import CoreLIMSWorkflow

def print_setup_instructions():
    """Print setup instructions for Langfuse"""
    print("🔧 LANGFUSE SETUP INSTRUCTIONS")
    print("=" * 50)
    print("1. Create a Langfuse account:")
    print("   • Cloud: https://cloud.langfuse.com")
    print("   • Self-hosted: https://langfuse.com/docs/deployment")
    print()
    print("2. Get your API keys from the Langfuse dashboard")
    print()
    print("3. Set environment variables:")
    print("   export LANGFUSE_PUBLIC_KEY='pk-lf-...'")
    print("   export LANGFUSE_SECRET_KEY='sk-lf-...'")
    print("   export LANGFUSE_HOST='https://cloud.langfuse.com'")
    print()
    print("4. Install Langfuse:")
    print("   pip install langfuse>=2.55.0")
    print()
    print("5. Run this demo again!")
    print("=" * 50)

def check_langfuse_config():
    """Check if Langfuse is properly configured"""
    public_key = os.getenv("LANGFUSE_PUBLIC_KEY")
    secret_key = os.getenv("LANGFUSE_SECRET_KEY")
    host = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
    
    if not public_key or not secret_key:
        return False, "Missing API keys"
    
    try:
        from langfuse import Langfuse
        langfuse = Langfuse(
            public_key=public_key,
            secret_key=secret_key,
            host=host
        )
        # Test connection
        langfuse.trace(
            name="test_connection",
            input={"test": "connection"}
        )
        langfuse.flush()
        return True, "Connected successfully"
    except ImportError:
        return False, "Langfuse not installed (pip install langfuse>=2.55.0)"
    except Exception as e:
        return False, f"Connection failed: {e}"

async def demo_monitored_workflow():
    """Demo monitored LIMS workflow execution"""
    print("\n🔬 ALIMS LANGFUSE MONITORING DEMO")
    print("=" * 50)
    
    # Check Langfuse configuration
    print("Checking Langfuse configuration...")
    is_configured, status = check_langfuse_config()
    
    if not is_configured:
        print(f"❌ Langfuse not configured: {status}")
        print("\n" + "=" * 50)
        print_setup_instructions()
        return
    
    print(f"✅ Langfuse configured: {status}")
    print(f"🌐 Host: {os.getenv('LANGFUSE_HOST', 'https://cloud.langfuse.com')}")
    
    # Initialize LIMS system
    print("\n📊 Initializing LIMS system...")
    lims_system = LIMSSystemState()
    workflow = CoreLIMSWorkflow(lims_system)
    
    print(f"✅ LIMS system initialized")
    print(f"📈 Langfuse monitoring: {'ENABLED' if workflow.langfuse else 'DISABLED'}")
    
    # Run multiple workflows for demonstration
    scenarios = [
        {"priority": "ROUTINE", "initiated_by": "LAB_TECH_001"},
        {"priority": "URGENT", "initiated_by": "LAB_TECH_002"},
        {"priority": "STAT", "initiated_by": "EMERGENCY_DEPT"},
        {"priority": "ROUTINE", "initiated_by": "LAB_TECH_003"}
    ]
    
    results = []
    
    for i, scenario in enumerate(scenarios, 1):
        print(f"\n🧪 WORKFLOW {i}: {scenario['priority']} Sample")
        print("-" * 30)
        
        start_time = time.time()
        
        try:
            result = await workflow.execute_workflow(
                priority=scenario["priority"],
                initiated_by=scenario["initiated_by"]
            )
            
            duration = time.time() - start_time
            results.append({**result, "scenario": scenario, "duration": duration})
            
            # Print workflow results
            print(f"📋 Result: {'✅ SUCCESS' if result['success'] else '❌ FAILED'}")
            print(f"🆔 Sample ID: {result.get('sample_id', 'N/A')}")
            print(f"🏁 Final State: {result.get('final_state', 'N/A')}")
            print(f"⏱️  Duration: {duration:.2f}s")
            print(f"📊 Steps Completed: {len(result.get('completed_steps', []))}")
            print(f"🔍 Trace ID: {result.get('monitoring', {}).get('trace_id', 'N/A')}")
            
            if result.get('errors'):
                print(f"❗ Errors: {len(result['errors'])}")
                for error in result['errors'][:3]:  # Show first 3 errors
                    print(f"   • {error}")
            
            # Brief pause between workflows
            await asyncio.sleep(1)
            
        except Exception as e:
            print(f"❌ Workflow failed: {e}")
            results.append({
                "success": False, 
                "error": str(e), 
                "scenario": scenario,
                "duration": time.time() - start_time
            })
    
    # Summary analytics
    print("\n📈 WORKFLOW ANALYTICS SUMMARY")
    print("=" * 50)
    
    successful_workflows = [r for r in results if r.get('success', False)]
    failed_workflows = [r for r in results if not r.get('success', False)]
    
    print(f"📊 Total Workflows: {len(results)}")
    print(f"✅ Successful: {len(successful_workflows)} ({len(successful_workflows)/len(results)*100:.1f}%)")
    print(f"❌ Failed: {len(failed_workflows)} ({len(failed_workflows)/len(results)*100:.1f}%)")
    
    if successful_workflows:
        avg_duration = sum(r["duration"] for r in successful_workflows) / len(successful_workflows)
        print(f"⏱️  Average Duration: {avg_duration:.2f}s")
        
        # Priority breakdown
        priority_stats = {}
        for result in successful_workflows:
            priority = result["scenario"]["priority"]
            if priority not in priority_stats:
                priority_stats[priority] = {"count": 0, "total_duration": 0}
            priority_stats[priority]["count"] += 1
            priority_stats[priority]["total_duration"] += result["duration"]
        
        print("\n📋 Priority Breakdown:")
        for priority, stats in priority_stats.items():
            avg_dur = stats["total_duration"] / stats["count"]
            print(f"   {priority}: {stats['count']} workflows, avg {avg_dur:.2f}s")
    
    # Langfuse dashboard info
    print("\n🎯 LANGFUSE DASHBOARD")
    print("=" * 50)
    print(f"🌐 Dashboard URL: {os.getenv('LANGFUSE_HOST', 'https://cloud.langfuse.com')}")
    print("📊 Check your Langfuse dashboard for:")
    print("   • Complete workflow traces")
    print("   • Step-by-step execution timing")
    print("   • Agent performance metrics")
    print("   • TLA+ compliance validation")
    print("   • Error tracking and patterns")
    print("   • Regulatory audit trails")
    
    print("\n🔍 Trace Analysis:")
    print("   • Search for traces tagged 'lims'")
    print("   • Filter by priority: routine, urgent, stat")
    print("   • View state transition patterns")
    print("   • Analyze agent execution times")
    print("   • Track TLA+ property validation")
    
    print("\n🎊 Demo completed! Check your Langfuse dashboard for detailed insights.")

async def demo_langfuse_features():
    """Demo specific Langfuse features"""
    print("\n🚀 LANGFUSE FEATURES DEMONSTRATION")
    print("=" * 50)
    
    try:
        from langfuse import Langfuse
        
        public_key = os.getenv("LANGFUSE_PUBLIC_KEY")
        secret_key = os.getenv("LANGFUSE_SECRET_KEY")
        host = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
        
        if not public_key or not secret_key:
            print("❌ Langfuse credentials not configured")
            return
        
        langfuse = Langfuse(
            public_key=public_key,
            secret_key=secret_key,
            host=host
        )
        
        print("✅ Connected to Langfuse")
        
        # Create a demo trace with spans
        trace_id = f"alims_demo_{int(time.time())}"
        
        print(f"\n📊 Creating demo trace: {trace_id}")
        
        # Main trace
        trace = langfuse.trace(
            id=trace_id,
            name="ALIMS_Demo_Workflow",
            input={
                "demo_type": "langfuse_features",
                "timestamp": datetime.now().isoformat()
            },
            metadata={
                "system": "ALIMS",
                "demo": True,
                "tla_verified": True
            },
            tags=["demo", "alims", "lims", "tla-verified"]
        )
        
        # Create spans for different workflow steps
        steps = [
            {"name": "Sample_Reception", "duration": 0.5},
            {"name": "Sample_Accessioning", "duration": 0.8},
            {"name": "Test_Scheduling", "duration": 0.3},
            {"name": "Test_Execution", "duration": 2.1},
            {"name": "QC_Review", "duration": 0.7},
            {"name": "Result_Reporting", "duration": 0.4},
            {"name": "Sample_Archiving", "duration": 0.2}
        ]
        
        for i, step in enumerate(steps):
            print(f"   📋 Step {i+1}: {step['name']}")
            
            langfuse.span(
                trace_id=trace_id,
                name=step["name"],
                input={
                    "step_number": i + 1,
                    "step_name": step["name"]
                },
                output={
                    "success": True,
                    "duration_seconds": step["duration"],
                    "tla_compliant": True
                },
                metadata={
                    "step_type": "workflow_stage",
                    "tla_verified": True,
                    "agent_type": step["name"].lower().replace("_", "-")
                }
            )
            
            await asyncio.sleep(0.1)  # Brief pause for demo
        
        # Complete the trace
        langfuse.trace(
            id=trace_id,
            output={
                "success": True,
                "total_steps": len(steps),
                "total_duration": sum(s["duration"] for s in steps),
                "compliance_status": "COMPLIANT"
            }
        )
        
        # Create a session for analytics
        session_id = f"alims_demo_session_{int(time.time())}"
        langfuse.session(
            id=session_id,
            metadata={
                "session_type": "demo",
                "workflow_count": 1,
                "demo_features": [
                    "trace_creation",
                    "span_tracking",
                    "metadata_annotation",
                    "session_analytics"
                ]
            }
        )
        
        # Flush to ensure data is sent
        langfuse.flush()
        
        print(f"✅ Demo trace created successfully!")
        print(f"🔍 Trace ID: {trace_id}")
        print(f"📊 Session ID: {session_id}")
        print(f"🌐 View in dashboard: {host}")
        
    except ImportError:
        print("❌ Langfuse not installed. Run: pip install langfuse>=2.55.0")
    except Exception as e:
        print(f"❌ Error creating demo trace: {e}")

if __name__ == "__main__":
    print("🎯 ALIMS Langfuse Monitoring Demo")
    print("Comprehensive observability for TLA+ verified LIMS workflows")
    print("=" * 60)
    
    # Run the main demo
    asyncio.run(demo_monitored_workflow())
    
    # Run feature demonstration
    asyncio.run(demo_langfuse_features())
    
    print("\n🎉 Demo completed!")
    print("Next steps:")
    print("1. Explore your Langfuse dashboard")
    print("2. Set up alerts for workflow failures")
    print("3. Create custom analytics dashboards")
    print("4. Configure compliance monitoring rules")
