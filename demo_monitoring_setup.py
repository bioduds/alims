#!/usr/bin/env python3
"""
Quick demo to show monitoring setup and usage
"""

import os
import sys
import time
from pathlib import Path

# Add backend to path
sys.path.append(str(Path(__file__).parent / "backend"))

def check_langfuse():
    """Check if Langfuse is configured"""
    pub_key = os.getenv("LANGFUSE_PUBLIC_KEY")
    sec_key = os.getenv("LANGFUSE_SECRET_KEY")
    host = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
    
    print("🔍 Checking Langfuse configuration...")
    print(f"   Public Key: {'✅ Set' if pub_key else '❌ Missing'}")
    print(f"   Secret Key: {'✅ Set' if sec_key else '❌ Missing'}")
    print(f"   Host: {host}")
    
    if pub_key and sec_key:
        try:
            from langfuse import Langfuse
            client = Langfuse(
                public_key=pub_key,
                secret_key=sec_key,
                host=host
            )
            
            # Try to create a simple trace
            trace = client.trace(name="test_connection")
            trace.span(name="test_span")
            client.flush()
            
            print("   Status: ✅ Connected successfully!")
            return True
        except Exception as e:
            print(f"   Status: ❌ Connection failed: {e}")
            return False
    else:
        print("   Status: ⚠️  Not configured")
        return False

def check_opentelemetry():
    """Check if OpenTelemetry is available"""
    print("\n📊 Checking OpenTelemetry...")
    try:
        from opentelemetry import trace
        from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
        
        print("   OpenTelemetry: ✅ Available")
        print("   OTLP Exporter: ✅ Available")
        
        # Check if Jaeger is running
        import requests
        try:
            response = requests.get("http://localhost:16686", timeout=2)
            print("   Jaeger UI: ✅ Running on http://localhost:16686")
            return True
        except:
            print("   Jaeger UI: ❌ Not running")
            print("   Start with: docker run -d -p 16686:16686 -p 14317:4317 jaegertracing/all-in-one")
            return True  # OpenTelemetry still works without UI
            
    except ImportError as e:
        print(f"   Status: ❌ Not available: {e}")
        return False

def demo_monitoring():
    """Demonstrate monitoring in action"""
    print("\n🚀 Running monitoring demo...")
    
    # Try Langfuse first
    langfuse_works = check_langfuse()
    if langfuse_works:
        print("\n   Using Langfuse monitoring...")
        try:
            from app.lims.monitoring.langfuse_integration import LangfuseLIMSMonitor
            
            monitor = LangfuseLIMSMonitor()
            if monitor.enabled:
                # Demo workflow
                workflow_id = monitor.start_workflow("URGENT", "demo_user")
                print(f"   Started workflow: {workflow_id}")
                
                time.sleep(0.5)  # Simulate work
                
                monitor.track_state_transition(
                    workflow_id, 
                    "RECEIVED", 
                    "PROCESSING",
                    {"sample_id": 12345}
                )
                print("   Tracked state transition")
                
                time.sleep(0.5)  # Simulate work
                
                monitor.complete_workflow(workflow_id, True, {"samples_processed": 1})
                print("   Completed workflow")
                
                print("   ✅ Langfuse demo completed!")
                print(f"   View traces at: {os.getenv('LANGFUSE_HOST', 'https://cloud.langfuse.com')}")
                return
        except Exception as e:
            print(f"   ❌ Langfuse demo failed: {e}")
    
    # Try OpenTelemetry
    otel_works = check_opentelemetry()
    if otel_works:
        print("\n   Using OpenTelemetry monitoring...")
        try:
            from app.lims.monitoring.opentelemetry_integration import OpenTelemetryLIMSMonitor
            
            monitor = OpenTelemetryLIMSMonitor()
            
            # Demo workflow
            with monitor.trace_workflow("URGENT", "demo_user") as workflow_span:
                workflow_span.set_attribute("demo", True)
                print("   Started workflow trace")
                
                with monitor.trace_agent_step("reception", 12345) as step_span:
                    time.sleep(0.5)  # Simulate work
                    step_span.set_attribute("step.success", True)
                    step_span.set_attribute("step.duration_ms", 500)
                    print("   Tracked agent step")
                
                workflow_span.set_attribute("workflow.success", True)
                print("   Completed workflow trace")
            
            print("   ✅ OpenTelemetry demo completed!")
            print("   View traces at: http://localhost:16686")
            return
        except Exception as e:
            print(f"   ❌ OpenTelemetry demo failed: {e}")
    
    print("\n   ⚠️  No monitoring available. Run setup first:")
    print("   ./setup_monitoring.sh")

def main():
    print("🔍 ALIMS Monitoring Demo")
    print("========================")
    
    # Check for .env file
    if os.path.exists(".env"):
        print("📁 Loading .env file...")
        with open(".env") as f:
            for line in f:
                if "=" in line and not line.startswith("#"):
                    key, value = line.strip().split("=", 1)
                    os.environ[key] = value
    else:
        print("📁 No .env file found")
    
    print(f"📍 Working directory: {os.getcwd()}")
    
    # Run checks and demo
    demo_monitoring()
    
    print("\n🛠️  Setup Help:")
    print("   1. Quick setup: ./setup_monitoring.sh")
    print("   2. Manual setup: see MONITORING_SETUP_GUIDE.md")
    print("   3. Install packages: pip install langfuse opentelemetry-api opentelemetry-sdk opentelemetry-exporter-jaeger")

if __name__ == "__main__":
    main()
