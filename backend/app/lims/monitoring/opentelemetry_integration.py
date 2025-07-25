"""
OpenTelemetry Integration for ALIMS LangGraph Workflows

Pure open source alternative to Langfuse using OpenTelemetry + Jaeger
"""

import os
import time
from datetime import datetime
from typing import Dict, Any, Optional
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import Resource

class OpenTelemetryLIMSMonitor:
    """Open source monitoring using OpenTelemetry + OTLP"""
    
    def __init__(self, otlp_endpoint: str = "http://localhost:4317"):
        # Configure OpenTelemetry
        resource = Resource.create({
            "service.name": "alims-lims-workflow",
            "service.version": "1.0.0",
            "deployment.environment": os.getenv("ENV", "development")
        })
        
        provider = TracerProvider(resource=resource)
        trace.set_tracer_provider(provider)
        
        # Configure OTLP exporter (works with Jaeger, Zipkin, etc.)
        otlp_exporter = OTLPSpanExporter(
            endpoint=otlp_endpoint,
            insecure=True  # For local development
        )
        
        span_processor = BatchSpanProcessor(otlp_exporter)
        provider.add_span_processor(span_processor)
        
        self.tracer = trace.get_tracer(__name__)
        
    def trace_workflow(self, priority: str, initiated_by: str):
        """Create a workflow trace"""
        return self.tracer.start_span(
            "lims_workflow",
            attributes={
                "workflow.priority": priority,
                "workflow.initiated_by": initiated_by,
                "workflow.system": "ALIMS",
                "workflow.tla_verified": True
            }
        )
    
    def trace_agent_step(self, step_name: str, sample_id: Optional[int] = None):
        """Create a span for an agent step"""
        return self.tracer.start_span(
            f"lims_{step_name}",
            attributes={
                "agent.step": step_name,
                "sample.id": sample_id,
                "agent.type": "pydantic_ai",
                "tla.verified": True
            }
        )

# Usage example:
monitor = OpenTelemetryLIMSMonitor()

# In your workflow:
with monitor.trace_workflow("URGENT", "LAB_TECH_001") as workflow_span:
    with monitor.trace_agent_step("reception", 12345) as step_span:
        # Your agent logic here
        step_span.set_attribute("step.success", True)
        step_span.set_attribute("step.duration_ms", 500)
