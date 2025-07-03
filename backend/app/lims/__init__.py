"""
ALIMS - Agentic Laboratory Information Management System

Core LIMS module implementing TLA+ verified workflows with PydanticAI agents
and LangGraph orchestration for intelligent laboratory sample processing.

This module provides:
- Formally verified workflow specifications (TLA+)
- Intelligent AI agents for each workflow stage (PydanticAI)  
- Workflow orchestration and state management (LangGraph)
- Complete audit trail and compliance tracking
- Local AI processing with Ollama + Gemma

Key Components:
- models: Pydantic data models matching TLA+ specification
- agents: PydanticAI agents for intelligent workflow processing
- workflows: LangGraph workflows for orchestration
"""

from .models import (
    SampleState,
    Sample,
    SampleWorkflow, 
    LIMSSystemState,
    AuditLogEntry
)

from .agents.sample_reception import (
    receive_sample,
    SampleReceptionRequest,
    SampleReceptionResponse
)

from .agents.sample_accessioning import (
    accession_sample,
    SampleAccessionRequest, 
    SampleAccessionResponse
)

from .workflows.core_workflow import (
    CoreLIMSWorkflow,
    WorkflowState
)

__version__ = "1.0.0"
__author__ = "ALIMS Development Team"

__all__ = [
    # Core models
    "SampleState",
    "Sample", 
    "SampleWorkflow",
    "LIMSSystemState",
    "AuditLogEntry",
    
    # Reception agent
    "receive_sample",
    "SampleReceptionRequest",
    "SampleReceptionResponse",
    
    # Accessioning agent  
    "accession_sample",
    "SampleAccessionRequest",
    "SampleAccessionResponse",
    
    # Workflow orchestration
    "CoreLIMSWorkflow",
    "WorkflowState"
]
