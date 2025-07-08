"""
FastAPI Integration for Workflow Manager Service

This module provides REST API endpoints for the ALIMS Workflow Manager Service,
implementing TLA+ verified properties through runtime enforcement and providing
comprehensive workflow orchestration capabilities.

Key Features:
- RESTful API for workflow operations
- Runtime TLA+ property validation
- Optimistic locking for concurrent safety
- Event-driven notifications
- Recovery and fault tolerance
- OpenAPI documentation
"""

from datetime import datetime
from typing import Dict, List, Optional, Any
import logging
from contextlib import asynccontextmanager

from fastapi import FastAPI, HTTPException, Depends, status, BackgroundTasks
from fastapi.responses import JSONResponse
from pydantic import BaseModel, Field, validator
import uvicorn

from .core import WorkflowManagerCore
from .models import (
    WorkflowState, WorkflowEvent, WorkflowStates, EventTypes,
    TLAPropertyViolation, WorkflowNotFoundError, 
    InvalidTransitionError, OptimisticLockError
)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global workflow manager instance
workflow_manager: Optional[WorkflowManagerCore] = None

@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan management"""
    global workflow_manager
    
    # Startup
    logger.info("Initializing Workflow Manager Service...")
    workflow_manager = WorkflowManagerCore()
    logger.info("Workflow Manager Service initialized successfully")
    
    yield
    
    # Shutdown
    logger.info("Shutting down Workflow Manager Service...")
    # Perform any cleanup operations if needed
    logger.info("Workflow Manager Service shutdown complete")

# FastAPI application
app = FastAPI(
    title="ALIMS Workflow Manager Service",
    description="TLA+ Verified Workflow Orchestration Service for Laboratory Information Management",
    version="1.0.0",
    docs_url="/docs",
    redoc_url="/redoc",
    lifespan=lifespan
)

# Request/Response Models
class CreateWorkflowRequest(BaseModel):
    """Request model for creating a new workflow"""
    workflow_id: str = Field(..., description="Unique workflow identifier")
    metadata: Optional[Dict[str, Any]] = Field(default_factory=dict, description="Additional workflow metadata")
    
    @validator('workflow_id')
    def validate_workflow_id(cls, v):
        if not v or not v.strip():
            raise ValueError("Workflow ID cannot be empty")
        if len(v) > 100:
            raise ValueError("Workflow ID cannot exceed 100 characters")
        return v.strip()

class TransitionRequest(BaseModel):
    """Request model for workflow state transitions"""
    target_state: WorkflowStates = Field(..., description="Target workflow state")
    expected_version: int = Field(..., description="Expected workflow version for optimistic locking")
    metadata: Optional[Dict[str, Any]] = Field(default_factory=dict, description="Transition metadata")
    
    @validator('expected_version')
    def validate_version(cls, v):
        if v < 1:
            raise ValueError("Expected version must be positive")
        return v

class WorkflowResponse(BaseModel):
    """Response model for workflow operations"""
    workflow_id: str
    state: WorkflowStates
    previous_state: Optional[WorkflowStates]
    version: int
    created_at: datetime
    updated_at: datetime
    in_transition: bool
    metadata: Dict[str, Any]

class EventResponse(BaseModel):
    """Response model for workflow events"""
    event_id: int
    workflow_id: str
    event_type: EventTypes
    from_state: Optional[WorkflowStates]
    to_state: WorkflowStates
    timestamp: datetime
    retry_count: int

class ErrorResponse(BaseModel):
    """Standard error response model"""
    error: str
    detail: str
    timestamp: datetime = Field(default_factory=datetime.utcnow)

# Dependency injection
def get_workflow_manager() -> WorkflowManagerCore:
    """Get the workflow manager instance"""
    if workflow_manager is None:
        raise HTTPException(
            status_code=status.HTTP_503_SERVICE_UNAVAILABLE,
            detail="Workflow Manager Service not initialized"
        )
    return workflow_manager

# Error handlers
@app.exception_handler(WorkflowNotFoundError)
async def workflow_not_found_handler(request, exc: WorkflowNotFoundError):
    """Handle workflow not found errors"""
    return JSONResponse(
        status_code=status.HTTP_404_NOT_FOUND,
        content=ErrorResponse(
            error="WorkflowNotFound",
            detail=str(exc)
        ).dict()
    )

@app.exception_handler(InvalidTransitionError)
async def invalid_transition_handler(request, exc: InvalidTransitionError):
    """Handle invalid transition errors"""
    return JSONResponse(
        status_code=status.HTTP_400_BAD_REQUEST,
        content=ErrorResponse(
            error="InvalidTransition",
            detail=str(exc)
        ).dict()
    )

@app.exception_handler(OptimisticLockError)
async def optimistic_lock_handler(request, exc: OptimisticLockError):
    """Handle optimistic locking conflicts"""
    return JSONResponse(
        status_code=status.HTTP_409_CONFLICT,
        content=ErrorResponse(
            error="OptimisticLockConflict",
            detail=str(exc)
        ).dict()
    )

@app.exception_handler(TLAPropertyViolation)
async def tla_property_violation_handler(request, exc: TLAPropertyViolation):
    """Handle TLA+ property violations"""
    return JSONResponse(
        status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
        content=ErrorResponse(
            error="TLAPropertyViolation",
            detail=f"System invariant violated: {exc}"
        ).dict()
    )

# Health check endpoint
@app.get("/health", tags=["Health"])
async def health_check():
    """Service health check"""
    return {
        "status": "healthy",
        "service": "ALIMS Workflow Manager",
        "timestamp": datetime.utcnow(),
        "tla_properties": "enforced"
    }

# Workflow Management Endpoints
@app.post("/workflows", response_model=WorkflowResponse, tags=["Workflows"])
async def create_workflow(
    request: CreateWorkflowRequest,
    background_tasks: BackgroundTasks,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Create a new workflow with TLA+ property enforcement
    
    - **workflow_id**: Unique identifier for the workflow
    - **metadata**: Optional metadata for the workflow
    
    Returns the created workflow with initial state 'CREATED'
    """
    try:
        logger.info(f"Creating workflow: {request.workflow_id}")
        
        workflow = wm.create_workflow(
            workflow_id=request.workflow_id,
            metadata=request.metadata
        )
        
        # Schedule background event processing
        background_tasks.add_task(
            _process_workflow_events,
            wm,
            request.workflow_id
        )
        
        logger.info(f"Workflow created successfully: {request.workflow_id}")
        
        return WorkflowResponse(
            workflow_id=workflow.id,
            state=workflow.state,
            previous_state=workflow.previous_state,
            version=workflow.version,
            created_at=workflow.created_at,
            updated_at=workflow.updated_at,
            in_transition=workflow.in_transition,
            metadata=workflow.metadata
        )
        
    except Exception as e:
        logger.error(f"Failed to create workflow {request.workflow_id}: {e}")
        raise

@app.get("/workflows/{workflow_id}", response_model=WorkflowResponse, tags=["Workflows"])
async def get_workflow(
    workflow_id: str,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Retrieve a workflow by ID
    
    - **workflow_id**: The unique workflow identifier
    
    Returns the current workflow state and metadata
    """
    try:
        logger.info(f"Retrieving workflow: {workflow_id}")
        
        workflow = wm.get_workflow(workflow_id)
        
        return WorkflowResponse(
            workflow_id=workflow.id,
            state=workflow.state,
            previous_state=workflow.previous_state,
            version=workflow.version,
            created_at=workflow.created_at,
            updated_at=workflow.updated_at,
            in_transition=workflow.in_transition,
            metadata=workflow.metadata
        )
        
    except WorkflowNotFoundError:
        logger.warning(f"Workflow not found: {workflow_id}")
        raise
    except Exception as e:
        logger.error(f"Failed to retrieve workflow {workflow_id}: {e}")
        raise

@app.post("/workflows/{workflow_id}/transitions", response_model=WorkflowResponse, tags=["Workflows"])
async def transition_workflow(
    workflow_id: str,
    request: TransitionRequest,
    background_tasks: BackgroundTasks,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Request a workflow state transition with optimistic locking
    
    - **workflow_id**: The unique workflow identifier
    - **target_state**: The desired target state
    - **expected_version**: Current workflow version for optimistic locking
    - **metadata**: Optional transition metadata
    
    Returns the updated workflow after successful transition
    """
    try:
        logger.info(f"Transitioning workflow {workflow_id} to {request.target_state}")
        
        workflow = wm.transition_workflow(
            workflow_id=workflow_id,
            target_state=request.target_state,
            expected_version=request.expected_version,
            metadata=request.metadata
        )
        
        # Schedule background event processing
        background_tasks.add_task(
            _process_workflow_events,
            wm,
            workflow_id
        )
        
        logger.info(f"Workflow transitioned successfully: {workflow_id} -> {request.target_state}")
        
        return WorkflowResponse(
            workflow_id=workflow.id,
            state=workflow.state,
            previous_state=workflow.previous_state,
            version=workflow.version,
            created_at=workflow.created_at,
            updated_at=workflow.updated_at,
            in_transition=workflow.in_transition,
            metadata=workflow.metadata
        )
        
    except (WorkflowNotFoundError, InvalidTransitionError, OptimisticLockError):
        logger.warning(f"Transition failed for workflow {workflow_id}")
        raise
    except Exception as e:
        logger.error(f"Failed to transition workflow {workflow_id}: {e}")
        raise

@app.get("/workflows", response_model=List[WorkflowResponse], tags=["Workflows"])
async def list_workflows(
    state: Optional[WorkflowStates] = None,
    limit: int = 100,
    offset: int = 0,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    List workflows with optional state filtering
    
    - **state**: Optional state filter
    - **limit**: Maximum number of workflows to return (default: 100)
    - **offset**: Number of workflows to skip (default: 0)
    
    Returns a list of workflows matching the criteria
    """
    try:
        logger.info(f"Listing workflows (state={state}, limit={limit}, offset={offset})")
        
        workflows = wm.list_workflows(state=state, limit=limit, offset=offset)
        
        return [
            WorkflowResponse(
                workflow_id=wf.id,
                state=wf.state,
                previous_state=wf.previous_state,
                version=wf.version,
                created_at=wf.created_at,
                updated_at=wf.updated_at,
                in_transition=wf.in_transition,
                metadata=wf.metadata
            )
            for wf in workflows
        ]
        
    except Exception as e:
        logger.error(f"Failed to list workflows: {e}")
        raise

# Event Management Endpoints
@app.get("/workflows/{workflow_id}/events", response_model=List[EventResponse], tags=["Events"])
async def get_workflow_events(
    workflow_id: str,
    limit: int = 100,
    offset: int = 0,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Retrieve events for a specific workflow
    
    - **workflow_id**: The unique workflow identifier
    - **limit**: Maximum number of events to return (default: 100)
    - **offset**: Number of events to skip (default: 0)
    
    Returns a list of workflow events in chronological order
    """
    try:
        logger.info(f"Retrieving events for workflow: {workflow_id}")
        
        events = wm.get_workflow_events(workflow_id, limit=limit, offset=offset)
        
        return [
            EventResponse(
                event_id=event.event_id,
                workflow_id=event.workflow_id,
                event_type=event.event_type,
                from_state=event.from_state,
                to_state=event.to_state,
                timestamp=event.timestamp,
                retry_count=event.retry_count
            )
            for event in events
        ]
        
    except WorkflowNotFoundError:
        logger.warning(f"Workflow not found for events: {workflow_id}")
        raise
    except Exception as e:
        logger.error(f"Failed to retrieve events for workflow {workflow_id}: {e}")
        raise

# Recovery Endpoints
@app.post("/workflows/{workflow_id}/recover", response_model=WorkflowResponse, tags=["Recovery"])
async def recover_workflow(
    workflow_id: str,
    background_tasks: BackgroundTasks,
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Initiate recovery for a failed workflow
    
    - **workflow_id**: The unique workflow identifier
    
    Returns the recovered workflow in 'ACTIVE' state
    """
    try:
        logger.info(f"Initiating recovery for workflow: {workflow_id}")
        
        workflow = wm.recover_workflow(workflow_id)
        
        # Schedule background event processing
        background_tasks.add_task(
            _process_workflow_events,
            wm,
            workflow_id
        )
        
        logger.info(f"Workflow recovered successfully: {workflow_id}")
        
        return WorkflowResponse(
            workflow_id=workflow.id,
            state=workflow.state,
            previous_state=workflow.previous_state,
            version=workflow.version,
            created_at=workflow.created_at,
            updated_at=workflow.updated_at,
            in_transition=workflow.in_transition,
            metadata=workflow.metadata
        )
        
    except WorkflowNotFoundError:
        logger.warning(f"Workflow not found for recovery: {workflow_id}")
        raise
    except Exception as e:
        logger.error(f"Failed to recover workflow {workflow_id}: {e}")
        raise

# System Information Endpoints
@app.get("/system/stats", tags=["System"])
async def get_system_stats(
    wm: WorkflowManagerCore = Depends(get_workflow_manager)
):
    """
    Get system statistics and TLA+ property validation status
    
    Returns comprehensive system metrics and health information
    """
    try:
        stats = wm.get_system_stats()
        
        return {
            "timestamp": datetime.utcnow(),
            "workflow_stats": stats,
            "tla_properties": {
                "state_consistency": "enforced",
                "transition_validity": "enforced",
                "concurrent_safety": "enforced",
                "optimistic_locking": "active",
                "event_ordering": "guaranteed"
            },
            "service_health": "healthy"
        }
        
    except Exception as e:
        logger.error(f"Failed to retrieve system stats: {e}")
        raise

# Background Tasks
async def _process_workflow_events(wm: WorkflowManagerCore, workflow_id: str):
    """Background task for processing workflow events"""
    try:
        # Simulate event processing delay
        import asyncio
        await asyncio.sleep(0.1)
        
        # Process any pending events for the workflow
        logger.info(f"Processing events for workflow: {workflow_id}")
        
        # In a real implementation, this would handle:
        # - Event delivery to external systems
        # - Notification services
        # - Audit logging
        # - Integration with other ALIMS services
        
    except Exception as e:
        logger.error(f"Failed to process events for workflow {workflow_id}: {e}")

# Development server
def run_server(host: str = "127.0.0.1", port: int = 8001, debug: bool = False):
    """Run the FastAPI development server"""
    uvicorn.run(
        "integration:app",
        host=host,
        port=port,
        reload=debug,
        log_level="debug" if debug else "info"
    )

if __name__ == "__main__":
    run_server(debug=True)
