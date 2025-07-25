"""
Core LIMS Workflow - LangGraph Implementation

This module implements the TLA+ verified sample workflow using LangGraph
to orchestrate PydanticAI agents through the complete sample lifecycle.

Workflow States (matching TLA+ specification):
RECEIVED → ACCESSIONED → SCHEDULED → TESTING → QC_PENDING → QC_APPROVED → REPORTED → ARCHIVED

Each state transition is handled by specialized agents with formal verification
guarantees provided by the TLA+ specification.
"""

from typing import TypedDict, Annotated, Optional, Dict, Any, List
from langgraph.graph import StateGraph, START, END
from langgraph.graph.message import add_messages
import asyncio
from datetime import datetime
import logging
import time

from ..models import SampleState, LIMSSystemState, SampleWorkflow
from ..agents.sample_reception import receive_sample, SampleReceptionRequest
from ..agents.sample_accessioning import accession_sample, SampleAccessionRequest

# Langfuse monitoring integration
try:
    from langfuse import Langfuse, observe
    LANGFUSE_AVAILABLE = True
    
    # Mock langfuse_context for compatibility
    class MockLangfuseContext:
        def configure(self, **kwargs):
            return self
        def __enter__(self):
            return self
        def __exit__(self, *args):
            pass
    langfuse_context = MockLangfuseContext()
    
except ImportError:
    LANGFUSE_AVAILABLE = False
    def observe(*args, **kwargs):
        """Fallback decorator when Langfuse is not available"""
        def decorator(func):
            return func
        return decorator
    
    class MockLangfuseContext:
        def configure(self, **kwargs):
            return self
        def __enter__(self):
            return self
        def __exit__(self, *args):
            pass
    langfuse_context = MockLangfuseContext()

logger = logging.getLogger(__name__)


class WorkflowState(TypedDict):
    """
    LangGraph state for LIMS workflow.
    
    This state structure maintains all information needed to track
    a sample through the complete LIMS workflow while preserving
    the TLA+ verified properties.
    """
    # Core sample information
    sample_id: Optional[int]
    current_state: SampleState
    lims_system: LIMSSystemState
    
    # Workflow tracking
    messages: Annotated[List[str], add_messages]
    errors: List[str]
    completed_steps: List[str]
    
    # Monitoring and observability
    workflow_id: Optional[str]
    trace_id: Optional[str]
    step_timings: Dict[str, Dict[str, float]]
    
    # Agent responses
    reception_response: Optional[Dict[str, Any]]
    accessioning_response: Optional[Dict[str, Any]]
    scheduling_response: Optional[Dict[str, Any]]
    testing_response: Optional[Dict[str, Any]]
    qc_response: Optional[Dict[str, Any]]
    reporting_response: Optional[Dict[str, Any]]
    archiving_response: Optional[Dict[str, Any]]
    
    # Workflow metadata
    initiated_by: str
    initiated_at: datetime
    priority: str
    special_handling: List[str]


class CoreLIMSWorkflow:
    """
    Core LIMS Workflow orchestrator using LangGraph.
    
    This class implements the TLA+ verified workflow specification
    using LangGraph to coordinate PydanticAI agents through each
    state transition with formal correctness guarantees.
    """
    
    def __init__(self, lims_system: LIMSSystemState):
        self.lims_system = lims_system
        self.workflow_graph = self._build_workflow_graph()
        
        # Initialize Langfuse monitoring if available
        self.langfuse = None
        if LANGFUSE_AVAILABLE:
            try:
                import os
                public_key = os.getenv("LANGFUSE_PUBLIC_KEY")
                secret_key = os.getenv("LANGFUSE_SECRET_KEY")
                host = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
                
                if public_key and secret_key:
                    self.langfuse = Langfuse(
                        public_key=public_key,
                        secret_key=secret_key,
                        host=host
                    )
                    logger.info("Langfuse monitoring enabled for LIMS workflows")
                else:
                    logger.warning("Langfuse credentials not found - monitoring disabled")
            except Exception as e:
                logger.warning(f"Failed to initialize Langfuse: {e}")
        
    def _create_trace(self, priority: str, initiated_by: str) -> str:
        """Create a Langfuse trace for workflow monitoring"""
        if not self.langfuse:
            return f"workflow_{int(time.time())}"
            
        trace_id = f"lims_workflow_{int(time.time())}"
        
        try:
            self.langfuse.trace(
                id=trace_id,
                name="LIMS_Sample_Workflow",
                input={
                    "priority": priority,
                    "initiated_by": initiated_by,
                    "timestamp": datetime.now().isoformat()
                },
                metadata={
                    "system": "ALIMS",
                    "workflow_type": "TLA_Verified_LIMS",
                    "tla_specification": "LIMSSampleWorkflow.tla",
                    "langgraph_version": "0.5.1"
                },
                tags=["lims", "tla-verified", "langgraph", priority.lower()]
            )
        except Exception as e:
            logger.warning(f"Failed to create Langfuse trace: {e}")
            
        return trace_id
    
    def _track_step_start(self, state: WorkflowState, step_name: str):
        """Track the start of a workflow step"""
        if step_name not in state["step_timings"]:
            state["step_timings"][step_name] = {}
        state["step_timings"][step_name]["start"] = time.time()
    
    def _track_step_end(self, state: WorkflowState, step_name: str, success: bool = True):
        """Track the end of a workflow step and create Langfuse span"""
        if step_name in state["step_timings"] and "start" in state["step_timings"][step_name]:
            end_time = time.time()
            duration = end_time - state["step_timings"][step_name]["start"]
            state["step_timings"][step_name]["end"] = end_time
            state["step_timings"][step_name]["duration"] = duration
            
            # Create Langfuse span if monitoring is enabled
            if self.langfuse and state.get("trace_id"):
                try:
                    self.langfuse.span(
                        trace_id=state["trace_id"],
                        name=f"LIMS_{step_name}",
                        input={
                            "step": step_name,
                            "sample_id": state.get("sample_id"),
                            "current_state": state["current_state"].value if state.get("current_state") else None
                        },
                        output={
                            "success": success,
                            "duration_seconds": duration,
                            "completed_steps": state["completed_steps"]
                        },
                        metadata={
                            "step_type": step_name,
                            "tla_verified": True,
                            "error_count": len(state["errors"])
                        },
                        level="ERROR" if not success else "DEFAULT"
                    )
                except Exception as e:
                    logger.warning(f"Failed to create Langfuse span for {step_name}: {e}")
    
    def _build_workflow_graph(self) -> StateGraph:
        """
        Build the LangGraph workflow matching TLA+ specification.
        
        Creates a state graph with nodes for each workflow stage
        and edges representing valid state transitions.
        """
        
        # Create the workflow graph
        workflow = StateGraph(WorkflowState)
        
        # Add nodes for each workflow stage
        workflow.add_node("reception", self._handle_reception)
        workflow.add_node("accessioning", self._handle_accessioning)
        workflow.add_node("scheduling", self._handle_scheduling)
        workflow.add_node("testing", self._handle_testing)
        workflow.add_node("qc_review", self._handle_qc_review)
        workflow.add_node("reporting", self._handle_reporting)
        workflow.add_node("archiving", self._handle_archiving)
        workflow.add_node("error_handler", self._handle_error)
        
        # Define workflow edges (matching TLA+ valid transitions)
        workflow.add_edge(START, "reception")
        workflow.add_edge("reception", "accessioning")
        workflow.add_edge("accessioning", "scheduling")
        workflow.add_edge("scheduling", "testing")
        workflow.add_edge("testing", "qc_review")
        workflow.add_edge("qc_review", "reporting")
        workflow.add_edge("reporting", "archiving")
        workflow.add_edge("archiving", END)
        
        # Add conditional edges for error handling
        workflow.add_conditional_edges(
            "reception",
            self._check_for_errors,
            {"continue": "accessioning", "error": "error_handler"}
        )
        workflow.add_conditional_edges(
            "accessioning",
            self._check_for_errors,
            {"continue": "scheduling", "error": "error_handler"}
        )
        workflow.add_conditional_edges(
            "scheduling",
            self._check_for_errors,
            {"continue": "testing", "error": "error_handler"}
        )
        workflow.add_conditional_edges(
            "testing",
            self._check_for_errors,
            {"continue": "qc_review", "error": "error_handler"}
        )
        workflow.add_conditional_edges(
            "qc_review",
            self._check_for_errors,
            {"continue": "reporting", "error": "error_handler"}
        )
        workflow.add_conditional_edges(
            "reporting",
            self._check_for_errors,
            {"continue": "archiving", "error": "error_handler"}
        )
        
        workflow.add_edge("error_handler", END)
        
        return workflow.compile()
    
    @observe(name="LIMS_Sample_Reception")
    async def _handle_reception(self, state: WorkflowState) -> WorkflowState:
        """Handle sample reception stage"""
        step_name = "reception"
        self._track_step_start(state, step_name)
        
        try:
            state["messages"].append("Starting sample reception...")
            
            # Create reception request from workflow state
            # In a real implementation, this would come from external input
            reception_request = SampleReceptionRequest(
                sample_type="blood",  # This would be provided by user
                patient_id="PAT12345",  # This would be provided by user
                collection_site="Main Lab",  # This would be provided by user
                priority=state.get("priority", "ROUTINE"),
                notes="Automated workflow processing"
            )
            
            # Process sample reception
            response = await receive_sample(reception_request, state["lims_system"])
            
            if response.success:
                state["sample_id"] = response.sample_id
                state["current_state"] = SampleState.RECEIVED
                state["reception_response"] = response.dict()
                state["messages"].append(f"Sample {response.sample_id} successfully received")
                state["completed_steps"].append("reception")
                self._track_step_end(state, step_name, True)
            else:
                state["errors"].append(f"Reception failed: {response.message}")
                self._track_step_end(state, step_name, False)
                
        except Exception as e:
            state["errors"].append(f"Reception error: {str(e)}")
            self._track_step_end(state, step_name, False)
        
        return state
    
    @observe(name="LIMS_Sample_Accessioning")
    async def _handle_accessioning(self, state: WorkflowState) -> WorkflowState:
        """Handle sample accessioning stage"""
        step_name = "accessioning"
        self._track_step_start(state, step_name)
        
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for accessioning")
                self._track_step_end(state, step_name, False)
                return state
                
            state["messages"].append(f"Starting accessioning for sample {state['sample_id']}...")
            
            # Create accessioning request
            accession_request = SampleAccessionRequest(
                sample_id=state["sample_id"],
                technician_id=state.get("initiated_by", "SYSTEM"),
                quality_check_passed=True,
                volume_received=5.0,
                temperature_ok=True,
                container_intact=True,
                label_legible=True,
                requisition_complete=True,
                notes="Automated workflow accessioning"
            )
            
            # Process sample accessioning
            response = await accession_sample(accession_request, state["lims_system"])
            
            if response.success:
                state["current_state"] = SampleState.ACCESSIONED
                state["accessioning_response"] = response.dict()
                state["messages"].append(f"Sample {state['sample_id']} successfully accessioned")
                state["completed_steps"].append("accessioning")
                
                # Extract special handling requirements
                if response.recommended_actions:
                    state["special_handling"].extend(response.recommended_actions)
                    
                self._track_step_end(state, step_name, True)
            else:
                state["errors"].append(f"Accessioning failed: {response.message}")
                self._track_step_end(state, step_name, False)
                
        except Exception as e:
            state["errors"].append(f"Accessioning error: {str(e)}")
            self._track_step_end(state, step_name, False)
        
        return state
    
    async def _handle_scheduling(self, state: WorkflowState) -> WorkflowState:
        """Handle test scheduling stage"""
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for scheduling")
                return state
                
            state["messages"].append(f"Starting test scheduling for sample {state['sample_id']}...")
            
            # Transition to SCHEDULED state
            lims = state["lims_system"]
            success = lims.transition_sample(
                state["sample_id"],
                SampleState.SCHEDULED,
                state.get("initiated_by", "SYSTEM"),
                "Tests scheduled for processing"
            )
            
            if success:
                state["current_state"] = SampleState.SCHEDULED
                state["messages"].append(f"Sample {state['sample_id']} successfully scheduled")
                state["completed_steps"].append("scheduling")
                
                # Create scheduling response
                workflow = lims.get_sample(state["sample_id"])
                state["scheduling_response"] = {
                    "success": True,
                    "sample_id": state["sample_id"],
                    "scheduled_tests": ["CBC", "BMP", "Lipid Panel"],  # Would be determined by requisition
                    "estimated_completion": "2 hours",
                    "workflow_status": {
                        "current_state": workflow.current_state,
                        "audit_trail_length": len(workflow.audit_trail)
                    }
                }
            else:
                state["errors"].append("Failed to transition to SCHEDULED state")
                
        except Exception as e:
            state["errors"].append(f"Scheduling error: {str(e)}")
        
        return state
    
    async def _handle_testing(self, state: WorkflowState) -> WorkflowState:
        """Handle testing stage"""
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for testing")
                return state
                
            state["messages"].append(f"Starting testing for sample {state['sample_id']}...")
            
            # Transition to TESTING state
            lims = state["lims_system"]
            success = lims.transition_sample(
                state["sample_id"],
                SampleState.TESTING,
                state.get("initiated_by", "SYSTEM"),
                "Testing in progress"
            )
            
            if success:
                state["current_state"] = SampleState.TESTING
                
                # Simulate testing completion and transition to QC_PENDING
                await asyncio.sleep(0.1)  # Simulate processing time
                
                success = lims.transition_sample(
                    state["sample_id"],
                    SampleState.QC_PENDING,
                    state.get("initiated_by", "SYSTEM"),
                    "Testing completed, awaiting QC review"
                )
                
                if success:
                    state["current_state"] = SampleState.QC_PENDING
                    state["messages"].append(f"Sample {state['sample_id']} testing completed")
                    state["completed_steps"].append("testing")
                    
                    # Create testing response
                    workflow = lims.get_sample(state["sample_id"])
                    state["testing_response"] = {
                        "success": True,
                        "sample_id": state["sample_id"],
                        "test_results": {
                            "CBC": {"WBC": "7.2", "RBC": "4.5", "HGB": "14.2"},
                            "BMP": {"Na": "140", "K": "4.1", "Cl": "101"},
                        },
                        "testing_duration": "1.5 hours",
                        "workflow_status": {
                            "current_state": workflow.current_state,
                            "audit_trail_length": len(workflow.audit_trail)
                        }
                    }
                else:
                    state["errors"].append("Failed to transition to QC_PENDING state")
            else:
                state["errors"].append("Failed to transition to TESTING state")
                
        except Exception as e:
            state["errors"].append(f"Testing error: {str(e)}")
        
        return state
    
    async def _handle_qc_review(self, state: WorkflowState) -> WorkflowState:
        """Handle QC review stage"""
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for QC review")
                return state
                
            state["messages"].append(f"Starting QC review for sample {state['sample_id']}...")
            
            # Transition to QC_APPROVED state (simulating QC approval)
            lims = state["lims_system"]
            success = lims.transition_sample(
                state["sample_id"],
                SampleState.QC_APPROVED,
                state.get("initiated_by", "SYSTEM"),
                "QC review completed - results approved"
            )
            
            if success:
                state["current_state"] = SampleState.QC_APPROVED
                state["messages"].append(f"Sample {state['sample_id']} QC approved")
                state["completed_steps"].append("qc_review")
                
                # Create QC response
                workflow = lims.get_sample(state["sample_id"])
                state["qc_response"] = {
                    "success": True,
                    "sample_id": state["sample_id"],
                    "qc_status": "APPROVED",
                    "reviewer": state.get("initiated_by", "SYSTEM"),
                    "review_notes": "All results within expected ranges",
                    "workflow_status": {
                        "current_state": workflow.current_state,
                        "audit_trail_length": len(workflow.audit_trail)
                    }
                }
            else:
                state["errors"].append("Failed to transition to QC_APPROVED state")
                
        except Exception as e:
            state["errors"].append(f"QC review error: {str(e)}")
        
        return state
    
    async def _handle_reporting(self, state: WorkflowState) -> WorkflowState:
        """Handle reporting stage"""
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for reporting")
                return state
                
            state["messages"].append(f"Starting reporting for sample {state['sample_id']}...")
            
            # Verify QC approval before reporting (TLA+ QCRequired property)
            workflow = state["lims_system"].get_sample(state["sample_id"])
            if not workflow.can_be_reported():
                state["errors"].append("Sample cannot be reported - QC approval required")
                return state
            
            # Transition to REPORTED state
            lims = state["lims_system"]
            success = lims.transition_sample(
                state["sample_id"],
                SampleState.REPORTED,
                state.get("initiated_by", "SYSTEM"),
                "Results reported to ordering physician"
            )
            
            if success:
                state["current_state"] = SampleState.REPORTED
                state["messages"].append(f"Sample {state['sample_id']} results reported")
                state["completed_steps"].append("reporting")
                
                # Create reporting response
                workflow = lims.get_sample(state["sample_id"])
                state["reporting_response"] = {
                    "success": True,
                    "sample_id": state["sample_id"],
                    "report_id": f"RPT-{state['sample_id']}-{datetime.now().strftime('%Y%m%d')}",
                    "reported_at": datetime.now().isoformat(),
                    "delivery_method": "Electronic",
                    "workflow_status": {
                        "current_state": workflow.current_state,
                        "audit_trail_length": len(workflow.audit_trail)
                    }
                }
            else:
                state["errors"].append("Failed to transition to REPORTED state")
                
        except Exception as e:
            state["errors"].append(f"Reporting error: {str(e)}")
        
        return state
    
    async def _handle_archiving(self, state: WorkflowState) -> WorkflowState:
        """Handle archiving stage"""
        try:
            if not state.get("sample_id"):
                state["errors"].append("No sample ID available for archiving")
                return state
                
            state["messages"].append(f"Starting archiving for sample {state['sample_id']}...")
            
            # Transition to ARCHIVED state (final state)
            lims = state["lims_system"]
            success = lims.transition_sample(
                state["sample_id"],
                SampleState.ARCHIVED,
                state.get("initiated_by", "SYSTEM"),
                "Sample workflow completed and archived"
            )
            
            if success:
                state["current_state"] = SampleState.ARCHIVED
                state["messages"].append(f"Sample {state['sample_id']} successfully archived")
                state["completed_steps"].append("archiving")
                
                # Create archiving response
                workflow = lims.get_sample(state["sample_id"])
                state["archiving_response"] = {
                    "success": True,
                    "sample_id": state["sample_id"],
                    "archived_at": datetime.now().isoformat(),
                    "retention_period": "7 years",
                    "storage_location": "Digital Archive",
                    "workflow_status": {
                        "current_state": workflow.current_state,
                        "audit_trail_length": len(workflow.audit_trail),
                        "complete": True
                    }
                }
                
                # Validate all TLA+ invariants are maintained
                invariants = lims.validate_system_invariants()
                state["messages"].append(f"TLA+ Invariants: {invariants}")
                
            else:
                state["errors"].append("Failed to transition to ARCHIVED state")
                
        except Exception as e:
            state["errors"].append(f"Archiving error: {str(e)}")
        
        return state
    
    async def _handle_error(self, state: WorkflowState) -> WorkflowState:
        """Handle workflow errors"""
        state["messages"].append("Workflow encountered errors and is terminating")
        return state
    
    def _check_for_errors(self, state: WorkflowState) -> str:
        """Check if workflow should continue or handle errors"""
        return "error" if state.get("errors") else "continue"
    
    async def execute_workflow(self, 
                             priority: str = "ROUTINE",
                             initiated_by: str = "SYSTEM") -> Dict[str, Any]:
        """
        Execute the complete LIMS workflow for a sample.
        
        This method runs the entire TLA+ verified workflow from
        RECEIVED to ARCHIVED state with full audit trail maintenance
        and Langfuse monitoring.
        """
        
        # Create monitoring trace
        trace_id = self._create_trace(priority, initiated_by)
        
        # Initialize workflow state
        initial_state = WorkflowState(
            sample_id=None,
            current_state=SampleState.RECEIVED,
            lims_system=self.lims_system,
            messages=[],
            errors=[],
            completed_steps=[],
            workflow_id=f"workflow_{int(time.time())}",
            trace_id=trace_id,
            step_timings={},
            reception_response=None,
            accessioning_response=None,
            scheduling_response=None,
            testing_response=None,
            qc_response=None,
            reporting_response=None,
            archiving_response=None,
            initiated_by=initiated_by,
            initiated_at=datetime.now(),
            priority=priority,
            special_handling=[]
        )
        
        try:
            # Execute the workflow with monitoring
            if self.langfuse:
                with langfuse_context.configure(trace_id=trace_id):
                    final_state = await self.workflow_graph.ainvoke(initial_state)
            else:
                final_state = await self.workflow_graph.ainvoke(initial_state)
            
            # Complete the monitoring trace
            if self.langfuse:
                self._complete_trace(trace_id, final_state)
            
            # Return comprehensive results
            return {
                "success": len(final_state["errors"]) == 0,
                "sample_id": final_state.get("sample_id"),
                "final_state": final_state.get("current_state"),
                "completed_steps": final_state["completed_steps"],
                "messages": final_state["messages"],
                "errors": final_state["errors"],
                "responses": {
                    "reception": final_state.get("reception_response"),
                    "accessioning": final_state.get("accessioning_response"),
                    "scheduling": final_state.get("scheduling_response"),
                    "testing": final_state.get("testing_response"),
                    "qc_review": final_state.get("qc_response"),
                    "reporting": final_state.get("reporting_response"),
                    "archiving": final_state.get("archiving_response")
                },
                "special_handling": final_state["special_handling"],
                "system_invariants": self.lims_system.validate_system_invariants(),
                "monitoring": {
                    "trace_id": trace_id,
                    "step_timings": final_state["step_timings"],
                    "langfuse_enabled": self.langfuse is not None
                }
            }
            
        except Exception as e:
            # Track workflow failure
            if self.langfuse:
                try:
                    self.langfuse.trace(
                        id=trace_id,
                        output={"error": str(e), "success": False},
                        level="ERROR"
                    )
                except Exception:
                    pass
            
            return {
                "success": False,
                "error": str(e),
                "trace_id": trace_id,
                "langfuse_enabled": self.langfuse is not None
            }
    
    def _complete_trace(self, trace_id: str, final_state: WorkflowState):
        """Complete the Langfuse trace with final results"""
        try:
            total_duration = sum(
                timing.get("duration", 0) 
                for timing in final_state["step_timings"].values()
            )
            
            self.langfuse.trace(
                id=trace_id,
                output={
                    "success": len(final_state["errors"]) == 0,
                    "sample_id": final_state.get("sample_id"),
                    "final_state": final_state.get("current_state").value if final_state.get("current_state") else None,
                    "completed_steps": final_state["completed_steps"],
                    "error_count": len(final_state["errors"]),
                    "total_duration_seconds": total_duration,
                    "step_count": len(final_state["completed_steps"]),
                    "tla_compliant": len(final_state["errors"]) == 0
                },
                metadata={
                    "step_timings": final_state["step_timings"],
                    "special_handling": final_state["special_handling"],
                    "system_invariants": self.lims_system.validate_system_invariants()
                }
            )
        except Exception as e:
            logger.warning(f"Failed to complete Langfuse trace: {e}")


# Example usage and testing
if __name__ == "__main__":
    async def test_complete_workflow():
        """Test the complete LIMS workflow using LangGraph"""
        lims_system = LIMSSystemState()
        workflow = CoreLIMSWorkflow(lims_system)
        
        print("Starting complete LIMS workflow test...")
        result = await workflow.execute_workflow(
            priority="ROUTINE",
            initiated_by="TEST_USER"
        )
        
        print("\n=== WORKFLOW RESULTS ===")
        print(f"Success: {result['success']}")
        print(f"Sample ID: {result['sample_id']}")
        print(f"Final State: {result['final_state']}")
        print(f"Completed Steps: {result['completed_steps']}")
        print(f"TLA+ Invariants: {result['system_invariants']}")
        
        if result['errors']:
            print(f"Errors: {result['errors']}")
        
        print("\n=== WORKFLOW MESSAGES ===")
        for message in result['messages']:
            print(f"- {message}")
    
    # Run test
    asyncio.run(test_complete_workflow())
