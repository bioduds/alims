"""
Langfuse Integration for ALIMS LangGraph Workflows

This module provides comprehensive monitoring and observability for the TLA+ verified
LIMS workflows using Langfuse. It tracks:
- Complete workflow execution traces
- Individual agent performance
- State transitions and timing
- Error rates and recovery patterns
- Compliance audit trails
"""

import os
import uuid
import asyncio
from typing import Dict, Any, Optional, List, Callable
from datetime import datetime
from dataclasses import dataclass, asdict
from langfuse import Langfuse
import json
import logging

from ..models import SampleState, LIMSSystemState

logger = logging.getLogger(__name__)

@dataclass
class WorkflowMetrics:
    """Metrics collected during workflow execution"""
    workflow_id: str
    sample_id: Optional[int]
    start_time: datetime
    end_time: Optional[datetime] = None
    total_duration_ms: Optional[int] = None
    state_transitions: List[Dict[str, Any]] = None
    agent_performance: Dict[str, Dict[str, Any]] = None
    error_count: int = 0
    tla_violations: List[str] = None
    compliance_events: List[Dict[str, Any]] = None
    
    def __post_init__(self):
        if self.state_transitions is None:
            self.state_transitions = []
        if self.agent_performance is None:
            self.agent_performance = {}
        if self.tla_violations is None:
            self.tla_violations = []
        if self.compliance_events is None:
            self.compliance_events = []


class LangfuseLIMSMonitor:
    """
    Langfuse monitoring integration for ALIMS LangGraph workflows.
    
    Provides comprehensive observability with TLA+ compliance tracking.
    """
    
    def __init__(self, 
                 public_key: Optional[str] = None,
                 secret_key: Optional[str] = None,
                 host: Optional[str] = None):
        """Initialize Langfuse monitoring"""
        
        # Get credentials from environment or parameters
        self.public_key = public_key or os.getenv("LANGFUSE_PUBLIC_KEY")
        self.secret_key = secret_key or os.getenv("LANGFUSE_SECRET_KEY")
        self.host = host or os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
        
        if not self.public_key or not self.secret_key:
            logger.warning("Langfuse credentials not found. Monitoring will be disabled.")
            self.enabled = False
            self.langfuse = None
        else:
            self.enabled = True
            self.langfuse = Langfuse(
                public_key=self.public_key,
                secret_key=self.secret_key,
                host=self.host
            )
        
        # Active workflow tracking
        self.active_workflows: Dict[str, WorkflowMetrics] = {}
        
    def create_workflow_trace(self, 
                            sample_id: Optional[int] = None,
                            priority: str = "ROUTINE",
                            initiated_by: str = "SYSTEM",
                            metadata: Optional[Dict[str, Any]] = None) -> str:
        """Create a new workflow trace in Langfuse"""
        
        if not self.enabled:
            return str(uuid.uuid4())
            
        workflow_id = str(uuid.uuid4())
        
        # Create Langfuse trace
        trace = self.langfuse.trace(
            id=workflow_id,
            name="LIMS_Sample_Workflow",
            input={
                "sample_id": sample_id,
                "priority": priority,
                "initiated_by": initiated_by,
                "metadata": metadata or {}
            },
            metadata={
                "system": "ALIMS",
                "workflow_type": "TLA_Verified_LIMS",
                "tla_specification": "LIMSSampleWorkflow.tla",
                "version": "1.0.0"
            },
            tags=["lims", "tla-verified", "langgraph", priority.lower()]
        )
        
        # Initialize workflow metrics
        self.active_workflows[workflow_id] = WorkflowMetrics(
            workflow_id=workflow_id,
            sample_id=sample_id,
            start_time=datetime.now()
        )
        
        logger.info(f"Created workflow trace {workflow_id} for sample {sample_id}")
        return workflow_id
    
    def track_state_transition(self,
                             workflow_id: str,
                             from_state: SampleState,
                             to_state: SampleState,
                             agent_name: str,
                             duration_ms: int,
                             success: bool = True,
                             metadata: Optional[Dict[str, Any]] = None):
        """Track a state transition in the workflow"""
        
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        metrics = self.active_workflows[workflow_id]
        
        # Record state transition
        transition = {
            "timestamp": datetime.now().isoformat(),
            "from_state": from_state.value if from_state else None,
            "to_state": to_state.value,
            "agent": agent_name,
            "duration_ms": duration_ms,
            "success": success,
            "metadata": metadata or {}
        }
        
        metrics.state_transitions.append(transition)
        
        # Update agent performance
        if agent_name not in metrics.agent_performance:
            metrics.agent_performance[agent_name] = {
                "total_calls": 0,
                "total_duration_ms": 0,
                "success_count": 0,
                "error_count": 0
            }
        
        perf = metrics.agent_performance[agent_name]
        perf["total_calls"] += 1
        perf["total_duration_ms"] += duration_ms
        if success:
            perf["success_count"] += 1
        else:
            perf["error_count"] += 1
            metrics.error_count += 1
        
        # Create Langfuse span for this transition
        self._create_transition_span(workflow_id, transition)
        
        logger.debug(f"Tracked transition {from_state} -> {to_state} for workflow {workflow_id}")
    
    def track_agent_execution(self,
                            workflow_id: str,
                            agent_name: str,
                            input_data: Dict[str, Any],
                            output_data: Dict[str, Any],
                            duration_ms: int,
                            success: bool = True,
                            error_message: Optional[str] = None):
        """Track individual agent execution"""
        
        if not self.enabled:
            return
        
        # Create agent span
        span_data = {
            "name": f"Agent_{agent_name}",
            "input": input_data,
            "output": output_data,
            "metadata": {
                "agent_type": agent_name,
                "duration_ms": duration_ms,
                "success": success,
                "error_message": error_message
            }
        }
        
        if not success:
            span_data["level"] = "ERROR"
            span_data["status_message"] = error_message
        
        # Update Langfuse trace
        self.langfuse.span(**span_data, trace_id=workflow_id)
        
        logger.debug(f"Tracked agent {agent_name} execution for workflow {workflow_id}")
    
    def track_tla_validation(self,
                           workflow_id: str,
                           validation_type: str,
                           passed: bool,
                           details: Optional[Dict[str, Any]] = None):
        """Track TLA+ property validation results"""
        
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        metrics = self.active_workflows[workflow_id]
        
        if not passed:
            violation = {
                "timestamp": datetime.now().isoformat(),
                "validation_type": validation_type,
                "details": details or {}
            }
            metrics.tla_violations.append(violation)
        
        # Create validation span
        self.langfuse.span(
            trace_id=workflow_id,
            name=f"TLA_Validation_{validation_type}",
            input={"validation_type": validation_type},
            output={"passed": passed, "details": details},
            metadata={
                "tla_property": validation_type,
                "verification_result": "PASS" if passed else "FAIL"
            },
            level="WARNING" if not passed else "DEFAULT"
        )
        
        logger.debug(f"Tracked TLA+ validation {validation_type} for workflow {workflow_id}: {'PASS' if passed else 'FAIL'}")
    
    def track_compliance_event(self,
                             workflow_id: str,
                             event_type: str,
                             description: str,
                             regulation: str = "21 CFR Part 11",
                             metadata: Optional[Dict[str, Any]] = None):
        """Track regulatory compliance events"""
        
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        metrics = self.active_workflows[workflow_id]
        
        compliance_event = {
            "timestamp": datetime.now().isoformat(),
            "event_type": event_type,
            "description": description,
            "regulation": regulation,
            "metadata": metadata or {}
        }
        
        metrics.compliance_events.append(compliance_event)
        
        # Create compliance span
        self.langfuse.span(
            trace_id=workflow_id,
            name=f"Compliance_{event_type}",
            input={"event_type": event_type, "regulation": regulation},
            output={"description": description, "metadata": metadata},
            metadata={
                "compliance_type": event_type,
                "regulation": regulation,
                "audit_required": True
            },
            tags=["compliance", "audit", regulation.lower().replace(" ", "-")]
        )
        
        logger.info(f"Tracked compliance event {event_type} for workflow {workflow_id}")
    
    def complete_workflow(self,
                        workflow_id: str,
                        final_state: SampleState,
                        success: bool = True,
                        error_message: Optional[str] = None,
                        lims_system: Optional[LIMSSystemState] = None):
        """Complete a workflow trace"""
        
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        metrics = self.active_workflows[workflow_id]
        metrics.end_time = datetime.now()
        metrics.total_duration_ms = int((metrics.end_time - metrics.start_time).total_seconds() * 1000)
        
        # Gather system invariants if LIMS system provided
        system_invariants = {}
        if lims_system:
            system_invariants = lims_system.validate_system_invariants()
        
        # Update Langfuse trace
        trace_output = {
            "final_state": final_state.value,
            "success": success,
            "total_duration_ms": metrics.total_duration_ms,
            "state_transitions": len(metrics.state_transitions),
            "agent_calls": sum(perf["total_calls"] for perf in metrics.agent_performance.values()),
            "error_count": metrics.error_count,
            "tla_violations": len(metrics.tla_violations),
            "compliance_events": len(metrics.compliance_events),
            "system_invariants": system_invariants
        }
        
        if not success:
            trace_output["error_message"] = error_message
        
        # Complete the trace
        trace = self.langfuse.trace(
            id=workflow_id,
            output=trace_output,
            metadata={
                "workflow_metrics": asdict(metrics)
            }
        )
        
        # Generate session for analytics
        self._create_workflow_session(metrics)
        
        # Clean up
        del self.active_workflows[workflow_id]
        
        logger.info(f"Completed workflow trace {workflow_id}: {final_state.value} ({'SUCCESS' if success else 'FAILED'})")
    
    def _create_transition_span(self, workflow_id: str, transition: Dict[str, Any]):
        """Create a span for a state transition"""
        
        self.langfuse.span(
            trace_id=workflow_id,
            name=f"Transition_{transition['from_state']}_to_{transition['to_state']}",
            input={
                "from_state": transition['from_state'],
                "agent": transition['agent']
            },
            output={
                "to_state": transition['to_state'],
                "success": transition['success'],
                "duration_ms": transition['duration_ms']
            },
            metadata={
                "transition_type": "state_change",
                "tla_verified": True,
                **transition.get('metadata', {})
            },
            start_time=datetime.fromisoformat(transition['timestamp']),
            end_time=datetime.fromisoformat(transition['timestamp'])
        )
    
    def _create_workflow_session(self, metrics: WorkflowMetrics):
        """Create a Langfuse session for workflow analytics"""
        
        session_id = f"lims_session_{metrics.sample_id}_{metrics.start_time.strftime('%Y%m%d_%H%M%S')}"
        
        self.langfuse.session(
            id=session_id,
            metadata={
                "session_type": "lims_workflow",
                "sample_id": metrics.sample_id,
                "total_duration_ms": metrics.total_duration_ms,
                "state_transitions": len(metrics.state_transitions),
                "agent_performance": metrics.agent_performance,
                "error_count": metrics.error_count,
                "tla_violations": metrics.tla_violations,
                "compliance_events": metrics.compliance_events
            }
        )
    
    @observe()
    async def monitor_workflow_execution(self,
                                       workflow_func: Callable,
                                       *args,
                                       **kwargs) -> Any:
        """Decorator-style monitoring for workflow execution"""
        
        # Extract monitoring parameters
        sample_id = kwargs.get('sample_id')
        priority = kwargs.get('priority', 'ROUTINE')
        initiated_by = kwargs.get('initiated_by', 'SYSTEM')
        
        # Create workflow trace
        workflow_id = self.create_workflow_trace(
            sample_id=sample_id,
            priority=priority,
            initiated_by=initiated_by
        )
        
        try:
            # Execute workflow
            result = await workflow_func(*args, **kwargs)
            
            # Track completion
            final_state = result.get('final_state', SampleState.ARCHIVED)
            success = result.get('success', True)
            
            self.complete_workflow(
                workflow_id=workflow_id,
                final_state=final_state,
                success=success
            )
            
            return result
            
        except Exception as e:
            # Track failure
            self.complete_workflow(
                workflow_id=workflow_id,
                final_state=SampleState.RECEIVED,  # Default to initial state
                success=False,
                error_message=str(e)
            )
            raise
    
    def get_workflow_analytics(self, 
                             days: int = 7) -> Dict[str, Any]:
        """Get workflow analytics from Langfuse"""
        
        if not self.enabled:
            return {"error": "Langfuse monitoring not enabled"}
        
        # This would typically use Langfuse API to retrieve analytics
        # For now, return placeholder data
        return {
            "period_days": days,
            "total_workflows": 0,
            "success_rate": 0.0,
            "average_duration_ms": 0,
            "error_count": 0,
            "tla_violations": 0,
            "compliance_events": 0,
            "agent_performance": {},
            "state_transition_patterns": {}
        }
    
    def flush(self):
        """Flush any pending data to Langfuse"""
        if self.enabled and self.langfuse:
            self.langfuse.flush()


# Global monitor instance
lims_monitor = LangfuseLIMSMonitor()

# Convenience functions
def track_workflow_start(**kwargs) -> str:
    """Convenience function to start workflow tracking"""
    return lims_monitor.create_workflow_trace(**kwargs)

def track_state_transition(workflow_id: str, **kwargs):
    """Convenience function to track state transitions"""
    return lims_monitor.track_state_transition(workflow_id, **kwargs)

def track_agent_execution(workflow_id: str, **kwargs):
    """Convenience function to track agent execution"""
    return lims_monitor.track_agent_execution(workflow_id, **kwargs)

def track_tla_validation(workflow_id: str, **kwargs):
    """Convenience function to track TLA+ validation"""
    return lims_monitor.track_tla_validation(workflow_id, **kwargs)

def track_compliance_event(workflow_id: str, **kwargs):
    """Convenience function to track compliance events"""
    return lims_monitor.track_compliance_event(workflow_id, **kwargs)

def complete_workflow(workflow_id: str, **kwargs):
    """Convenience function to complete workflow tracking"""
    return lims_monitor.complete_workflow(workflow_id, **kwargs)
