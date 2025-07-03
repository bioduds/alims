"""
ALIMS Laboratory Interface
User interface and system integration for laboratory operations
"""

import asyncio
import logging
from datetime import datetime
from typing import Dict, List, Optional, Any
from dataclasses import dataclass

from .sample_manager import SampleManager, Sample, SampleStatus, SampleType
from .laboratory_workflow import LaboratoryWorkflowEngine, LaboratoryWorkflow, WorkflowStatus


@dataclass
class LIMSNotification:
    """System notification for laboratory events"""
    id: str
    timestamp: datetime
    type: str  # info, warning, error, success
    title: str
    message: str
    recipient: Optional[str] = None
    read: bool = False


class LIMSInterface:
    """
    Main interface for laboratory information management
    
    Provides high-level operations for laboratory staff to interact
    with samples, workflows, and system functionality.
    """
    
    def __init__(self, 
                 sample_manager: SampleManager,
                 workflow_engine: LaboratoryWorkflowEngine,
                 config: Dict[str, Any]):
        self.logger = logging.getLogger("LIMSInterface")
        self.sample_manager = sample_manager
        self.workflow_engine = workflow_engine
        self.config = config
        
        # Notifications
        self.notifications: List[LIMSNotification] = []
        
        # Session tracking
        self.active_sessions: Dict[str, Dict[str, Any]] = {}
        
        self.logger.info("LIMS Interface initialized")
    
    # Sample Operations
    async def receive_sample(self, 
                           sample_data: Dict[str, Any],
                           operator: str) -> Dict[str, Any]:
        """Process incoming sample with full workflow automation"""
        try:
            # Register sample
            sample = await self.sample_manager.register_sample(sample_data)
            
            # Create intake workflow if configured
            if self.config.get('auto_create_intake_workflow', True):
                workflow_data = {
                    'name': f'Intake Workflow - {sample.barcode}',
                    'sample_ids': [sample.id],
                    'created_by': operator,
                    'assigned_to': operator
                }
                
                # Find intake template
                intake_templates = [t for t in self.workflow_engine.templates.values()
                                  if t.workflow_type.value == 'sample_intake']
                
                if intake_templates:
                    workflow = await self.workflow_engine.create_workflow_from_template(
                        intake_templates[0].id, workflow_data
                    )
                    await self.workflow_engine.start_workflow(workflow.id, operator)
                    
                    await self._add_notification(
                        "success",
                        "Sample Received",
                        f"Sample {sample.barcode} registered and intake workflow started",
                        operator
                    )
                else:
                    await self._add_notification(
                        "warning",
                        "Sample Received",
                        f"Sample {sample.barcode} registered but no intake workflow template available",
                        operator
                    )
            
            return {
                "success": True,
                "sample": sample,
                "message": f"Sample {sample.barcode} successfully registered"
            }
            
        except Exception as e:
            self.logger.error(f"Error receiving sample: {e}")
            await self._add_notification(
                "error",
                "Sample Registration Failed",
                f"Failed to register sample: {str(e)}",
                operator
            )
            return {
                "success": False,
                "error": str(e),
                "message": "Failed to register sample"
            }
    
    async def search_samples(self, 
                           search_criteria: Dict[str, Any],
                           operator: str) -> List[Sample]:
        """Search samples based on various criteria"""
        results = []
        
        # Get all samples (in a real system, this would be a database query)
        all_samples = list(self.sample_manager.samples.values())
        
        for sample in all_samples:
            match = True
            
            # Filter by barcode
            if 'barcode' in search_criteria:
                if search_criteria['barcode'].lower() not in sample.barcode.lower():
                    match = False
            
            # Filter by status
            if 'status' in search_criteria:
                if sample.status.value != search_criteria['status']:
                    match = False
            
            # Filter by sample type
            if 'type' in search_criteria:
                if sample.sample_type.value != search_criteria['type']:
                    match = False
            
            # Filter by date range
            if 'start_date' in search_criteria:
                if sample.received_date < search_criteria['start_date']:
                    match = False
            
            if 'end_date' in search_criteria:
                if sample.received_date > search_criteria['end_date']:
                    match = False
            
            # Filter by project
            if 'project_id' in search_criteria:
                if sample.project_id != search_criteria['project_id']:
                    match = False
            
            if match:
                results.append(sample)
        
        self.logger.info(f"Sample search by {operator}: {len(results)} results")
        return results
    
    async def get_sample_details(self, 
                               identifier: str,
                               operator: str) -> Optional[Dict[str, Any]]:
        """Get complete sample information including workflow status"""
        sample = await self.sample_manager.get_sample(identifier)
        if not sample:
            return None
        
        # Get associated workflows
        associated_workflows = []
        for workflow in self.workflow_engine.active_workflows.values():
            if sample.id in workflow.sample_ids:
                associated_workflows.append({
                    'id': workflow.id,
                    'name': workflow.name,
                    'status': workflow.status.value,
                    'progress': self._calculate_workflow_progress(workflow)
                })
        
        # Get completed workflows
        for workflow in self.workflow_engine.completed_workflows:
            if sample.id in workflow.sample_ids:
                associated_workflows.append({
                    'id': workflow.id,
                    'name': workflow.name,
                    'status': workflow.status.value,
                    'progress': 100
                })
        
        return {
            'sample': sample,
            'workflows': associated_workflows,
            'custody_chain': sample.custody_chain,
            'test_status': {
                'requested': sample.requested_tests,
                'completed': sample.completed_tests,
                'remaining': list(set(sample.requested_tests) - set(sample.completed_tests))
            }
        }
    
    # Workflow Operations
    async def start_analysis_workflow(self, 
                                    sample_ids: List[str],
                                    test_type: str,
                                    operator: str) -> Dict[str, Any]:
        """Start analytical testing workflow for samples"""
        try:
            workflow_data = {
                'name': f'{test_type} Analysis - {datetime.now().strftime("%Y%m%d_%H%M")}',
                'type': 'analytical_testing',
                'sample_ids': sample_ids,
                'created_by': operator,
                'assigned_to': operator
            }
            
            # Find appropriate template (simplified - would be more sophisticated)
            template_id = None
            for template in self.workflow_engine.templates.values():
                if template.workflow_type.value == 'analytical_testing':
                    template_id = template.id
                    break
            
            if not template_id:
                return {
                    "success": False,
                    "error": "No analytical testing template available",
                    "message": "Cannot start analysis workflow"
                }
            
            workflow = await self.workflow_engine.create_workflow_from_template(
                template_id, workflow_data
            )
            await self.workflow_engine.start_workflow(workflow.id, operator)
            
            # Update sample statuses
            for sample_id in sample_ids:
                await self.sample_manager.update_sample_status(
                    sample_id, SampleStatus.IN_PROGRESS, operator
                )
            
            await self._add_notification(
                "success",
                "Analysis Started",
                f"Analysis workflow started for {len(sample_ids)} samples",
                operator
            )
            
            return {
                "success": True,
                "workflow": workflow,
                "message": "Analysis workflow started successfully"
            }
            
        except Exception as e:
            self.logger.error(f"Error starting analysis workflow: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "Failed to start analysis workflow"
            }
    
    async def complete_task(self, 
                          workflow_id: str,
                          task_id: str,
                          result_data: Dict[str, Any],
                          operator: str) -> Dict[str, Any]:
        """Complete a workflow task with results"""
        try:
            success = await self.workflow_engine.complete_task(
                workflow_id, task_id, operator, result_data
            )
            
            if success:
                # Check if this was a test completion
                workflow = self.workflow_engine.active_workflows.get(workflow_id)
                if workflow:
                    task = next((t for t in workflow.tasks if t.id == task_id), None)
                    if task and task.task_type.value == 'analysis':
                        # Add test results to samples
                        for sample_id in workflow.sample_ids:
                            await self.sample_manager.add_test_result(
                                sample_id, task.name, result_data, operator
                            )
                
                await self._add_notification(
                    "success",
                    "Task Completed",
                    f"Task '{task.name if 'task' in locals() else 'Unknown'}' completed successfully",
                    operator
                )
                
                return {
                    "success": True,
                    "message": "Task completed successfully"
                }
            else:
                return {
                    "success": False,
                    "error": "Task not found or cannot be completed",
                    "message": "Failed to complete task"
                }
                
        except Exception as e:
            self.logger.error(f"Error completing task: {e}")
            return {
                "success": False,
                "error": str(e),
                "message": "Failed to complete task"
            }
    
    # Dashboard and Monitoring
    async def get_dashboard_data(self, operator: str) -> Dict[str, Any]:
        """Get dashboard data for laboratory overview"""
        try:
            # Sample statistics
            sample_stats = await self.sample_manager.get_statistics()
            
            # Workflow statistics
            workflow_stats = await self.workflow_engine.get_workflow_statistics()
            
            # Get priority items
            overdue_samples = await self.sample_manager.get_overdue_samples()
            high_priority_samples = await self.sample_manager.get_high_priority_samples()
            
            # Get active workflows
            active_workflows = list(self.workflow_engine.active_workflows.values())
            
            # Recent notifications
            recent_notifications = self.notifications[-10:]  # Last 10 notifications
            
            return {
                "sample_statistics": sample_stats,
                "workflow_statistics": workflow_stats,
                "alerts": {
                    "overdue_samples": len(overdue_samples),
                    "high_priority_samples": len(high_priority_samples),
                    "pending_approvals": len([w for w in active_workflows 
                                            if any(t.requires_approval and 
                                                 t.status.value == 'pending' 
                                                 for t in w.tasks)])
                },
                "active_workflows": [{
                    "id": w.id,
                    "name": w.name,
                    "status": w.status.value,
                    "progress": self._calculate_workflow_progress(w),
                    "due_date": w.due_date.isoformat() if w.due_date else None
                } for w in active_workflows[:5]],  # Top 5 workflows
                "notifications": [
                    {
                        "type": n.type,
                        "title": n.title,
                        "message": n.message,
                        "timestamp": n.timestamp.isoformat()
                    } for n in recent_notifications
                ]
            }
            
        except Exception as e:
            self.logger.error(f"Error getting dashboard data: {e}")
            return {
                "error": str(e),
                "message": "Failed to load dashboard data"
            }
    
    async def get_my_tasks(self, operator: str) -> List[Dict[str, Any]]:
        """Get tasks assigned to specific operator"""
        my_tasks = []
        
        for workflow in self.workflow_engine.active_workflows.values():
            for task in workflow.tasks:
                if (task.assigned_to == operator and 
                    task.status.value in ['pending', 'in_progress']):
                    my_tasks.append({
                        'workflow_id': workflow.id,
                        'workflow_name': workflow.name,
                        'task_id': task.id,
                        'task_name': task.name,
                        'task_type': task.task_type.value,
                        'status': task.status.value,
                        'estimated_duration': task.estimated_duration_minutes,
                        'started_at': task.started_at.isoformat() if task.started_at else None,
                        'description': task.description
                    })
        
        return my_tasks
    
    # Utility Methods
    def _calculate_workflow_progress(self, workflow: LaboratoryWorkflow) -> int:
        """Calculate workflow completion percentage"""
        if not workflow.tasks:
            return 0
        
        completed_tasks = len([t for t in workflow.tasks 
                             if t.status == WorkflowStatus.COMPLETED])
        return int((completed_tasks / len(workflow.tasks)) * 100)
    
    async def _add_notification(self, 
                              notification_type: str,
                              title: str,
                              message: str,
                              recipient: Optional[str] = None) -> None:
        """Add system notification"""
        notification = LIMSNotification(
            id=str(len(self.notifications) + 1),
            timestamp=datetime.now(),
            type=notification_type,
            title=title,
            message=message,
            recipient=recipient
        )
        
        self.notifications.append(notification)
        
        # In a real system, you might send email, SMS, or push notifications
        self.logger.info(f"Notification added: {title} - {message}")
    
    async def initialize(self) -> bool:
        """Initialize the LIMS interface"""
        try:
            self.logger.info("LIMS Interface initializing...")
            
            # Add welcome notification
            await self._add_notification(
                "info",
                "ALIMS Started",
                "Agentic Laboratory Information Management System is now active"
            )
            
            self.logger.info("LIMS Interface initialization complete")
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to initialize LIMS Interface: {e}")
            return False
    
    async def cleanup(self) -> None:
        """Cleanup resources"""
        self.logger.info("LIMS Interface shutting down...")
        
        # Add shutdown notification
        await self._add_notification(
            "info",
            "ALIMS Shutdown",
            "Laboratory system is shutting down"
        )
    
    def is_healthy(self) -> bool:
        """Check if interface is operating normally"""
        return (self.sample_manager.is_healthy() and 
                self.workflow_engine.is_healthy())
