"""
ALIMS Laboratory Workflow Engine
Automated workflow management for laboratory operations
"""

import asyncio
import logging
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from enum import Enum
import uuid

from .sample_manager import Sample, SampleStatus


class WorkflowType(Enum):
    """Types of laboratory workflows"""
    SAMPLE_INTAKE = "sample_intake"
    ANALYTICAL_TESTING = "analytical_testing"
    QUALITY_CONTROL = "quality_control"
    METHOD_VALIDATION = "method_validation"
    INSTRUMENT_MAINTENANCE = "instrument_maintenance"
    BATCH_RELEASE = "batch_release"
    REGULATORY_REPORTING = "regulatory_reporting"


class WorkflowStatus(Enum):
    """Workflow execution status"""
    PENDING = "pending"
    ACTIVE = "active"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"
    ON_HOLD = "on_hold"


class TaskType(Enum):
    """Types of workflow tasks"""
    SAMPLE_PREPARATION = "sample_preparation"
    INSTRUMENT_SETUP = "instrument_setup"
    ANALYSIS = "analysis"
    DATA_REVIEW = "data_review"
    QUALITY_CHECK = "quality_check"
    DOCUMENTATION = "documentation"
    APPROVAL = "approval"
    NOTIFICATION = "notification"


@dataclass
class WorkflowTask:
    """Individual task within a workflow"""
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    task_type: TaskType = TaskType.ANALYSIS
    description: str = ""
    
    # Dependencies and sequencing
    dependencies: List[str] = field(default_factory=list)  # Task IDs this depends on
    estimated_duration_minutes: int = 30
    
    # Assignment
    assigned_to: Optional[str] = None
    required_skills: List[str] = field(default_factory=list)
    
    # Resources
    required_instruments: List[str] = field(default_factory=list)
    required_materials: List[str] = field(default_factory=list)
    
    # Execution
    status: WorkflowStatus = WorkflowStatus.PENDING
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    
    # Results and notes
    result_data: Dict[str, Any] = field(default_factory=dict)
    notes: str = ""
    
    # Quality control
    requires_approval: bool = False
    approved_by: Optional[str] = None
    approved_at: Optional[datetime] = None


@dataclass
class LaboratoryWorkflowTemplate:
    """Template for standardized laboratory workflows"""
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    workflow_type: WorkflowType = WorkflowType.ANALYTICAL_TESTING
    description: str = ""
    version: str = "1.0"
    
    # Template tasks
    task_templates: List[Dict[str, Any]] = field(default_factory=list)
    
    # Validation and compliance
    sop_reference: Optional[str] = None
    regulatory_requirements: List[str] = field(default_factory=list)
    validation_status: str = "draft"  # draft, validated, approved, deprecated
    
    # Metadata
    created_by: str = ""
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)


@dataclass
class LaboratoryWorkflow:
    """Active laboratory workflow instance"""
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    template_id: Optional[str] = None
    name: str = ""
    workflow_type: WorkflowType = WorkflowType.ANALYTICAL_TESTING
    
    # Associated samples
    sample_ids: List[str] = field(default_factory=list)
    
    # Workflow execution
    tasks: List[WorkflowTask] = field(default_factory=list)
    status: WorkflowStatus = WorkflowStatus.PENDING
    priority: int = 5  # 1-10 scale
    
    # Timing
    created_at: datetime = field(default_factory=datetime.now)
    started_at: Optional[datetime] = None
    due_date: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    
    # Assignment and approval
    created_by: str = ""
    assigned_to: Optional[str] = None
    supervisor: Optional[str] = None
    
    # Results and documentation
    results: Dict[str, Any] = field(default_factory=dict)
    attachments: List[str] = field(default_factory=list)
    notes: str = ""


class LaboratoryWorkflowEngine:
    """
    Laboratory workflow automation engine
    
    Manages workflow templates, executes workflows, tracks progress,
    and ensures compliance with laboratory standards.
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.logger = logging.getLogger("LaboratoryWorkflow")
        self.config = config
        
        # Workflow storage
        self.templates: Dict[str, LaboratoryWorkflowTemplate] = {}
        self.active_workflows: Dict[str, LaboratoryWorkflow] = {}
        self.completed_workflows: List[LaboratoryWorkflow] = []
        
        # Resource tracking
        self.available_instruments: Dict[str, bool] = {}
        self.operator_assignments: Dict[str, List[str]] = {}  # operator -> workflow_ids
        
        # Statistics
        self.total_workflows_executed = 0
        self.total_tasks_completed = 0
        
        self.logger.info("Laboratory Workflow Engine initialized")
        
        # Load default templates
        asyncio.create_task(self._load_default_templates())
    
    async def create_workflow_template(self, 
                                     template_data: Dict[str, Any]) -> LaboratoryWorkflowTemplate:
        """Create a new workflow template"""
        try:
            template = LaboratoryWorkflowTemplate(
                name=template_data['name'],
                workflow_type=WorkflowType(template_data.get('type', 'analytical_testing')),
                description=template_data.get('description', ''),
                version=template_data.get('version', '1.0'),
                task_templates=template_data.get('tasks', []),
                sop_reference=template_data.get('sop_reference'),
                regulatory_requirements=template_data.get('regulatory_requirements', []),
                created_by=template_data.get('created_by', '')
            )
            
            self.templates[template.id] = template
            
            self.logger.info(f"Workflow template created: {template.name} ({template.id})")
            
            return template
            
        except Exception as e:
            self.logger.error(f"Error creating workflow template: {e}")
            raise
    
    async def create_workflow_from_template(self, 
                                          template_id: str,
                                          workflow_data: Dict[str, Any]) -> LaboratoryWorkflow:
        """Create workflow instance from template"""
        template = self.templates.get(template_id)
        if not template:
            raise ValueError(f"Template not found: {template_id}")
        
        try:
            # Create workflow from template
            workflow = LaboratoryWorkflow(
                template_id=template_id,
                name=workflow_data.get('name', template.name),
                workflow_type=template.workflow_type,
                sample_ids=workflow_data.get('sample_ids', []),
                priority=workflow_data.get('priority', 5),
                due_date=workflow_data.get('due_date'),
                created_by=workflow_data.get('created_by', ''),
                assigned_to=workflow_data.get('assigned_to'),
                supervisor=workflow_data.get('supervisor')
            )
            
            # Create tasks from template
            for task_template in template.task_templates:
                task = WorkflowTask(
                    name=task_template['name'],
                    task_type=TaskType(task_template.get('type', 'analysis')),
                    description=task_template.get('description', ''),
                    dependencies=task_template.get('dependencies', []),
                    estimated_duration_minutes=task_template.get('duration', 30),
                    required_skills=task_template.get('required_skills', []),
                    required_instruments=task_template.get('required_instruments', []),
                    required_materials=task_template.get('required_materials', []),
                    requires_approval=task_template.get('requires_approval', False)
                )
                workflow.tasks.append(task)
            
            # Store workflow
            self.active_workflows[workflow.id] = workflow
            
            self.logger.info(f"Workflow created from template: {workflow.name} ({workflow.id})")
            
            return workflow
            
        except Exception as e:
            self.logger.error(f"Error creating workflow from template: {e}")
            raise
    
    async def start_workflow(self, 
                           workflow_id: str,
                           operator: str) -> bool:
        """Start workflow execution"""
        workflow = self.active_workflows.get(workflow_id)
        if not workflow:
            return False
        
        try:
            workflow.status = WorkflowStatus.ACTIVE
            workflow.started_at = datetime.now()
            
            # Find and start first available tasks (no dependencies)
            ready_tasks = self._get_ready_tasks(workflow)
            for task in ready_tasks:
                await self._start_task(task, operator)
            
            self.logger.info(f"Workflow started: {workflow.name} ({workflow_id})")
            
            return True
            
        except Exception as e:
            self.logger.error(f"Error starting workflow {workflow_id}: {e}")
            return False
    
    async def complete_task(self, 
                          workflow_id: str,
                          task_id: str,
                          operator: str,
                          result_data: Dict[str, Any] = None,
                          notes: str = "") -> bool:
        """Complete a workflow task"""
        workflow = self.active_workflows.get(workflow_id)
        if not workflow:
            return False
        
        task = next((t for t in workflow.tasks if t.id == task_id), None)
        if not task:
            return False
        
        try:
            # Update task
            task.status = WorkflowStatus.COMPLETED
            task.completed_at = datetime.now()
            task.result_data = result_data or {}
            task.notes = notes
            
            self.total_tasks_completed += 1
            
            # Check if approval required
            if task.requires_approval:
                task.status = WorkflowStatus.PENDING  # Wait for approval
                self.logger.info(f"Task completed, pending approval: {task.name}")
            else:
                # Start dependent tasks
                dependent_tasks = self._get_dependent_tasks(workflow, task_id)
                for dependent_task in dependent_tasks:
                    if self._are_dependencies_complete(workflow, dependent_task):
                        await self._start_task(dependent_task, operator)
            
            # Check if workflow is complete
            if self._is_workflow_complete(workflow):
                await self._complete_workflow(workflow)
            
            self.logger.info(f"Task completed: {task.name} in workflow {workflow.name}")
            
            return True
            
        except Exception as e:
            self.logger.error(f"Error completing task {task_id}: {e}")
            return False
    
    async def approve_task(self, 
                         workflow_id: str,
                         task_id: str,
                         approver: str) -> bool:
        """Approve a completed task"""
        workflow = self.active_workflows.get(workflow_id)
        if not workflow:
            return False
        
        task = next((t for t in workflow.tasks if t.id == task_id), None)
        if not task or task.status != WorkflowStatus.PENDING:
            return False
        
        try:
            task.approved_by = approver
            task.approved_at = datetime.now()
            task.status = WorkflowStatus.COMPLETED
            
            # Start dependent tasks
            dependent_tasks = self._get_dependent_tasks(workflow, task_id)
            for dependent_task in dependent_tasks:
                if self._are_dependencies_complete(workflow, dependent_task):
                    await self._start_task(dependent_task, approver)
            
            # Check if workflow is complete
            if self._is_workflow_complete(workflow):
                await self._complete_workflow(workflow)
            
            self.logger.info(f"Task approved: {task.name} by {approver}")
            
            return True
            
        except Exception as e:
            self.logger.error(f"Error approving task {task_id}: {e}")
            return False
    
    def _get_ready_tasks(self, workflow: LaboratoryWorkflow) -> List[WorkflowTask]:
        """Get tasks that are ready to start (no pending dependencies)"""
        ready_tasks = []
        for task in workflow.tasks:
            if (task.status == WorkflowStatus.PENDING and 
                self._are_dependencies_complete(workflow, task)):
                ready_tasks.append(task)
        return ready_tasks
    
    def _get_dependent_tasks(self, 
                           workflow: LaboratoryWorkflow, 
                           completed_task_id: str) -> List[WorkflowTask]:
        """Get tasks that depend on the completed task"""
        dependent_tasks = []
        for task in workflow.tasks:
            if completed_task_id in task.dependencies:
                dependent_tasks.append(task)
        return dependent_tasks
    
    def _are_dependencies_complete(self, 
                                 workflow: LaboratoryWorkflow, 
                                 task: WorkflowTask) -> bool:
        """Check if all task dependencies are completed"""
        for dep_id in task.dependencies:
            dep_task = next((t for t in workflow.tasks if t.id == dep_id), None)
            if not dep_task or dep_task.status != WorkflowStatus.COMPLETED:
                return False
        return True
    
    def _is_workflow_complete(self, workflow: LaboratoryWorkflow) -> bool:
        """Check if all workflow tasks are completed"""
        return all(task.status == WorkflowStatus.COMPLETED for task in workflow.tasks)
    
    async def _start_task(self, task: WorkflowTask, operator: str) -> None:
        """Start execution of a task"""
        task.status = WorkflowStatus.IN_PROGRESS
        task.started_at = datetime.now()
        task.assigned_to = operator
        
        # Track operator assignment
        if operator not in self.operator_assignments:
            self.operator_assignments[operator] = []
        # Note: In a real system, you'd track this at the workflow level
    
    async def _complete_workflow(self, workflow: LaboratoryWorkflow) -> None:
        """Complete a workflow"""
        workflow.status = WorkflowStatus.COMPLETED
        workflow.completed_at = datetime.now()
        
        # Move to completed workflows
        self.completed_workflows.append(workflow)
        del self.active_workflows[workflow.id]
        
        self.total_workflows_executed += 1
        
        self.logger.info(f"Workflow completed: {workflow.name}")
    
    async def get_workflow_statistics(self) -> Dict[str, Any]:
        """Get workflow execution statistics"""
        active_count = len(self.active_workflows)
        overdue_count = len([w for w in self.active_workflows.values()
                           if w.due_date and w.due_date < datetime.now()])
        
        return {
            "active_workflows": active_count,
            "completed_workflows": len(self.completed_workflows),
            "total_executed": self.total_workflows_executed,
            "total_tasks_completed": self.total_tasks_completed,
            "overdue_workflows": overdue_count,
            "templates_available": len(self.templates)
        }
    
    async def _load_default_templates(self) -> None:
        """Load default workflow templates"""
        # Sample intake workflow
        sample_intake_template = {
            'name': 'Standard Sample Intake',
            'type': 'sample_intake',
            'description': 'Standard procedure for receiving and registering samples',
            'tasks': [
                {
                    'name': 'Sample Receipt Verification',
                    'type': 'quality_check',
                    'description': 'Verify sample integrity and documentation',
                    'duration': 15,
                    'required_skills': ['sample_handling']
                },
                {
                    'name': 'Sample Registration',
                    'type': 'documentation',
                    'description': 'Register sample in LIMS system',
                    'duration': 10,
                    'dependencies': ['Sample Receipt Verification']
                },
                {
                    'name': 'Storage Assignment',
                    'type': 'sample_preparation',
                    'description': 'Assign appropriate storage location',
                    'duration': 5,
                    'dependencies': ['Sample Registration']
                }
            ]
        }
        
        await self.create_workflow_template(sample_intake_template)
        
        self.logger.info("Default workflow templates loaded")
    
    def is_healthy(self) -> bool:
        """Check if workflow engine is operating normally"""
        return len(self.active_workflows) < 100  # Reasonable limit
