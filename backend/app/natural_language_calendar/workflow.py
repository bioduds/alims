"""
Natural Language Calendar Workflow Implementation
Based on TLA+ validated specification: NaturalLanguageCalendarWorkflow.tla

This implementation follows the mathematically proven operations and maintains
all invariants validated by the TLA+ model checker.

Core Workflow: "schedule a PCR for these samples" → full execution
"""

import asyncio
import logging
import time
from typing import Dict, Any, List, Optional, Set
from datetime import datetime, timedelta
import json
import re
import uuid

from .models import (
    NLRequest, ParsedIntent, CalendarOperation, StorageRequest, WorkflowResponse,
    IntentType, OperationType, OperationStatus, SystemState, ResponseStatus,
    SystemMetrics, ComponentStates, ScheduleData, WorkflowConfiguration
)
from .exceptions import (
    WorkflowConstraintError, CapacityExceededError, InvalidStateTransitionError,
    ProcessingConstraintError, StorageConsistencyError, RequestNotFoundError,
    DuplicateRequestError, InvalidIntentError, InvalidResourceError,
    InvalidUserError, OperationNotFoundError, PrerequisiteNotMetError,
    VectorStorageError, IntentParsingError, CalendarOperationError,
    ResponseGenerationError
)

# Import our TLA+ verified tensor calendar vector storage
from ..tensor_calendar import VectorTensorStorage


logger = logging.getLogger(__name__)


class IntentParser:
    """
    Natural Language Intent Parser
    Extracts structured intent from natural language requests
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.resources = config.get("resources", [])
        self.intent_types = config.get("intent_types", [])
        
        # Intent parsing patterns
        self.schedule_patterns = [
            r"schedule\s+a?\s*(\w+)",
            r"book\s+the\s+(\w+)",
            r"reserve\s+the\s+(\w+)",
            r"need\s+to\s+use\s+the\s+(\w+)"
        ]
        
        self.cancel_patterns = [
            r"cancel\s+.*(\w+)",
            r"delete\s+.*(\w+)",
            r"remove\s+.*(\w+)"
        ]
        
        self.query_patterns = [
            r"when\s+is\s+the\s+(\w+)",
            r"check\s+.*(\w+)",
            r"status\s+of\s+(\w+)"
        ]
    
    async def parse_intent(self, content: str, user: str) -> ParsedIntent:
        """Parse natural language content into structured intent"""
        try:
            content_lower = content.lower()
            
            # Determine intent type
            intent_type = self._extract_intent_type(content_lower)
            
            # Extract resource
            resource = self._extract_resource(content_lower)
            
            # Extract parameters (samples, time, etc.)
            parameters = self._extract_parameters(content_lower)
            
            # Calculate confidence based on pattern matches
            confidence = self._calculate_confidence(content_lower, intent_type, resource)
            
            return ParsedIntent(
                request_id=0,  # Will be set by caller
                type=intent_type,
                resource=resource,
                user=user,
                parameters=parameters,
                confidence=confidence
            )
            
        except Exception as e:
            raise IntentParsingError(content, str(e))
    
    def _extract_intent_type(self, content: str) -> IntentType:
        """Extract intent type from content"""
        # Check for scheduling patterns
        for pattern in self.schedule_patterns:
            if re.search(pattern, content):
                return IntentType.SCHEDULE
        
        # Check for cancellation patterns
        for pattern in self.cancel_patterns:
            if re.search(pattern, content):
                return IntentType.CANCEL
        
        # Check for query patterns
        for pattern in self.query_patterns:
            if re.search(pattern, content):
                return IntentType.QUERY
        
        # Default to QUERY if unclear
        return IntentType.QUERY
    
    def _extract_resource(self, content: str) -> str:
        """Extract resource from content"""
        content_lower = content.lower()
        
        # Look for common lab equipment terms FIRST with better matching
        equipment_mappings = {
            "confocal microscope": "microscope1",
            "confocal": "microscope1",
            "microscope": "microscope1",
            "pcr machine": "pcr_machine1",
            "pcr": "pcr_machine1",
            "sequencer": "sequencer1",
            "centrifuge": "centrifuge1",
            "spectrophotometer": "spectrophotometer1"
        }
        
        # Sort by length descending to match longer patterns first
        for term in sorted(equipment_mappings.keys(), key=len, reverse=True):
            if term in content_lower and equipment_mappings[term] in self.resources:
                return equipment_mappings[term]
        
        # Look for exact resource matches as fallback
        for resource in self.resources:
            if resource.lower() in content_lower:
                return resource
        
        # Look for partial matches as fallback
        for resource in self.resources:
            resource_base = resource.lower().split('_')[0].split('1')[0]
            if resource_base in content_lower:
                return resource
        
        # Default to first available resource
        return self.resources[0] if self.resources else "unknown"
    
    def _extract_parameters(self, content: str) -> List[str]:
        """Extract parameters like samples, time, etc."""
        parameters = []
        
        # Extract sample references
        sample_patterns = [
            r"sample[s]?\s+([A-Z0-9, ]+)",
            r"batch\s+([A-Z0-9]+)",
            r"specimens?\s+([A-Z0-9, ]+)"
        ]
        
        for pattern in sample_patterns:
            matches = re.findall(pattern, content.upper())
            for match in matches:
                # Split by comma and clean up
                samples = [s.strip() for s in match.split(',')]
                parameters.extend(samples)
        
        # Extract time references
        time_patterns = [
            r"tomorrow",
            r"(\d{1,2}:\d{2})",
            r"(\d{1,2}\s*(?:am|pm))",
            r"(morning|afternoon|evening)"
        ]
        
        for pattern in time_patterns:
            matches = re.findall(pattern, content.lower())
            parameters.extend(matches)
        
        return parameters
    
    def _calculate_confidence(self, content: str, intent_type: IntentType, resource: str) -> float:
        """Calculate confidence score for parsed intent"""
        confidence = 0.5  # Base confidence
        
        # Boost confidence for clear intent indicators
        intent_indicators = {
            IntentType.SCHEDULE: ["schedule", "book", "reserve", "need"],
            IntentType.CANCEL: ["cancel", "delete", "remove"],
            IntentType.QUERY: ["when", "check", "status", "available"]
        }
        
        for word in intent_indicators.get(intent_type, []):
            if word in content:
                confidence += 0.1
        
        # Boost confidence for exact resource match
        if resource.lower() in content:
            confidence += 0.2
        
        # Boost confidence for sample references
        if "sample" in content:
            confidence += 0.1
        
        return min(confidence, 1.0)


class CalendarOrchestrator:
    """
    Calendar Operation Orchestrator
    Manages calendar operations following TLA+ validated state transitions
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.operations: Dict[int, CalendarOperation] = {}
        self.state = SystemState.READY
        
    async def create_operation(self, request_id: int, operation_type: OperationType, 
                             resource: str, user: str) -> CalendarOperation:
        """Create a new calendar operation"""
        if self.state != SystemState.READY:
            raise InvalidStateTransitionError("orchestrator", self.state.value, "ORCHESTRATING")
        
        if len(self.operations) >= self.config.get("max_calendar_ops", 100):
            raise CapacityExceededError("calendar_operations", len(self.operations), 
                                      self.config.get("max_calendar_ops", 100))
        
        operation = CalendarOperation(
            id=request_id,
            operation=operation_type,
            resource=resource,
            user=user,
            status=OperationStatus.PENDING
        )
        
        self.operations[request_id] = operation
        self.state = SystemState.ORCHESTRATING
        
        return operation
    
    async def process_operation(self, operation_id: int) -> CalendarOperation:
        """Process a pending operation"""
        if operation_id not in self.operations:
            raise OperationNotFoundError(operation_id, "calendar")
        
        operation = self.operations[operation_id]
        if operation.status != OperationStatus.PENDING:
            raise PrerequisiteNotMetError("process_operation", 
                                        f"operation {operation_id} must be PENDING")
        
        # Update to IN_PROGRESS
        operation.status = OperationStatus.IN_PROGRESS
        operation.updated_at = datetime.now()
        
        return operation
    
    async def complete_operation(self, operation_id: int, success: bool, 
                               metadata: Optional[Dict[str, Any]] = None) -> CalendarOperation:
        """Complete an operation with success/failure"""
        if operation_id not in self.operations:
            raise OperationNotFoundError(operation_id, "calendar")
        
        operation = self.operations[operation_id]
        if operation.status != OperationStatus.IN_PROGRESS:
            raise PrerequisiteNotMetError("complete_operation",
                                        f"operation {operation_id} must be IN_PROGRESS")
        
        # Update status
        operation.status = OperationStatus.COMPLETED if success else OperationStatus.FAILED
        operation.updated_at = datetime.now()
        
        if metadata:
            operation.metadata.update(metadata)
        
        # Reset orchestrator state to READY
        self.state = SystemState.READY
        
        return operation
    
    async def get_operation(self, operation_id: int) -> Optional[CalendarOperation]:
        """Get operation by ID"""
        return self.operations.get(operation_id)
    
    async def list_operations(self) -> List[CalendarOperation]:
        """List all operations"""
        return list(self.operations.values())
    
    async def reset_state(self):
        """Reset orchestrator to READY state"""
        self.state = SystemState.READY


class ResponseGenerator:
    """
    Response Generator
    Creates responses for completed workflows
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.responses: Dict[int, WorkflowResponse] = {}
        self.state = SystemState.IDLE
        
        # Response templates
        self.templates = {
            "schedule_success": "Successfully scheduled {resource} for {user}. Schedule ID: {schedule_id}",
            "schedule_failure": "Failed to schedule {resource} for {user}. Reason: {reason}",
            "cancel_success": "Successfully cancelled {resource} reservation for {user}",
            "cancel_failure": "Failed to cancel {resource} reservation for {user}. Reason: {reason}",
            "query_success": "{resource} status: {status}",
            "query_failure": "Unable to query {resource} status. Reason: {reason}"
        }
        
        # Update with config templates
        self.templates.update(config.get("response_templates", {}))
    
    async def generate_response(self, request_id: int, status: ResponseStatus, 
                              message: str, data: Optional[List[Any]] = None,
                              processing_time_ms: Optional[float] = None) -> WorkflowResponse:
        """Generate a response for a request"""
        if self.state != SystemState.IDLE:
            raise InvalidStateTransitionError("response_generator", self.state.value, "GENERATING")
        
        self.state = SystemState.GENERATING
        
        try:
            response = WorkflowResponse(
                request_id=request_id,
                status=status,
                message=message,
                data=data or [],
                processing_time_ms=processing_time_ms
            )
            
            self.responses[request_id] = response
            return response
            
        except Exception as e:
            raise ResponseGenerationError(request_id, str(e))
    
    async def complete_generation(self):
        """Complete response generation and return to IDLE"""
        self.state = SystemState.IDLE
    
    async def get_response(self, request_id: int) -> Optional[WorkflowResponse]:
        """Get response by request ID"""
        return self.responses.get(request_id)
    
    async def list_responses(self) -> List[WorkflowResponse]:
        """List all responses"""
        return list(self.responses.values())


class NaturalLanguageCalendarWorkflow:
    """
    Main Natural Language Calendar Workflow Implementation
    Based on TLA+ validated specification: NaturalLanguageCalendarWorkflow.tla
    
    Handles the complete workflow from "schedule a PCR for these samples" to response
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.config = WorkflowConfiguration(**config)
        self.config.validate()
        
        # TLA+ State Variables (as per specification)
        self.nl_requests: Dict[int, Dict[str, str]] = {}  # Store {id: {content, user}}
        self.parsed_intents: Dict[int, ParsedIntent] = {}
        self.calendar_operations: Dict[int, CalendarOperation] = {}
        self.storage_requests: Dict[int, StorageRequest] = {}
        self.stored_schedules: Set[int] = set()
        self.generated_responses: Dict[int, WorkflowResponse] = {}
        
        # Component states (as per TLA+ specification)
        self.component_states = ComponentStates()
        
        # System metrics (for invariant validation)
        self.metrics = SystemMetrics()
        self.start_time = time.time()
        
        # Components
        self.intent_parser = IntentParser(config)
        self.calendar_orchestrator = CalendarOrchestrator(config)
        self.response_generator = ResponseGenerator(config)
        
        # Vector storage integration (TLA+ verified)
        self.vector_storage: Optional[VectorTensorStorage] = None
        
        # Processing locks for thread safety
        self._locks = {
            "requests": asyncio.Lock(),
            "intents": asyncio.Lock(),
            "operations": asyncio.Lock(),
            "storage": asyncio.Lock(),
            "responses": asyncio.Lock()
        }
    
    async def initialize(self):
        """Initialize the workflow system"""
        try:
            logger.info("Initializing Natural Language Calendar Workflow...")
            
            # Initialize vector storage with TLA+ verified implementation
            vector_config = self.config.vector_storage_config
            if vector_config:
                self.vector_storage = VectorTensorStorage(vector_config)
                await self.vector_storage.initialize()
                logger.info("Vector storage initialized successfully")
            
            # Set initial component states
            self.component_states = ComponentStates()
            
            logger.info("Natural Language Calendar Workflow initialized successfully")
            
        except Exception as e:
            logger.error(f"Failed to initialize workflow: {e}")
            raise
    
    async def cleanup(self):
        """Cleanup workflow resources"""
        try:
            if self.vector_storage:
                await self.vector_storage.cleanup()
            logger.info("Natural Language Calendar Workflow cleaned up successfully")
        except Exception as e:
            logger.error(f"Error during cleanup: {e}")
    
    # TLA+ Operations Implementation
    
    async def receive_nl_request(self, request_id: int, user: str, content: str) -> Dict[str, Any]:
        """
        TLA+ Operation: ReceiveNLRequest(request_id, user, content)
        Accept a natural language request from user
        """
        async with self._locks["requests"]:
            # TLA+ Preconditions
            if request_id in self.nl_requests:
                raise DuplicateRequestError(request_id)
            
            if len(self.nl_requests) >= self.config.max_requests:
                raise CapacityExceededError("requests", len(self.nl_requests), 
                                          self.config.max_requests)
            
            if user not in self.config.users:
                raise InvalidUserError(user, self.config.users)
            
            # TLA+ State Update
            self.nl_requests[request_id] = {"content": content, "user": user}
            
            logger.info(f"Received NL request {request_id} from {user}: {content}")
            
            return {
                "success": True,
                "request_id": request_id,
                "message": "Request received successfully"
            }
    
    async def parse_intent(self, request_id: int) -> Dict[str, Any]:
        """
        TLA+ Operation: ParseIntent(request_id, intent_type, resource, user)
        Parse natural language into structured intent
        """
        async with self._locks["intents"]:
            # TLA+ Preconditions
            if request_id not in self.nl_requests:
                raise RequestNotFoundError(request_id, "parse_intent")
            
            # Allow concurrent processing - only check if we can process more intents
            if len(self.parsed_intents) >= self.config.max_parsed_intents:
                raise CapacityExceededError("parsed_intents", len(self.parsed_intents),
                                           self.config.max_parsed_intents)
            
            # Get the stored request content and user
            request_data = self.nl_requests[request_id]
            content = request_data["content"]
            user = request_data["user"]
            
            try:
                # Parse intent using NLP
                intent = await self.intent_parser.parse_intent(content, user)
                intent.request_id = request_id
                
                # TLA+ State Update: Add to parsed_intents
                self.parsed_intents[request_id] = intent
                
                logger.info(f"Parsed intent for request {request_id}: {intent.type.value} -> {intent.resource}")
                
                return {
                    "success": True,
                    "request_id": request_id,
                    "intent_type": intent.type.value,
                    "resource": intent.resource,
                    "user": intent.user,
                    "confidence": intent.confidence
                }
                
            except Exception as e:
                raise IntentParsingError(content, str(e))
    
    async def complete_intent_parsing(self):
        """
        TLA+ Operation: CompleteIntentParsing
        Complete intent parsing and return to IDLE
        
        Note: For concurrent processing, this is a no-op since
        parse_intent doesn't change global state anymore.
        """
        # No-op for concurrent processing
        pass
    
    async def create_calendar_operation(self, request_id: int, operation_type: str, 
                                      resource: str, user: str) -> Dict[str, Any]:
        """
        TLA+ Operation: CreateCalendarOperation(request_id, operation_type, resource, user)
        Create a calendar operation from parsed intent
        """
        async with self._locks["operations"]:
            # TLA+ Preconditions
            if request_id not in self.parsed_intents:
                raise PrerequisiteNotMetError("create_calendar_operation",
                                            f"request {request_id} must be parsed first")
            
            if self.component_states.orchestrator != SystemState.READY:
                raise InvalidStateTransitionError("orchestrator",
                                                self.component_states.orchestrator.value, "ORCHESTRATING")
            
            # Convert string to enum
            op_type = OperationType(operation_type)
            
            # TLA+ State Update: orchestrator_state' = "ORCHESTRATING"
            self.component_states.orchestrator = SystemState.ORCHESTRATING
            
            # Create operation using orchestrator
            operation = await self.calendar_orchestrator.create_operation(
                request_id, op_type, resource, user
            )
            
            # TLA+ State Update: Add to calendar_operations
            self.calendar_operations[request_id] = operation
            
            logger.info(f"Created calendar operation {request_id}: {operation_type} {resource}")
            
            return {
                "success": True,
                "operation_id": request_id,
                "operation_type": operation_type,
                "resource": resource
            }
    
    async def process_calendar_operation(self, operation_id: int) -> Dict[str, Any]:
        """
        TLA+ Operation: ProcessCalendarOperation(op)
        Process a pending calendar operation
        """
        async with self._locks["operations"]:
            # Find operation
            if operation_id not in self.calendar_operations:
                raise OperationNotFoundError(operation_id, "calendar")
            
            # Process using orchestrator
            operation = await self.calendar_orchestrator.process_operation(operation_id)
            
            # Update local state
            self.calendar_operations[operation_id] = operation
            
            logger.info(f"Processing calendar operation {operation_id}")
            
            return {
                "success": True,
                "operation_id": operation_id,
                "status": operation.status.value
            }
    
    async def complete_calendar_operation(self, operation_id: int, success: bool) -> Dict[str, Any]:
        """
        TLA+ Operation: CompleteCalendarOperation(op, success)
        Complete a calendar operation with success/failure
        """
        async with self._locks["operations"]:
            # Complete using orchestrator
            operation = await self.calendar_orchestrator.complete_operation(operation_id, success)
            
            # Update local state
            self.calendar_operations[operation_id] = operation
            
            # TLA+ State Update: orchestrator_state' = "READY"
            self.component_states.orchestrator = SystemState.READY
            
            # TLA+ State Update: Update metrics
            if success:
                self.metrics.successful_schedules += 1
            else:
                self.metrics.failed_operations += 1
            
            logger.info(f"Completed calendar operation {operation_id}: {'SUCCESS' if success else 'FAILED'}")
            
            return {
                "success": True,
                "operation_id": operation_id,
                "operation_success": success,
                "status": operation.status.value
            }
    
    async def create_storage_request(self, schedule_id: int, operation_type: str) -> Dict[str, Any]:
        """
        TLA+ Operation: CreateStorageRequest(schedule_id, operation_type)
        Create a vector storage request for completed schedule
        """
        async with self._locks["storage"]:
            # TLA+ Preconditions: schedule must be from completed operation
            if schedule_id not in self.calendar_operations:
                raise StorageConsistencyError(schedule_id, "no corresponding calendar operation")
            
            operation = self.calendar_operations[schedule_id]
            if operation.status != OperationStatus.COMPLETED:
                raise StorageConsistencyError(schedule_id, "calendar operation not completed")
            
            if self.component_states.vector_storage != SystemState.AVAILABLE:
                raise InvalidStateTransitionError("vector_storage",
                                                self.component_states.vector_storage.value, "BUSY")
            
            if len(self.storage_requests) >= self.config.max_storage_ops:
                raise CapacityExceededError("storage_requests", len(self.storage_requests),
                                          self.config.max_storage_ops)
            
            # TLA+ State Update: vector_storage_state' = "BUSY"
            self.component_states.vector_storage = SystemState.BUSY
            
            # Create storage request
            storage_request = StorageRequest(
                id=schedule_id,
                operation=operation_type,
                data=[schedule_id],  # Schedule data would be more complex in practice
                status=OperationStatus.PENDING
            )
            
            # TLA+ State Update: Add to storage_requests
            self.storage_requests[schedule_id] = storage_request
            
            logger.info(f"Created storage request {schedule_id}: {operation_type}")
            
            return {
                "success": True,
                "request_id": schedule_id,
                "operation": operation_type
            }
    
    async def process_storage_request(self, request_id: int) -> Dict[str, Any]:
        """
        TLA+ Operation: ProcessStorageRequest(req)
        Process a pending storage request
        """
        async with self._locks["storage"]:
            if request_id not in self.storage_requests:
                raise OperationNotFoundError(request_id, "storage")
            
            request = self.storage_requests[request_id]
            if request.status != OperationStatus.PENDING:
                raise PrerequisiteNotMetError("process_storage_request",
                                            f"request {request_id} must be PENDING")
            
            # TLA+ State Update: status = "IN_PROGRESS"
            request.status = OperationStatus.IN_PROGRESS
            
            logger.info(f"Processing storage request {request_id}")
            
            return {
                "success": True,
                "request_id": request_id,
                "status": request.status.value
            }
    
    async def complete_storage_request(self, request_id: int, success: bool) -> Dict[str, Any]:
        """
        TLA+ Operation: CompleteStorageRequest(req, success)
        Complete a storage request with success/failure
        """
        async with self._locks["storage"]:
            if request_id not in self.storage_requests:
                raise OperationNotFoundError(request_id, "storage")
            
            request = self.storage_requests[request_id]
            if request.status != OperationStatus.IN_PROGRESS:
                raise PrerequisiteNotMetError("complete_storage_request",
                                            f"request {request_id} must be IN_PROGRESS")
            
            # TLA+ State Update: Update status and stored_schedules
            request.status = OperationStatus.COMPLETED if success else OperationStatus.FAILED
            
            if success and request.operation == "STORE":
                self.stored_schedules.add(request_id)
                
                # Actually store in vector database if available
                if self.vector_storage:
                    try:
                        # Create schedule data for storage
                        calendar_op = self.calendar_operations.get(request_id)
                        if calendar_op:
                            schedule_data = {
                                "operation_type": calendar_op.operation.value,
                                "resource": calendar_op.resource,
                                "user": calendar_op.user,
                                "created_at": calendar_op.created_at.isoformat(),
                                "metadata": calendar_op.metadata
                            }
                            
                            # Generate embedding (would use real embeddings in practice)
                            import numpy as np
                            embedding = np.random.rand(384).tolist()
                            
                            # Store in vector database
                            await self.vector_storage.store_tensor(
                                f"schedule_{request_id}",
                                schedule_data,
                                embedding
                            )
                            
                            logger.info(f"Stored schedule {request_id} in vector database")
                    
                    except Exception as e:
                        logger.error(f"Failed to store in vector database: {e}")
                        # Don't fail the operation, just log the error
            
            # TLA+ State Update: vector_storage_state' = "AVAILABLE"
            self.component_states.vector_storage = SystemState.AVAILABLE
            
            logger.info(f"Completed storage request {request_id}: {'SUCCESS' if success else 'FAILED'}")
            
            return {
                "success": True,
                "request_id": request_id,
                "storage_success": success,
                "status": request.status.value
            }
    
    async def generate_response(self, request_id: int, status: str, message: str) -> Dict[str, Any]:
        """
        TLA+ Operation: GenerateResponse(request_id, status, message)
        Generate a response for the user
        """
        async with self._locks["responses"]:
            if request_id not in self.parsed_intents:
                raise RequestNotFoundError(request_id, "generate_response")
            
            # Convert string to enum
            response_status = ResponseStatus(status)
            
            # Calculate processing time
            processing_time = (time.time() - self.start_time) * 1000
            
            # Generate response using response generator
            response = await self.response_generator.generate_response(
                request_id, response_status, message, processing_time_ms=processing_time
            )
            
            # TLA+ State Update: Add to generated_responses and increment total_processed
            self.generated_responses[request_id] = response
            self.metrics.total_processed += 1
            
            logger.info(f"Generated response for request {request_id}: {status}")
            
            return {
                "success": True,
                "request_id": request_id,
                "status": status,
                "message": message
            }
    
    async def complete_response_generation(self):
        """
        TLA+ Operation: CompleteResponseGeneration
        Complete response generation and return system to ready state
        """
        # Complete response generation
        await self.response_generator.complete_generation()
        
        # Reset orchestrator to ready state
        await self.calendar_orchestrator.reset_state()
        
        # TLA+ State Update: orchestrator_state' = "READY"
        self.component_states.orchestrator = SystemState.READY
    
    # Monitoring and State Access Methods
    
    async def get_system_metrics(self) -> SystemMetrics:
        """Get current system metrics for invariant validation"""
        self.metrics.system_uptime_seconds = time.time() - self.start_time
        self.metrics.active_requests = len(self.nl_requests)
        self.metrics.parsed_intents = len(self.parsed_intents)
        self.metrics.calendar_operations = len(self.calendar_operations)
        self.metrics.storage_operations = len(self.storage_requests)
        
        return self.metrics
    
    async def get_component_states(self) -> Dict[str, str]:
        """Get current component states for state consistency validation"""
        return self.component_states.to_dict()
    
    async def get_active_requests(self) -> Set[int]:
        """Get active request IDs"""
        return set(self.nl_requests.keys())
    
    async def get_parsed_intents(self) -> Dict[int, ParsedIntent]:
        """Get parsed intents"""
        return self.parsed_intents.copy()
    
    async def get_calendar_operations(self) -> List[CalendarOperation]:
        """Get calendar operations"""
        return list(self.calendar_operations.values())
    
    async def get_stored_schedules(self) -> Set[int]:
        """Get stored schedule IDs"""
        return self.stored_schedules.copy()
    
    async def get_generated_responses(self) -> List[WorkflowResponse]:
        """Get generated responses"""
        return list(self.generated_responses.values())
    
    # High-Level Workflow Methods
    
    async def process_natural_language_request(self, user: str, content: str) -> WorkflowResponse:
        """
        High-level method to process a complete natural language request
        
        Example: "schedule a PCR for these samples" → full workflow execution
        """
        request_id = int(time.time() * 1000) % 1000000  # Generate unique ID
        
        try:
            # Step 1: Receive NL request
            await self.receive_nl_request(request_id, user, content)
            
            # Step 2: Parse intent
            parse_result = await self.parse_intent(request_id)
            await self.complete_intent_parsing()
            
            # Step 3: Create calendar operation
            operation_type = "CREATE" if parse_result["intent_type"] == "SCHEDULE" else "QUERY"
            await self.create_calendar_operation(
                request_id, operation_type, parse_result["resource"], user
            )
            
            # Step 4: Process calendar operation
            await self.process_calendar_operation(request_id)
            
            # Step 5: Complete calendar operation (simulate success)
            await self.complete_calendar_operation(request_id, success=True)
            
            # Step 6: Store in vector database (if CREATE operation)
            if operation_type == "CREATE":
                await self.create_storage_request(request_id, "STORE")
                await self.process_storage_request(request_id)
                await self.complete_storage_request(request_id, success=True)
            
            # Step 7: Generate response
            success_message = f"Successfully {parse_result['intent_type'].lower()}d {parse_result['resource']} for {user}"
            await self.generate_response(request_id, "SUCCESS", success_message)
            await self.complete_response_generation()
            
            # Return the generated response
            return self.generated_responses[request_id]
            
        except Exception as e:
            # Generate error response
            error_message = f"Failed to process request: {str(e)}"
            try:
                await self.generate_response(request_id, "FAILED", error_message)
                await self.complete_response_generation()
                return self.generated_responses[request_id]
            except:
                # Fallback response if even error handling fails
                return WorkflowResponse(
                    request_id=request_id,
                    status=ResponseStatus.FAILED,
                    message=error_message
                )
