# ALIMS Workflow Manager Service - Implementation Plan

## 🎯 **Overview**

The Workflow Manager Service is the central orchestration component for all LIMS (Laboratory Information Management System) workflows within ALIMS. It manages workflow state transitions, enforces business rules via the PredicateLogic Engine, and coordinates between different services through the API Gateway.

## 🏗️ **Architecture Goals**

### Core Responsibilities
1. **Workflow State Management**: Track and manage workflow lifecycle states
2. **State Transition Orchestration**: Ensure valid state transitions based on business rules
3. **Business Rule Integration**: Integrate with PredicateLogic Engine for validation
4. **Event-Driven Coordination**: Publish workflow events for other services
5. **Persistence Management**: Maintain workflow state in data layer
6. **Recovery & Resilience**: Handle failures and provide workflow recovery

### Service Boundaries
- **IN SCOPE**: Workflow orchestration, state management, transition validation
- **OUT OF SCOPE**: AI processing (client-side), direct data persistence (data service), business rules logic (predicate logic engine)

## 🔬 **TLA+ Specification Requirements**

The TLA+ specification must model and verify:

### Safety Properties
1. **State Consistency**: Workflows can only be in one valid state at a time
2. **Transition Validity**: All state transitions must be validated by business rules
3. **Concurrent Safety**: Multiple concurrent operations on the same workflow maintain consistency
4. **Data Integrity**: Workflow state changes are atomic and consistent

### Liveness Properties
1. **Progress Guarantee**: Valid workflow transitions eventually complete
2. **Recovery Completeness**: Failed workflows can be recovered to a consistent state
3. **Event Delivery**: Workflow events are eventually delivered to subscribers

### Critical Invariants
1. **Workflow Uniqueness**: Each workflow has a unique identifier and single active state
2. **Rule Compliance**: All transitions comply with PredicateLogic Engine validation
3. **State Persistence**: Workflow states are persistently stored before acknowledgment
4. **Event Ordering**: Workflow events maintain causal ordering

## 📋 **Functional Requirements**

### 1. Workflow Lifecycle Management
```yaml
Workflow States:
  - CREATED: Initial workflow creation
  - ACTIVE: Workflow is actively being processed
  - PAUSED: Workflow temporarily suspended
  - COMPLETED: Workflow successfully finished
  - FAILED: Workflow encountered unrecoverable error
  - CANCELLED: Workflow manually cancelled

Valid Transitions:
  - CREATED → ACTIVE
  - ACTIVE → PAUSED, COMPLETED, FAILED, CANCELLED
  - PAUSED → ACTIVE, CANCELLED
  - FAILED → ACTIVE (retry), CANCELLED
  - COMPLETED, CANCELLED → (terminal states)
```

### 2. State Transition Rules
- All transitions must be validated by PredicateLogic Engine
- Concurrent state changes must be handled with optimistic locking
- State changes must be atomic (succeed completely or rollback)
- Failed transitions must leave workflow in previous valid state

### 3. Event Management
- Publish workflow events for state changes
- Support event replay for audit and recovery
- Maintain event ordering guarantees
- Handle event delivery failures with retry logic

### 4. Integration Points
- **API Gateway**: Receive workflow commands and return status
- **PredicateLogic Engine**: Validate state transitions
- **Data Service**: Persist workflow state and retrieve workflow data
- **Notification Service**: Publish workflow events

## 🔧 **Technical Specifications**

### Data Models
```python
@dataclass
class WorkflowState:
    workflow_id: str
    current_state: WorkflowStateEnum
    previous_state: Optional[WorkflowStateEnum]
    created_at: datetime
    updated_at: datetime
    metadata: Dict[str, Any]
    version: int  # For optimistic locking

@dataclass
class StateTransitionRequest:
    workflow_id: str
    target_state: WorkflowStateEnum
    reason: str
    requested_by: str
    validation_context: Dict[str, Any]

@dataclass
class WorkflowEvent:
    event_id: str
    workflow_id: str
    event_type: WorkflowEventType
    from_state: Optional[WorkflowStateEnum]
    to_state: WorkflowStateEnum
    timestamp: datetime
    metadata: Dict[str, Any]
```

### Service Interface
```python
class WorkflowManagerService:
    async def create_workflow(self, workflow_data: WorkflowCreate) -> WorkflowState
    async def get_workflow_state(self, workflow_id: str) -> WorkflowState
    async def request_state_transition(self, request: StateTransitionRequest) -> TransitionResult
    async def list_workflows(self, filters: WorkflowFilters) -> List[WorkflowState]
    async def get_workflow_history(self, workflow_id: str) -> List[WorkflowEvent]
    async def recover_workflow(self, workflow_id: str) -> RecoveryResult
```

## 🧪 **Quality Requirements**

### Performance
- **State Transition Latency**: < 100ms for valid transitions
- **Concurrent Workflow Capacity**: Handle 1000+ concurrent workflows
- **Event Processing**: < 50ms event publication latency

### Reliability
- **Availability**: 99.9% uptime during business hours
- **Data Consistency**: Zero workflow state corruption
- **Recovery Time**: < 30 seconds for workflow recovery

### Security
- **Authorization**: All workflow operations require valid permissions
- **Audit Trail**: Complete audit log of all state changes
- **Data Protection**: Workflow metadata encryption at rest

## 📈 **Success Criteria**

### Phase 1: TLA+ Specification (Week 1)
- [ ] TLA+ specification models all workflow states and transitions
- [ ] Safety properties verified: state consistency, transition validity
- [ ] Liveness properties verified: progress guarantee, recovery completeness
- [ ] Concurrent operation safety validated
- [ ] TLC model checker validates all properties (>100K states explored)

### Phase 2: Property-Based Testing (Week 1-2)
- [ ] Hypothesis-based tests for all TLA+ properties
- [ ] Concurrent operation tests using threading
- [ ] State transition edge case validation
- [ ] Recovery scenario testing

### Phase 3: Implementation (Week 2)
- [ ] Core workflow state management
- [ ] State transition orchestration with PredicateLogic integration
- [ ] Event-driven architecture with reliable event delivery
- [ ] FastAPI REST endpoints with OpenAPI documentation
- [ ] Comprehensive error handling and recovery

### Phase 4: Integration Testing (Week 2)
- [ ] Integration with API Gateway service routing
- [ ] Integration with PredicateLogic Engine for validation
- [ ] Integration with Data Service for persistence
- [ ] End-to-end workflow scenario testing

## 🔄 **Implementation Phases**

### **Phase 1: TLA+ Specification (Days 1-3)**
1. **Day 1**: Create TLA+ specification modeling workflow states and transitions
2. **Day 2**: Add concurrent operation handling and safety properties
3. **Day 3**: Validate with TLC model checker and fix any issues

### **Phase 2: Property-Based Testing (Days 4-6)**
1. **Day 4**: Create test framework and basic state transition tests
2. **Day 5**: Add concurrent operation and recovery tests
3. **Day 6**: Validate all TLA+ properties with Hypothesis testing

### **Phase 3: Core Implementation (Days 7-10)**
1. **Day 7**: Implement core data models and state management
2. **Day 8**: Add state transition orchestration with PredicateLogic integration
3. **Day 9**: Implement event management and publication
4. **Day 10**: Add FastAPI endpoints and error handling

### **Phase 4: Integration & Demo (Days 11-14)**
1. **Day 11**: Integration testing with other ALIMS services
2. **Day 12**: End-to-end workflow scenario testing
3. **Day 13**: Create comprehensive demo showcasing TLA+ property enforcement
4. **Day 14**: Documentation and production readiness validation

## 🎮 **Demo Scenarios**

### Scenario 1: Basic Workflow Lifecycle
1. Create new LIMS workflow
2. Transition through valid states: CREATED → ACTIVE → COMPLETED
3. Verify state consistency and rule compliance

### Scenario 2: Concurrent Operations
1. Multiple simultaneous state transition requests
2. Verify only one succeeds while maintaining consistency
3. Demonstrate optimistic locking behavior

### Scenario 3: Business Rule Integration
1. Attempt invalid state transition
2. PredicateLogic Engine rejects transition
3. Workflow remains in previous valid state

### Scenario 4: Recovery Operations
1. Simulate workflow failure during state transition
2. Initiate workflow recovery
3. Verify workflow returns to consistent state

## 🎯 **Next Steps**

1. **Create TLA+ Specification**: Model workflow state management and transitions
2. **Validate with TLC**: Ensure all safety and liveness properties hold
3. **Human Review**: Validate TLA+ specification matches requirements
4. **Property-Based Testing**: Create comprehensive test suite
5. **Implementation**: Build production-ready Workflow Manager Service

This implementation plan provides a comprehensive roadmap for creating a robust, formally verified Workflow Manager Service that integrates seamlessly with the existing ALIMS architecture.
