# ALIMS PydanticAI + LangGraph Implementation Plan

## 🎯 Vision: Agentic Laboratory Information Management System

Transform ALIMS into a formally verified, AI-orchestrated LIMS where PydanticAI agents manage laboratory workflows through LangGraph state machines.

## 🔬 Architecture Overview

### **Core Philosophy**
- **Formal Verification First**: All workflows must be TLA+ specified and TLC validated
- **Agent-Driven**: PydanticAI agents handle intelligent decision-making
- **Workflow Orchestration**: LangGraph manages state transitions and dependencies
- **Type Safety**: Pydantic models ensure data integrity throughout

### **Technology Stack**
```
┌─────────────────────────────────────────────────┐
│                   ALIMS UI                      │
│              (React + TypeScript)               │
├─────────────────────────────────────────────────┤
│                LangGraph Layer                  │
│           (Workflow Orchestration)              │
├─────────────────────────────────────────────────┤
│              PydanticAI Agents                  │
│         (Intelligent Process Automation)        │
├─────────────────────────────────────────────────┤
│               Core LIMS Services                │
│            (FastAPI + SQLModel)                 │
├─────────────────────────────────────────────────┤
│              Data & Integration                 │
│         (PostgreSQL + Redis + Kafka)            │
└─────────────────────────────────────────────────┘
```

## 📋 Implementation Phases

### **Phase 1: TLA+ Specification & Validation**
**Duration**: 2-3 weeks

#### Deliverables:
1. **Core Workflow Specification**
   - `plans/feature-1-core-lims-workflow/tla/SampleLifecycle.tla`
   - Sample states: Received → Accessioned → Testing → QC → Reported
   - Invariants: Chain of custody, data integrity, audit compliance

2. **Agent Interaction Protocol**
   - `plans/feature-2-agent-protocols/tla/AgentCoordination.tla`
   - Message passing between agents
   - Concurrency control and resource management

3. **Quality Control Workflow**
   - `plans/feature-3-qc-workflow/tla/QualityControl.tla`
   - Automated QC decision trees
   - Exception handling and escalation

#### TLA+ Properties to Verify:
- **Safety**: No sample data corruption
- **Liveness**: Every sample eventually gets processed
- **Compliance**: Full audit trail maintained
- **Resource**: No instrument double-booking

### **Phase 2: Core LIMS Domain Models**
**Duration**: 1-2 weeks

#### Pydantic Models:
```python
# backend/app/lims/models.py
class Sample(BaseModel):
    id: SampleID
    barcode: str
    received_at: datetime
    status: SampleStatus
    tests_ordered: List[TestCode]
    chain_of_custody: List[CustodyEvent]

class TestResult(BaseModel):
    sample_id: SampleID
    test_code: TestCode
    value: Decimal
    units: str
    measured_at: datetime
    instrument_id: InstrumentID
    qc_flags: List[QCFlag]

class WorkflowState(BaseModel):
    sample_id: SampleID
    current_step: WorkflowStep
    next_actions: List[Action]
    assigned_agents: List[AgentID]
```

### **Phase 3: PydanticAI Agent Development**
**Duration**: 3-4 weeks

#### Core Agents:

1. **Sample Management Agent**
   ```python
   class SampleAgent(Agent):
       """Handles sample reception, accessioning, and tracking"""
       
       @tool
       def accession_sample(self, sample_data: SampleData) -> Sample:
           """Generate barcode, create DB record, print labels"""
       
       @tool  
       def track_custody_chain(self, sample_id: SampleID) -> CustodyChain:
           """Maintain complete audit trail"""
   ```

2. **Quality Control Agent**
   ```python
   class QCAgent(Agent):
       """AI-powered quality control and result validation"""
       
       @tool
       def validate_result(self, result: TestResult) -> QCDecision:
           """Check delta limits, trends, reference ranges"""
       
       @tool
       def flag_anomalies(self, results: List[TestResult]) -> List[QCFlag]:
           """Detect statistical outliers and patterns"""
   ```

3. **Workflow Orchestration Agent**
   ```python
   class WorkflowAgent(Agent):
       """Manages sample progression through laboratory processes"""
       
       @tool
       def determine_next_step(self, workflow_state: WorkflowState) -> NextAction:
           """AI-driven workflow routing"""
       
       @tool
       def schedule_instruments(self, tests: List[Test]) -> Schedule:
           """Optimize instrument utilization"""
   ```

### **Phase 4: LangGraph Workflow Integration**
**Duration**: 2-3 weeks

#### Core Workflows:

1. **Sample Processing Graph**
   ```python
   from langgraph import StateGraph, Node, Router
   
   sample_workflow = StateGraph(SampleState)
   
   @Node
   def receive_sample(state: SampleState) -> SampleState:
       return sample_agent.accession_sample(state.sample_data)
   
   @Router  
   def route_tests(state: SampleState) -> str:
       return workflow_agent.determine_next_step(state.workflow)
   
   @Node
   def perform_testing(state: SampleState) -> SampleState:
       # Instrument integration and result capture
       
   @Node
   def quality_control(state: SampleState) -> SampleState:
       return qc_agent.validate_result(state.results)
   ```

2. **Quality Control Decision Tree**
   ```python
   qc_workflow = StateGraph(QCState)
   
   @Router
   def qc_decision(state: QCState) -> str:
       if qc_agent.needs_review(state.result):
           return "manual_review"
       elif qc_agent.needs_rerun(state.result):
           return "schedule_rerun"
       else:
           return "approve_result"
   ```

### **Phase 5: Integration & Testing**
**Duration**: 2-3 weeks

#### Components:
1. **Instrument Integration**: Bidirectional communication with lab instruments
2. **API Layer**: RESTful APIs for external systems
3. **Event Streaming**: Kafka for real-time workflow events
4. **Monitoring**: OpenTelemetry for observability

## 🛠️ Development Workflow

### **TLA+ First Approach**
1. Create feature branch: `feature/1/core-lims-workflow`
2. Write TLA+ specification in `plans/feature-1-core-lims-workflow/`
3. Validate with TLC model checker
4. Get human approval on natural language description
5. Write comprehensive tests
6. Implement code following TLA+ specification
7. Validate implementation against tests

### **File Structure**
```
backend/app/
├── lims/
│   ├── agents/          # PydanticAI agents
│   │   ├── sample_agent.py
│   │   ├── qc_agent.py
│   │   └── workflow_agent.py
│   ├── workflows/       # LangGraph workflows
│   │   ├── sample_processing.py
│   │   ├── quality_control.py
│   │   └── instrument_integration.py
│   ├── models/          # Pydantic domain models
│   │   ├── sample.py
│   │   ├── test_result.py
│   │   └── workflow.py
│   └── services/        # Core LIMS services
│       ├── sample_service.py
│       ├── instrument_service.py
│       └── qc_service.py
```

## 🎯 Success Criteria

### **Technical**
- [ ] All workflows formally verified with TLA+
- [ ] 100% type coverage with Pydantic models
- [ ] AI agents demonstrate intelligent decision-making
- [ ] LangGraph workflows handle complex state transitions
- [ ] Full audit trail for compliance

### **Business**
- [ ] Reduced manual intervention in routine processes
- [ ] Faster sample turnaround times
- [ ] Improved quality control accuracy
- [ ] Enhanced regulatory compliance
- [ ] Scalable architecture for laboratory growth

## 🚀 Next Actions

1. **Create TLA+ specifications** for core workflows
2. **Set up development environment** with PydanticAI and LangGraph
3. **Define Pydantic models** for laboratory domain
4. **Implement first PydanticAI agent** (Sample Management)
5. **Create basic LangGraph workflow** for sample processing

This approach transforms ALIMS into a cutting-edge, formally verified, AI-driven LIMS that sets new standards for laboratory automation and compliance.
