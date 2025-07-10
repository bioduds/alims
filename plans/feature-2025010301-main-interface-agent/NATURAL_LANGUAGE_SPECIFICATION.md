# Main Interface Agent System - Natural Language Specification

## Executive Summary

This document translates the formal TLA+ model into natural language to describe the **Main Interface Agent System** for ALIMS (Adaptive Laboratory Information Management System). The system integrates Prolog-style logical reasoning with agent-based conversation management to provide intelligent laboratory workflow orchestration.

## System Architecture Overview

### Core Components

1. **Central Brain** - The main orchestrator that coordinates all system activities
2. **Agent Dispatcher** - Routes conversations to appropriate agents based on capabilities  
3. **Prolog Reasoning Engine** - Performs logical inference using facts and rules
4. **Conversation Manager** - Handles user interactions and maintains conversation state
5. **Resource Monitor** - Tracks system resources and performance metrics

### Key Entities

- **Conversations**: User interactions with the system (max 2 concurrent)
- **Agents**: Specialized workers with specific capabilities (max 3 agents)
- **Queries**: Logical reasoning requests processed by Prolog engine
- **Knowledge Base**: Facts and rules used for logical inference
- **Dead Letter Queue**: Failed operations that need retry or manual intervention

## System Configuration

Based on the current configuration (`ProductionReadyAgent.cfg`):

- **Maximum Conversations**: 2 concurrent user sessions
- **Maximum Agents**: 3 specialized agents
- **Query Depth Limit**: 3 levels to prevent infinite recursion  
- **Knowledge Base Size**: Up to 10 entries
- **Timeout Threshold**: 5 time units for operations
- **Retry Limit**: 2 attempts before marking as failed

### Agent Capabilities

1. **Sample Analysis Agent** - Handles laboratory sample processing
2. **Workflow Control Agent** - Manages laboratory workflows  
3. **Logical Reasoning Agent** - Performs complex inference tasks

### Prolog Predicates

- `has_capability(Agent, Capability)` - Facts about agent abilities
- `suitable_agent(Agent, Task)` - Rules for agent-task matching
- `requires_capability(Task, Capability)` - Task requirements

## System States and Lifecycle

### Central Brain States

1. **INITIALIZING** - System startup, setting up agents
2. **READY** - Normal operation, accepting new conversations
3. **ORCHESTRATING** - Managing active conversations  
4. **PROLOG_INFERENCE** - Processing logical reasoning queries
5. **ERROR_RECOVERY** - Handling system errors

### Conversation Lifecycle

1. **ACTIVE** - Conversation started, waiting for agent assignment
2. **PROCESSING** - Agent assigned and working on conversation
3. **LOGICAL_REASONING** - Prolog inference in progress
4. **COMPLETED** - Conversation successfully finished
5. **ERROR** - Conversation failed due to error
6. **TIMEOUT** - Conversation timed out

### Agent States

1. **IDLE** - Available for new conversations
2. **BUSY** - Currently handling a conversation
3. **REASONING** - Performing logical inference
4. **ERROR** - Agent encountered an error

## System Operations

### 1. System Initialization

**What happens**: System starts up and creates the initial agent pool

**Process**:
- Central brain transitions from INITIALIZING to READY
- Creates 3 agents with different capabilities:
  - Agent 1: Sample analysis specialist
  - Agent 2: Workflow control specialist  
  - Agent 3: Logical reasoning specialist
- Initializes knowledge base with basic facts and rules
- Sets up monitoring and audit systems

**Preconditions**: System in INITIALIZING state
**Postconditions**: System READY with 3 idle agents available

### 2. Starting a Conversation

**What happens**: User begins interaction with the system

**Process**:
- System accepts new conversation if under the limit (max 2)
- Creates conversation record with unique ID and timeout deadline
- Marks conversation as ACTIVE
- Dispatcher enters ROUTING mode to find suitable agent
- Updates system metrics and audit trail

**Preconditions**: 
- System in READY state
- Less than maximum conversations active
- Dispatcher not busy

**Postconditions**: New conversation in ACTIVE state, dispatcher in ROUTING mode

### 3. Agent Assignment

**What happens**: Dispatcher assigns an available agent to handle conversation

**Process**:
- Dispatcher finds an IDLE agent with appropriate capabilities
- Updates conversation to link to assigned agent
- Updates agent to link to assigned conversation  
- Agent state changes from IDLE to BUSY
- Dispatcher returns to IDLE state

**Preconditions**:
- Dispatcher in ROUTING mode
- Conversation exists and needs agent
- Agent available and capable

**Postconditions**: Conversation-agent linkage established, both entities updated

### 4. Prolog Query Processing

**What happens**: System performs logical reasoning to answer questions or make decisions

**Process**:
1. **Query Initiation**:
   - Creates query with predicate (e.g., \"suitable_agent\") and arguments
   - Links query to conversation requesting it
   - Marks query as PENDING
   - Central brain enters PROLOG_INFERENCE mode

2. **Inference Processing**:
   - Searches knowledge base for matching facts
   - If match found: marks query SUCCESS, creates inference chain
   - If no match: marks query FAILED, adds to dead letter queue
   - Updates system clock and metrics

3. **Query Completion**:
   - Conversation returns to ACTIVE state
   - Completed queries are garbage collected
   - Central brain returns to READY state

**Example Query Flow**:
```
Query: suitable_agent(?Agent, \"sample_analysis_task\")
1. Search for: requires_capability(\"sample_analysis_task\", ?Cap)
2. Search for: has_capability(?Agent, ?Cap)  
3. If both found: return Agent as suitable
4. Create inference chain showing reasoning path
```

### 5. Timeout and Error Handling

**What happens**: System handles stuck or failed operations

**Timeout Process**:
- Monitor queries that exceed timeout threshold (5 time units)
- Mark timed-out queries as TIMEOUT status
- Move to dead letter queue for later retry
- Update error metrics and logs
- Release system resources

**Error Recovery**:
- Log all errors with timestamps for debugging
- Increment retry counters up to maximum (2 retries)
- Move permanently failed items to dead letter queue
- Maintain system stability and prevent cascading failures

### 6. Knowledge Base Management

**What happens**: System learns new facts and rules dynamically

**Process**:
- Validate new knowledge entries for correct format
- Ensure unique IDs to prevent duplicates
- Add to knowledge base if space available (max 10 entries)
- Update audit trail with knowledge additions

**Knowledge Types**:
- **Facts**: Direct statements like `has_capability(sample_tracker, sample_analysis)`
- **Rules**: Logical implications like `suitable_agent(X,Y) :- requires_capability(Y,Z), has_capability(X,Z)`

## System Invariants (What Must Always Be True)

### Type Safety
- All conversations have valid IDs and states
- All agents have valid capabilities and assignments
- All queries link to existing conversations
- Knowledge base entries are well-formed

### Unique Identity
- No two conversations can have the same ID
- No two agents can have the same ID  
- No two queries can have the same ID
- Knowledge base entries have unique IDs

### Resource Constraints
- Never exceed maximum conversations (2)
- Never exceed maximum agents (3)
- Never exceed maximum queries (6 = 2 conversations × 3 depth)
- Knowledge base stays within size limit (10 entries)

### Business Logic Consistency
- If conversation assigned to agent, agent must be linked back to conversation
- All queries must belong to existing conversations
- Timeout deadlines must be after start times
- Agent capabilities must match their assigned tasks

## System Properties (What Will Eventually Happen)

### Liveness Guarantees
- System will complete initialization and become READY
- Pending queries will eventually complete (SUCCESS, FAILED, or TIMEOUT)
- Conversations in LOGICAL_REASONING will eventually progress
- Dead letter queue will eventually drain through retries
- System will not get stuck in PROLOG_INFERENCE mode indefinitely

### Fairness Guarantees
- All pending queries get fair chance to be processed
- All conversations get fair access to agents
- System clock advances to ensure timeouts are detected
- Critical operations (timeouts, completions) are prioritized

## Example Scenario Walkthrough

### Scenario: Lab Sample Analysis Request

1. **User Request**: \"I need to analyze a blood sample\"

2. **System Response**:
   - Creates Conversation #1 (ACTIVE state)
   - Dispatcher routes to find suitable agent
   - Assigns Sample Analysis Agent (Agent #1)
   - Agent becomes BUSY, conversation links to agent

3. **Logical Reasoning**:
   - System queries: `suitable_agent(?Agent, blood_sample_analysis)`
   - Prolog engine searches knowledge base:
     - Finds: `requires_capability(blood_sample_analysis, sample_analysis)`
     - Finds: `has_capability(sample_tracker, sample_analysis)`
   - Concludes: sample_tracker agent is suitable
   - Creates inference chain documenting the reasoning

4. **Task Execution**:
   - Agent processes the sample analysis request
   - Updates conversation state to PROCESSING
   - Completes analysis and marks conversation COMPLETED
   - Agent returns to IDLE state for next assignment

5. **Cleanup**:
   - System garbage collects completed queries
   - Updates metrics and audit trail
   - Returns to READY state for next conversation

## Error Scenarios

### Timeout Example
- Query takes longer than 5 time units
- System marks query as TIMEOUT
- Moves to dead letter queue for retry
- If retries exhausted, marks as permanently failed
- System continues operating normally

### Resource Exhaustion
- If 2 conversations already active, new requests wait
- If all agents busy, conversations wait for assignment
- Knowledge base full: new additions rejected until space available
- System maintains stability under resource pressure

## Monitoring and Observability

### System Metrics
- **conversation_count**: Number of active conversations
- **queries**: Total queries processed
- **errors**: Error count for health monitoring
- **timeouts**: Timeout incidents for performance tuning

### Audit Trail
- Every major action logged with timestamp
- Full traceability of system decisions
- Support for debugging and compliance
- Evidence trail for logical reasoning paths

### Error Logging
- All failures captured with context
- Timeout incidents tracked
- Query failures diagnosed
- System health monitoring enabled

## Validation Questions for Human Review

1. **Capability Matching**: Does the agent assignment logic correctly match agent capabilities to task requirements?

2. **Timeout Handling**: Is the 5-time-unit timeout threshold appropriate for your laboratory workflows?

3. **Concurrent Limits**: Are 2 concurrent conversations and 3 agents sufficient for expected load?

4. **Knowledge Base**: Does the initial knowledge base contain the right facts and rules for your domain?

5. **Error Recovery**: Is the retry logic (max 2 retries) appropriate for your reliability requirements?

6. **Resource Management**: Are the resource limits (conversations, queries, knowledge) sized correctly?

7. **Audit Requirements**: Does the audit trail capture sufficient information for your compliance needs?

8. **Prolog Integration**: Do the logical reasoning patterns match how you want the system to make decisions?

This natural language specification captures the complete formal behavior defined in the TLA+ model while remaining accessible for human validation and understanding.
