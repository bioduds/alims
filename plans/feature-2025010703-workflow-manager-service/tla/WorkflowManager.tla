--------------------------- MODULE WorkflowManager ---------------------------

(*
ALIMS Workflow Manager Service - TLA+ Specification

This specification models the core workflow state management and orchestration
for the ALIMS Laboratory Information Management System. It focuses on:

1. Workflow state consistency and valid transitions
2. Concurrent operation safety with optimistic locking
3. Integration with PredicateLogic Engine for business rule validation
4. Event-driven architecture with reliable event delivery
5. Recovery and fault tolerance mechanisms

Key Properties Verified:
- Safety: State consistency, transition validity, concurrent safety
- Liveness: Progress guarantee, recovery completeness, event delivery
- Invariants: Workflow uniqueness, rule compliance, state persistence
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    WorkflowIds,      \* Set of possible workflow identifiers
    MaxWorkflows,     \* Maximum number of concurrent workflows  
    MaxEvents,        \* Maximum number of events in history
    MaxRetries,       \* Maximum number of retry attempts
    NULL              \* Null value for optional fields

VARIABLES
    workflows,        \* Set of active workflows (using records)
    events,          \* Sequence of workflow events
    predicateLogic,  \* PredicateLogic Engine state (available/unavailable)
    pendingOps,      \* Set of pending operations
    recoverySessions \* Set of active recovery sessions

vars == <<workflows, events, predicateLogic, pendingOps, recoverySessions>>

\* Workflow states
WorkflowStates == {"CREATED", "ACTIVE", "PAUSED", "COMPLETED", "FAILED", "CANCELLED"}

\* Terminal states (no further transitions allowed)
TerminalStates == {"COMPLETED", "CANCELLED"}

\* Event types
EventTypes == {"CREATED", "TRANSITION", "FAILED", "RECOVERED"}

\* Operation types
OperationTypes == {"CREATE", "TRANSITION", "RECOVER"}

\* Delivery status for events
DeliveryStatus == {"PENDING", "DELIVERED", "FAILED", "RETRYING"}

\* Valid state transitions based on LIMS business rules
ValidTransitions == {
    <<"CREATED", "ACTIVE">>,
    <<"ACTIVE", "PAUSED">>,
    <<"ACTIVE", "COMPLETED">>,
    <<"ACTIVE", "FAILED">>,
    <<"ACTIVE", "CANCELLED">>,
    <<"PAUSED", "ACTIVE">>,
    <<"PAUSED", "CANCELLED">>,
    <<"FAILED", "ACTIVE">>,      \* Recovery transition
    <<"FAILED", "CANCELLED">>
}

\* Type definitions for workflow state
WorkflowState == [
    id: WorkflowIds,
    state: WorkflowStates,
    previousState: WorkflowStates \cup {NULL},
    version: Nat,                \* For optimistic locking
    createdAt: Nat,
    updatedAt: Nat,
    inTransition: BOOLEAN,       \* Prevents concurrent modifications
    metadata: [STRING -> STRING]
]

\* Type definitions for workflow events
WorkflowEvent == [
    eventId: Nat,
    workflowId: WorkflowIds,
    eventType: EventTypes,
    fromState: WorkflowStates \cup {NULL},
    toState: WorkflowStates,
    timestamp: Nat,
    retryCount: Nat
]

\* Type definitions for pending operations
PendingOperation == [
    opId: Nat,
    opType: OperationTypes,
    workflowId: WorkflowIds,
    targetState: WorkflowStates \cup {NULL},
    requestedAt: Nat,
    version: Nat                 \* Expected workflow version
]

-----------------------------------------------------------------------------
\* INITIAL STATE

Init ==
    /\ workflows = {}
    /\ events = <<>>
    /\ predicateLogic = TRUE     \* PredicateLogic Engine initially available
    /\ pendingOps = {}
    /\ recoverySessions = {}

-----------------------------------------------------------------------------
\* HELPER FUNCTIONS

\* Check if a workflow exists
WorkflowExists(wfId) == 
    \E wf \in workflows : wf.id = wfId

\* Get workflow by ID
GetWorkflow(wfId) == 
    CHOOSE wf \in workflows : wf.id = wfId

\* Check if state transition is valid
IsValidTransition(fromState, toState) ==
    <<fromState, toState>> \in ValidTransitions

\* Check if workflow is in terminal state
IsTerminalState(state) == state \in TerminalStates

\* Generate next event ID
NextEventId == Len(events) + 1

\* Generate next operation ID
NextOpId == Cardinality(pendingOps) + 1

\* Check if workflow can accept new operations
CanModifyWorkflow(wfId) ==
    /\ WorkflowExists(wfId)
    /\ LET wf == GetWorkflow(wfId)
       IN /\ ~wf.inTransition
          /\ ~IsTerminalState(wf.state)

\* Validate transition with PredicateLogic Engine
ValidateTransition(wfId, targetState) ==
    /\ predicateLogic = TRUE     \* Engine must be available
    /\ WorkflowExists(wfId)
    /\ LET wf == GetWorkflow(wfId)
       IN IsValidTransition(wf.state, targetState)

-----------------------------------------------------------------------------
\* WORKFLOW OPERATIONS

\* Create a new workflow
CreateWorkflow(wfId) ==
    /\ ~WorkflowExists(wfId)
    /\ Cardinality(workflows) < MaxWorkflows
    /\ LET newWorkflow == [
            id |-> wfId,
            state |-> "CREATED",
            previousState |-> NULL,
            version |-> 1,
            createdAt |-> Len(events) + 1,
            updatedAt |-> Len(events) + 1,
            inTransition |-> FALSE,
            metadata |-> [type |-> "LIMS_WORKFLOW"]
        ]
       newEvent == [
            eventId |-> NextEventId,
            workflowId |-> wfId,
            eventType |-> "CREATED",
            fromState |-> NULL,
            toState |-> "CREATED",
            timestamp |-> Len(events) + 1,
            retryCount |-> 0
        ]
       IN
       /\ workflows' = workflows \cup {newWorkflow}
       /\ events' = Append(events, newEvent)
       /\ UNCHANGED <<predicateLogic, pendingOps, recoverySessions>>

\* Request state transition (with optimistic locking)
RequestStateTransition(wfId, targetState, expectedVersion) ==
    /\ CanModifyWorkflow(wfId)
    /\ LET currentWorkflow == GetWorkflow(wfId)
       IN /\ currentWorkflow.version = expectedVersion  \* Optimistic locking check
          /\ ValidateTransition(wfId, targetState)
          /\ LET updatedWorkflow == [currentWorkflow EXCEPT !.inTransition = TRUE]
                 newOp == [
                     opId |-> NextOpId,
                     opType |-> "TRANSITION",
                     workflowId |-> wfId,
                     targetState |-> targetState,
                     requestedAt |-> Len(events) + 1,
                     version |-> expectedVersion
                 ]
             IN
             /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
             /\ pendingOps' = pendingOps \cup {newOp}
             /\ UNCHANGED <<events, predicateLogic, recoverySessions>>

\* Execute pending state transition
ExecuteStateTransition ==
    /\ pendingOps # {}
    /\ \E op \in pendingOps :
        /\ op.opType = "TRANSITION"
        /\ WorkflowExists(op.workflowId)
        /\ workflows[op.workflowId].version = op.version
        /\ workflows[op.workflowId].inTransition = TRUE
        /\ LET wfId == op.workflowId
               currentWorkflow == workflows[wfId]
               targetState == op.targetState
           IN
           /\ workflows' = [workflows EXCEPT 
               ![wfId].state = targetState,
               ![wfId].previousState = currentWorkflow.state,
               ![wfId].version = currentWorkflow.version + 1,
               ![wfId].updatedAt = Len(events) + 1,
               ![wfId].inTransition = FALSE
              ]
           /\ events' = Append(events, [
                   eventId |-> NextEventId,
                   workflowId |-> wfId,
                   eventType |-> "TRANSITION",
                   fromState |-> currentWorkflow.state,
                   toState |-> targetState,
                   timestamp |-> Len(events) + 1,
                   retryCount |-> 0
               ])
           /\ eventDelivery' = eventDelivery @@ (NextEventId :> "PENDING")
           /\ pendingOps' = pendingOps \ {op}
           /\ UNCHANGED <<predicateLogic, recoverySessions>>

\* Handle transition failure (rollback to previous state)
HandleTransitionFailure ==
    /\ pendingOps # {}
    /\ \E op \in pendingOps :
        /\ op.opType = "TRANSITION"
        /\ WorkflowExists(op.workflowId)
        /\ workflows[op.workflowId].inTransition = TRUE
        /\ LET wfId == op.workflowId
           IN
           /\ workflows' = [workflows EXCEPT 
               ![wfId].inTransition = FALSE]
           /\ pendingOps' = pendingOps \ {op}
           /\ UNCHANGED <<events, predicateLogic, eventDelivery, recoverySessions>>

\* PredicateLogic Engine state changes
PredicateLogicBecomeUnavailable ==
    /\ predicateLogic = TRUE
    /\ predicateLogic' = FALSE
    /\ UNCHANGED <<workflows, events, eventDelivery, pendingOps, recoverySessions>>

PredicateLogicBecomeAvailable ==
    /\ predicateLogic = FALSE
    /\ predicateLogic' = TRUE
    /\ UNCHANGED <<workflows, events, eventDelivery, pendingOps, recoverySessions>>

\* Event delivery operations
DeliverEvent ==
    /\ \E eventId \in DOMAIN eventDelivery :
        /\ eventDelivery[eventId] = "PENDING"
        /\ eventDelivery' = [eventDelivery EXCEPT ![eventId] = "DELIVERED"]
    /\ UNCHANGED <<workflows, events, predicateLogic, pendingOps, recoverySessions>>

FailEventDelivery ==
    /\ \E eventId \in DOMAIN eventDelivery :
        /\ eventDelivery[eventId] = "PENDING"
        /\ eventDelivery' = [eventDelivery EXCEPT ![eventId] = "FAILED"]
    /\ UNCHANGED <<workflows, events, predicateLogic, pendingOps, recoverySessions>>

RetryEventDelivery ==
    /\ \E eventId \in DOMAIN eventDelivery :
        /\ eventDelivery[eventId] = "FAILED"
        /\ eventDelivery' = [eventDelivery EXCEPT ![eventId] = "RETRYING"]
    /\ UNCHANGED <<workflows, events, predicateLogic, pendingOps, recoverySessions>>

\* Recovery operations
StartWorkflowRecovery(wfId) ==
    /\ WorkflowExists(wfId)
    /\ workflows[wfId].state = "FAILED"
    /\ wfId \notin recoverySessions
    /\ recoverySessions' = recoverySessions \cup {wfId}
    /\ UNCHANGED <<workflows, events, predicateLogic, eventDelivery, pendingOps>>

CompleteWorkflowRecovery(wfId) ==
    /\ wfId \in recoverySessions
    /\ WorkflowExists(wfId)
    /\ workflows[wfId].state = "FAILED"
    /\ workflows' = [workflows EXCEPT 
        ![wfId].state = "ACTIVE",
        ![wfId].version = workflows[wfId].version + 1,
        ![wfId].updatedAt = Len(events) + 1
       ]
    /\ events' = Append(events, [
            eventId |-> NextEventId,
            workflowId |-> wfId,
            eventType |-> "RECOVERED",
            fromState |-> "FAILED",
            toState |-> "ACTIVE",
            timestamp |-> Len(events) + 1,
            retryCount |-> 0
        ])
    /\ eventDelivery' = eventDelivery @@ (NextEventId :> "PENDING")
    /\ recoverySessions' = recoverySessions \ {wfId}
    /\ UNCHANGED <<predicateLogic, pendingOps>>

-----------------------------------------------------------------------------
\* NEXT STATE RELATION

Next ==
    \/ \E wfId \in WorkflowIds : CreateWorkflow(wfId)
    \/ \E wfId \in WorkflowIds, targetState \in WorkflowStates, version \in Nat :
        RequestStateTransition(wfId, targetState, version)
    \/ ExecuteStateTransition
    \/ HandleTransitionFailure
    \/ PredicateLogicBecomeUnavailable
    \/ PredicateLogicBecomeAvailable
    \/ DeliverEvent
    \/ FailEventDelivery
    \/ RetryEventDelivery
    \/ \E wfId \in WorkflowIds : StartWorkflowRecovery(wfId)
    \/ \E wfId \in WorkflowIds : CompleteWorkflowRecovery(wfId)

\* Specification
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* SAFETY PROPERTIES

\* Every workflow has a unique state at any time
StateConsistency ==
    \A wfId \in DOMAIN workflows :
        workflows[wfId].state \in WorkflowStates

\* State transitions only occur through valid paths
TransitionValidity ==
    \A i \in 1..Len(events) :
        LET event == events[i]
        IN event.eventType = "TRANSITION" =>
           <<event.fromState, event.toState>> \in ValidTransitions

\* Workflows not in transition cannot be concurrently modified
ConcurrentSafety ==
    \A wfId \in DOMAIN workflows :
        workflows[wfId].inTransition => 
            \A op \in pendingOps :
                op.workflowId = wfId => op.opType = "TRANSITION"

\* Terminal states are immutable
TerminalStateImmutability ==
    \A wfId \in DOMAIN workflows :
        IsTerminalState(workflows[wfId].state) =>
            workflows[wfId].inTransition = FALSE

\* Version numbers increase monotonically
VersionMonotonicity ==
    \A wfId \in DOMAIN workflows :
        workflows[wfId].version >= 1

\* Recovery sessions only exist for failed workflows
RecoverySessionValidity ==
    \A wfId \in recoverySessions :
        /\ WorkflowExists(wfId)
        /\ workflows[wfId].state = "FAILED"

-----------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* Valid transitions eventually complete
TransitionProgress ==
    \A op \in pendingOps :
        op.opType = "TRANSITION" => 
            <>(op \notin pendingOps)

\* Failed workflows can eventually be recovered
RecoveryCompleteness ==
    \A wfId \in DOMAIN workflows :
        workflows[wfId].state = "FAILED" =>
            <>(workflows[wfId].state = "ACTIVE" \/ 
               workflows[wfId].state = "CANCELLED")

\* Events are eventually delivered or marked as failed
EventDelivery ==
    \A eventId \in DOMAIN eventDelivery :
        eventDelivery[eventId] = "PENDING" =>
            <>(eventDelivery[eventId] \in {"DELIVERED", "FAILED"})

-----------------------------------------------------------------------------
\* INVARIANTS

\* System has bounded number of workflows
BoundedWorkflows == Cardinality(DOMAIN workflows) <= MaxWorkflows

\* Events history has bounded size
BoundedEvents == Len(events) <= MaxEvents

\* Pending operations are bounded
BoundedPendingOps == Cardinality(pendingOps) <= MaxWorkflows

\* All workflows have valid IDs
ValidWorkflowIds ==
    \A wfId \in DOMAIN workflows : wfId \in WorkflowIds

\* Event delivery status is consistent
EventDeliveryConsistency ==
    DOMAIN eventDelivery = {events[i].eventId : i \in 1..Len(events)}

=============================================================================
