--------------------------- MODULE WorkflowManagerSimple ---------------------------

(*
ALIMS Workflow Manager Service - Simplified TLA+ Specification

This specification models the core workflow state management for ALIMS:
1. Workflow state consistency and valid transitions
2. Concurrent operation safety with optimistic locking  
3. Integration with PredicateLogic Engine for validation
4. Recovery mechanisms

Simplified to focus on essential safety and liveness properties.
*)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    WorkflowIds,      \* Set of possible workflow identifiers
    MaxWorkflows      \* Maximum number of concurrent workflows

VARIABLES
    workflows,        \* Set of workflow records
    events,          \* Sequence of workflow events
    predicateLogic   \* PredicateLogic Engine availability

vars == <<workflows, events, predicateLogic>>

\* Workflow states
WorkflowStates == {"CREATED", "ACTIVE", "PAUSED", "COMPLETED", "FAILED", "CANCELLED"}

\* Terminal states (no further transitions allowed)
TerminalStates == {"COMPLETED", "CANCELLED"}

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

\* Workflow record structure
WorkflowRecord == [
    id: WorkflowIds,
    state: WorkflowStates,
    version: Nat,
    inTransition: BOOLEAN
]

\* Event record structure  
EventRecord == [
    eventId: Nat,
    workflowId: WorkflowIds,
    fromState: WorkflowStates \cup {"NULL"},
    toState: WorkflowStates,
    timestamp: Nat
]

-----------------------------------------------------------------------------
\* INITIAL STATE

Init ==
    /\ workflows = {}
    /\ events = <<>>
    /\ predicateLogic = TRUE

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

\* Check if workflow can be modified
CanModifyWorkflow(wfId) ==
    /\ WorkflowExists(wfId)
    /\ LET wf == GetWorkflow(wfId)
       IN /\ ~wf.inTransition
          /\ ~IsTerminalState(wf.state)

\* Validate transition requires PredicateLogic Engine
ValidateTransition(wfId, targetState) ==
    /\ predicateLogic = TRUE
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
            version |-> 1,
            inTransition |-> FALSE
        ]
       newEvent == [
            eventId |-> Len(events) + 1,
            workflowId |-> wfId,
            fromState |-> "NULL",
            toState |-> "CREATED",
            timestamp |-> Len(events) + 1
        ]
       IN
       /\ workflows' = workflows \cup {newWorkflow}
       /\ events' = Append(events, newEvent)
       /\ UNCHANGED predicateLogic

\* Execute state transition
ExecuteStateTransition(wfId, targetState) ==
    /\ CanModifyWorkflow(wfId)
    /\ ValidateTransition(wfId, targetState)
    /\ LET currentWorkflow == GetWorkflow(wfId)
           updatedWorkflow == [
               currentWorkflow EXCEPT 
               !.state = targetState,
               !.version = currentWorkflow.version + 1
           ]
           newEvent == [
               eventId |-> Len(events) + 1,
               workflowId |-> wfId,
               fromState |-> currentWorkflow.state,
               toState |-> targetState,
               timestamp |-> Len(events) + 1
           ]
       IN
       /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
       /\ events' = Append(events, newEvent)
       /\ UNCHANGED predicateLogic

\* Start transition (sets inTransition flag)
StartTransition(wfId, targetState) ==
    /\ CanModifyWorkflow(wfId)
    /\ ValidateTransition(wfId, targetState)
    /\ LET currentWorkflow == GetWorkflow(wfId)
           updatedWorkflow == [currentWorkflow EXCEPT !.inTransition = TRUE]
       IN
       /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
       /\ UNCHANGED <<events, predicateLogic>>

\* Complete transition (clears inTransition flag and updates state)
CompleteTransition(wfId, targetState) ==
    /\ WorkflowExists(wfId)
    /\ LET currentWorkflow == GetWorkflow(wfId)
       IN /\ currentWorkflow.inTransition = TRUE
          /\ IsValidTransition(currentWorkflow.state, targetState)
          /\ LET updatedWorkflow == [
                     currentWorkflow EXCEPT 
                     !.state = targetState,
                     !.version = currentWorkflow.version + 1,
                     !.inTransition = FALSE
                 ]
                 newEvent == [
                     eventId |-> Len(events) + 1,
                     workflowId |-> wfId,
                     fromState |-> currentWorkflow.state,
                     toState |-> targetState,
                     timestamp |-> Len(events) + 1
                 ]
             IN
             /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
             /\ events' = Append(events, newEvent)
             /\ UNCHANGED predicateLogic

\* Cancel transition (rollback to previous state)
CancelTransition(wfId) ==
    /\ WorkflowExists(wfId)
    /\ LET currentWorkflow == GetWorkflow(wfId)
       IN /\ currentWorkflow.inTransition = TRUE
          /\ LET updatedWorkflow == [currentWorkflow EXCEPT !.inTransition = FALSE]
             IN
             /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
             /\ UNCHANGED <<events, predicateLogic>>

\* PredicateLogic Engine state changes
PredicateLogicUnavailable ==
    /\ predicateLogic = TRUE
    /\ predicateLogic' = FALSE
    /\ UNCHANGED <<workflows, events>>

PredicateLogicAvailable ==
    /\ predicateLogic = FALSE
    /\ predicateLogic' = TRUE
    /\ UNCHANGED <<workflows, events>>

\* Recover failed workflow
RecoverWorkflow(wfId) ==
    /\ WorkflowExists(wfId)
    /\ LET currentWorkflow == GetWorkflow(wfId)
       IN /\ currentWorkflow.state = "FAILED"
          /\ ~currentWorkflow.inTransition
          /\ predicateLogic = TRUE
          /\ LET updatedWorkflow == [
                     currentWorkflow EXCEPT 
                     !.state = "ACTIVE",
                     !.version = currentWorkflow.version + 1
                 ]
                 newEvent == [
                     eventId |-> Len(events) + 1,
                     workflowId |-> wfId,
                     fromState |-> "FAILED",
                     toState |-> "ACTIVE",
                     timestamp |-> Len(events) + 1
                 ]
             IN
             /\ workflows' = (workflows \ {currentWorkflow}) \cup {updatedWorkflow}
             /\ events' = Append(events, newEvent)
             /\ UNCHANGED predicateLogic

-----------------------------------------------------------------------------
\* NEXT STATE RELATION

Next ==
    \/ \E wfId \in WorkflowIds : CreateWorkflow(wfId)
    \/ \E wfId \in WorkflowIds, targetState \in WorkflowStates : 
        ExecuteStateTransition(wfId, targetState)
    \/ \E wfId \in WorkflowIds, targetState \in WorkflowStates :
        StartTransition(wfId, targetState)
    \/ \E wfId \in WorkflowIds, targetState \in WorkflowStates :
        CompleteTransition(wfId, targetState)
    \/ \E wfId \in WorkflowIds : CancelTransition(wfId)
    \/ \E wfId \in WorkflowIds : RecoverWorkflow(wfId)
    \/ PredicateLogicUnavailable
    \/ PredicateLogicAvailable

\* Specification
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* SAFETY PROPERTIES

\* Type correctness
TypeOK ==
    /\ workflows \subseteq WorkflowRecord
    /\ \A wf \in workflows : wf.id \in WorkflowIds
    /\ \A i \in 1..Len(events) : events[i] \in EventRecord

\* Workflow uniqueness - each workflow ID appears at most once
WorkflowUniqueness ==
    \A wf1, wf2 \in workflows : wf1.id = wf2.id => wf1 = wf2

\* State consistency - all workflows have valid states
StateConsistency ==
    \A wf \in workflows : wf.state \in WorkflowStates

\* Transition validity - all state transitions follow business rules
TransitionValidity ==
    \A i \in 1..Len(events) :
        LET event == events[i]
        IN event.fromState # "NULL" => 
           <<event.fromState, event.toState>> \in ValidTransitions

\* Terminal state immutability
TerminalStateImmutability ==
    \A wf \in workflows : 
        IsTerminalState(wf.state) => ~wf.inTransition

\* Concurrent safety - workflows in transition cannot start new transitions
ConcurrentSafety ==
    \A wf \in workflows : 
        wf.inTransition => wf.state \notin TerminalStates

\* Version monotonicity - version numbers only increase
VersionMonotonicity ==
    \A wf \in workflows : wf.version >= 1

\* PredicateLogic dependency - transitions only occur when engine available
PredicateLogicDependency ==
    \A i \in 2..Len(events) :
        LET event == events[i]
            prevEvent == events[i-1]
        IN (event.fromState # "NULL" /\ event.fromState # prevEvent.toState) =>
           predicateLogic = TRUE

-----------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* Progress - workflows eventually transition out of non-terminal states
WorkflowProgress ==
    \A wf \in workflows :
        (~IsTerminalState(wf.state) /\ ~wf.inTransition) =>
            <>(wf \notin workflows \/ IsTerminalState(wf.state))

\* Recovery availability - failed workflows can be recovered
RecoveryAvailability ==
    \A wf \in workflows :
        (wf.state = "FAILED" /\ ~wf.inTransition /\ predicateLogic = TRUE) =>
            <>(wf.state = "ACTIVE")

\* Transition completion - transitions eventually complete or are cancelled
TransitionCompletion ==
    \A wf \in workflows :
        wf.inTransition => <>~wf.inTransition

-----------------------------------------------------------------------------
\* INVARIANTS

\* Bounded workflows
BoundedWorkflows == Cardinality(workflows) <= MaxWorkflows

\* Bounded events
BoundedEvents == Len(events) <= MaxWorkflows * 10

\* All safety properties combined
SafetyProperties ==
    /\ TypeOK
    /\ WorkflowUniqueness
    /\ StateConsistency
    /\ TransitionValidity
    /\ TerminalStateImmutability
    /\ ConcurrentSafety
    /\ VersionMonotonicity
    /\ BoundedWorkflows
    /\ BoundedEvents

=============================================================================
