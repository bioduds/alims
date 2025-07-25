---- MODULE SimpleDebugSystem ----
EXTENDS Naturals, Sequences, FiniteSets

\* Constants
CONSTANTS MaxEvents, AgentIds, EventTypes

\* Variables  
VARIABLES events, agent_states, system_status

\* Type invariant
TypeInvariant ==
    /\ events \in Seq([type: EventTypes, agent_id: AgentIds, timestamp: Nat])
    /\ agent_states \in [AgentIds -> [status: {"READY", "BUSY", "ERROR"}]]
    /\ system_status \in {"INITIALIZING", "READY", "ERROR"}

\* Initial state
Init ==
    /\ events = <<>>
    /\ agent_states = [a \in AgentIds |-> [status |-> "READY"]]
    /\ system_status = "INITIALIZING"

\* Record a new event
RecordEvent(event_type, agent_id) ==
    /\ Len(events) < MaxEvents
    /\ events' = Append(events, [type |-> event_type, agent_id |-> agent_id, timestamp |-> Len(events) + 1])
    /\ UNCHANGED <<agent_states, system_status>>

\* Change agent status  
ChangeAgentStatus(agent_id, new_status) ==
    /\ agent_states' = [agent_states EXCEPT ![agent_id].status = new_status]
    /\ UNCHANGED <<events, system_status>>

\* System ready
SystemReady ==
    /\ system_status = "INITIALIZING"
    /\ system_status' = "READY"
    /\ UNCHANGED <<events, agent_states>>

\* Next state relation
Next ==
    \/ \E t \in EventTypes, a \in AgentIds: RecordEvent(t, a)
    \/ \E a \in AgentIds, s \in {"READY", "BUSY", "ERROR"}: ChangeAgentStatus(a, s)
    \/ SystemReady

\* Specification
Spec == Init /\ [][Next]_<<events, agent_states, system_status>>

\* Bounded memory invariant
BoundedMemory == Len(events) <= MaxEvents

====
