---- MODULE DebugSystem ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Define NULL constant for TLA+
NULL == "NULL"

\* Constants defining system boundaries
CONSTANTS
    MaxEvents,          \* Maximum number of events to track
    MaxAgents,          \* Maximum number of agents
    MaxConversations,   \* Maximum number of concurrent conversations
    DebugLevels,        \* Set of debug levels {TRACE, DEBUG, INFO, WARN, ERROR, CRITICAL}
    EventTypes,         \* Set of event types {INIT, RECEIVE_MESSAGE, PROCESS, RESPOND, ERROR, STATE_CHANGE}
    AgentIds,           \* Set of possible agent IDs
    ConversationIds     \* Set of possible conversation IDs

\* Assume reasonable bounds for model checking
ASSUME MaxEvents \in Nat /\ MaxEvents > 0
ASSUME MaxAgents \in Nat /\ MaxAgents > 0  
ASSUME MaxConversations \in Nat /\ MaxConversations > 0

\* Variables representing debug system state
VARIABLES
    events,                \* Sequence of all recorded events
    agent_states,          \* Function mapping agent_id to current state
    active_conversations,  \* Function mapping conversation_id to sequence of events
    performance_metrics,   \* Function mapping operation to sequence of durations
    subscribers,           \* Set of active WebSocket subscribers
    event_queue,          \* Queue of events waiting to be processed
    system_status         \* Current system status {INITIALIZING, READY, PROCESSING, ERROR}

\* Type definitions
EventRecord == [
    timestamp: Nat,
    agent_id: AgentIds,
    agent_type: STRING,
    event_type: EventTypes,
    message: STRING,
    data: STRING,
    level: DebugLevels,
    conversation_id: ConversationIds \cup {NULL},
    trace_id: STRING
]

AgentState == [
    status: STRING,
    last_activity: Nat,
    current_conversation: ConversationIds \cup {NULL},
    processing_message: BOOLEAN
]

PerformanceMetric == [
    operation: STRING,
    duration: Nat,
    timestamp: Nat
]

\* Type invariant
TypeInvariant ==
    /\ events \in Seq(EventRecord)
    /\ agent_states \in [AgentIds -> AgentState]
    /\ active_conversations \in [ConversationIds -> Seq(EventRecord)]
    /\ performance_metrics \in [STRING -> Seq(PerformanceMetric)]
    /\ subscribers \in SUBSET Nat
    /\ event_queue \in Seq(EventRecord)
    /\ system_status \in {"INITIALIZING", "READY", "PROCESSING", "ERROR"}

\* Initial state
Init ==
    /\ events = <<>>
    /\ agent_states = [a \in AgentIds |-> [
           status |-> "UNKNOWN",
           last_activity |-> 0,
           current_conversation |-> NULL,
           processing_message |-> FALSE
       ]]
    /\ active_conversations = [c \in ConversationIds |-> <<>>]
    /\ performance_metrics = [op \in {} |-> <<>>]
    /\ subscribers = {}
    /\ event_queue = <<>>
    /\ system_status = "INITIALIZING"

\* Helper functions
EventBelongsToConversation(event, conv_id) ==
    event.conversation_id = conv_id

GetConversationEvents(conv_id) ==
    SelectSeq(events, LAMBDA e: EventBelongsToConversation(e, conv_id))

\* System transitions

\* Initialize the debug system
InitializeSystem ==
    /\ system_status = "INITIALIZING"
    /\ system_status' = "READY"
    /\ UNCHANGED <<events, agent_states, active_conversations, performance_metrics, subscribers, event_queue>>

\* Record a new event
RecordEvent(event) ==
    /\ system_status = "READY"
    /\ Len(events) < MaxEvents
    /\ events' = Append(events, event)
    /\ IF event.conversation_id # NULL
       THEN active_conversations' = [active_conversations EXCEPT 
                ![event.conversation_id] = Append(@, event)]
       ELSE UNCHANGED active_conversations
    /\ UNCHANGED <<agent_states, performance_metrics, subscribers, event_queue, system_status>>

\* Update agent state
UpdateAgentState(agent_id, new_state) ==
    /\ system_status = "READY"
    /\ agent_id \in AgentIds
    /\ agent_states' = [agent_states EXCEPT ![agent_id] = new_state]
    /\ UNCHANGED <<events, active_conversations, performance_metrics, subscribers, event_queue, system_status>>

\* Record performance metric
RecordPerformanceMetric(operation, duration, timestamp) ==
    /\ system_status = "READY"
    /\ LET metric == [operation |-> operation, duration |-> duration, timestamp |-> timestamp]
       IN performance_metrics' = [performance_metrics EXCEPT 
            ![operation] = IF operation \in DOMAIN performance_metrics
                          THEN Append(@, metric)
                          ELSE <<metric>>]
    /\ UNCHANGED <<events, agent_states, active_conversations, subscribers, event_queue, system_status>>

\* Add WebSocket subscriber
AddSubscriber(subscriber_id) ==
    /\ system_status = "READY"
    /\ subscriber_id \notin subscribers
    /\ subscribers' = subscribers \cup {subscriber_id}
    /\ UNCHANGED <<events, agent_states, active_conversations, performance_metrics, event_queue, system_status>>

\* Remove WebSocket subscriber
RemoveSubscriber(subscriber_id) ==
    /\ system_status = "READY"
    /\ subscriber_id \in subscribers
    /\ subscribers' = subscribers \ {subscriber_id}
    /\ UNCHANGED <<events, agent_states, active_conversations, performance_metrics, event_queue, system_status>>

\* Process event queue (batch processing)
ProcessEventQueue ==
    /\ system_status = "READY"
    /\ event_queue # <<>>
    /\ system_status' = "PROCESSING"
    /\ LET new_events == events \o event_queue
       IN /\ events' = new_events
          /\ event_queue' = <<>>
    /\ system_status' = "READY"
    /\ UNCHANGED <<agent_states, active_conversations, performance_metrics, subscribers>>

\* Handle system error
HandleError ==
    /\ system_status \in {"READY", "PROCESSING"}
    /\ system_status' = "ERROR"
    /\ UNCHANGED <<events, agent_states, active_conversations, performance_metrics, subscribers, event_queue>>

\* Recover from error
RecoverFromError ==
    /\ system_status = "ERROR"
    /\ system_status' = "READY"
    /\ UNCHANGED <<events, agent_states, active_conversations, performance_metrics, subscribers, event_queue>>

\* System cleanup (memory management)
CleanupOldEvents ==
    /\ system_status = "READY"
    /\ Len(events) = MaxEvents
    /\ events' = SubSeq(events, 2, MaxEvents)  \* Remove oldest event
    /\ UNCHANGED <<agent_states, active_conversations, performance_metrics, subscribers, event_queue, system_status>>

\* Next state relation
Next ==
    \/ InitializeSystem
    \/ \E event \in EventRecord: RecordEvent(event)
    \/ \E agent_id \in AgentIds, state \in AgentState: UpdateAgentState(agent_id, state)
    \/ \E op \in STRING, dur \in Nat, ts \in Nat: RecordPerformanceMetric(op, dur, ts)
    \/ \E subscriber \in Nat: AddSubscriber(subscriber)
    \/ \E subscriber \in subscribers: RemoveSubscriber(subscriber)
    \/ ProcessEventQueue
    \/ HandleError
    \/ RecoverFromError
    \/ CleanupOldEvents

\* Specification
Spec == Init /\ [][Next]_<<events, agent_states, active_conversations, performance_metrics, subscribers, event_queue, system_status>>

\* Safety Properties

\* Events are always in chronological order
EventsChronologicalOrder ==
    \A i \in 1..(Len(events)-1):
        events[i].timestamp <= events[i+1].timestamp

\* No duplicate events
NoDuplicateEvents ==
    \A i, j \in 1..Len(events):
        i # j => events[i].trace_id # events[j].trace_id

\* Agent states are consistent
AgentStatesConsistent ==
    \A agent_id \in AgentIds:
        agent_states[agent_id].status \in {"UNKNOWN", "READY", "BUSY", "ERROR"}

\* Conversation events are properly grouped
ConversationEventsGrouped ==
    \A conv_id \in ConversationIds:
        \A event_idx \in DOMAIN active_conversations[conv_id]:
            active_conversations[conv_id][event_idx].conversation_id = conv_id

\* System maintains bounded memory
BoundedMemory ==
    /\ Len(events) <= MaxEvents
    /\ Cardinality(subscribers) <= MaxAgents
    /\ Len(event_queue) <= MaxEvents

\* System can always make progress
NoDeadlock ==
    system_status \in {"READY", "PROCESSING"} => ENABLED Next

\* Liveness Properties

\* All events eventually get processed
EventuallyProcessed ==
    []<>(event_queue = <<>>)

\* System eventually recovers from errors
EventuallyRecovers ==
    [](system_status = "ERROR" => <>(system_status = "READY"))

\* Performance metrics are eventually recorded
MetricsEventuallyRecorded ==
    \A op \in {"response_time", "cpu_usage", "memory_usage"}:
        []<>(op \in DOMAIN performance_metrics)

\* Invariants to check
THEOREM SystemInvariants ==
    Spec => []( TypeInvariant
                /\ EventsChronologicalOrder
                /\ NoDuplicateEvents
                /\ AgentStatesConsistent
                /\ ConversationEventsGrouped
                /\ BoundedMemory
                /\ NoDeadlock )

\* Properties to verify
THEOREM SystemProperties ==
    Spec => ( EventuallyProcessed
              /\ EventuallyRecovers
              /\ MetricsEventuallyRecorded )

====
