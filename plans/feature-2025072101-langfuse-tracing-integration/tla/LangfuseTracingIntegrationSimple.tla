---- MODULE LangfuseTracingIntegrationSimple ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* State variables
VARIABLES
    traces,          \* Set of trace records
    trace_buffer,    \* Buffer for traces awaiting transmission
    langfuse_state,  \* Connection state to Langfuse
    active_ops       \* Set of active operation IDs

\* Constants
CONSTANTS
    MAX_BUFFER_SIZE,     \* Maximum buffered traces
    MAX_TRACES,          \* Maximum total traces
    OP_IDS              \* Set of possible operation IDs

\* Type definitions
TraceStates == {"PENDING", "SUCCESS", "ERROR"}
LangfuseStates == {"CONNECTED", "DISCONNECTED", "RECONNECTING", "ERROR"}
OperationTypes == {"LLM", "API", "AGENT", "WORKFLOW"}

\* Initial state
Init ==
    /\ traces = {}
    /\ trace_buffer = <<>>
    /\ langfuse_state = "DISCONNECTED"
    /\ active_ops = {}

\* Actions

\* Start tracing an operation
StartTrace(op_id, op_type) ==
    /\ op_id \in OP_IDS
    /\ op_id \notin active_ops
    /\ ~\E trace \in traces : trace.id = op_id  \* Prevent reusing completed operation IDs
    /\ Cardinality(traces) < MAX_TRACES
    /\ LET new_trace == [id |-> op_id, type |-> op_type, state |-> "PENDING"]
       IN
       /\ traces' = traces \cup {new_trace}
       /\ active_ops' = active_ops \cup {op_id}
       /\ trace_buffer' = Append(trace_buffer, new_trace)
       /\ UNCHANGED langfuse_state

\* Complete trace successfully
CompleteTrace(op_id) ==
    /\ op_id \in active_ops
    /\ \E trace \in traces : 
        /\ trace.id = op_id 
        /\ trace.state = "PENDING"
        /\ LET updated_trace == [trace EXCEPT !.state = "SUCCESS"]
           IN traces' = (traces \ {trace}) \cup {updated_trace}
    /\ active_ops' = active_ops \ {op_id}
    /\ UNCHANGED <<trace_buffer, langfuse_state>>

\* Fail trace with error
FailTrace(op_id) ==
    /\ op_id \in active_ops
    /\ \E trace \in traces : 
        /\ trace.id = op_id 
        /\ trace.state = "PENDING"
        /\ LET error_trace == [trace EXCEPT !.state = "ERROR"]
           IN traces' = (traces \ {trace}) \cup {error_trace}
    /\ active_ops' = active_ops \ {op_id}
    /\ UNCHANGED <<trace_buffer, langfuse_state>>

\* Connect to Langfuse
ConnectLangfuse ==
    /\ langfuse_state \in {"DISCONNECTED", "ERROR"}
    /\ langfuse_state' = "CONNECTED"
    /\ UNCHANGED <<traces, trace_buffer, active_ops>>

\* Handle Langfuse connection error
LangfuseError ==
    /\ langfuse_state = "CONNECTED"
    /\ langfuse_state' = "ERROR"
    /\ UNCHANGED <<traces, trace_buffer, active_ops>>

\* Flush buffer to Langfuse
FlushBuffer ==
    /\ langfuse_state = "CONNECTED"
    /\ Len(trace_buffer) > 0
    /\ trace_buffer' = <<>>
    /\ UNCHANGED <<traces, langfuse_state, active_ops>>

\* Auto-flush when buffer is full
AutoFlush ==
    /\ Len(trace_buffer) >= MAX_BUFFER_SIZE
    /\ langfuse_state = "CONNECTED"
    /\ trace_buffer' = <<>>
    /\ UNCHANGED <<traces, langfuse_state, active_ops>>

\* Next state relation
Next ==
    \/ \E op_id \in OP_IDS, op_type \in OperationTypes : StartTrace(op_id, op_type)
    \/ \E op_id \in active_ops : CompleteTrace(op_id)
    \/ \E op_id \in active_ops : FailTrace(op_id)
    \/ ConnectLangfuse
    \/ LangfuseError
    \/ FlushBuffer
    \/ AutoFlush

\* Specification
Spec == Init /\ [][Next]_<<traces, trace_buffer, langfuse_state, active_ops>>

\* Invariants

\* Type safety
TypeInvariant ==
    /\ traces \subseteq [id: OP_IDS, type: OperationTypes, state: TraceStates]
    /\ trace_buffer \in Seq([id: OP_IDS, type: OperationTypes, state: TraceStates])
    /\ langfuse_state \in LangfuseStates
    /\ active_ops \subseteq OP_IDS

\* Resource bounds
ResourceBounds ==
    /\ Cardinality(traces) <= MAX_TRACES
    /\ Len(trace_buffer) <= MAX_BUFFER_SIZE
    /\ Cardinality(active_ops) <= MAX_TRACES

\* Trace consistency
TraceConsistency ==
    /\ \A op_id \in active_ops : \E trace \in traces : trace.id = op_id
    /\ \A trace \in traces : trace.state = "PENDING" <=> trace.id \in active_ops

\* No duplicate traces
NoDuplicateTraces ==
    \A t1, t2 \in traces : t1.id = t2.id => t1 = t2

\* Buffer management
BufferManagement ==
    Len(trace_buffer) <= MAX_BUFFER_SIZE

\* Main safety property
Safety == 
    /\ TypeInvariant
    /\ ResourceBounds
    /\ TraceConsistency
    /\ NoDuplicateTraces
    /\ BufferManagement

====
