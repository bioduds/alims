---- MODULE LangfuseTracingIntegration ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* State variables
VARIABLES
    traces,          \* Set of trace objects
    trace_buffer,    \* Buffered traces awaiting transmission
    langfuse_state,  \* Connection state to Langfuse
    system_ops,      \* Ongoing system operations
    trace_config     \* Tracing configuration

\* Constants
CONSTANTS
    MAX_BUFFER_SIZE,     \* Maximum buffered traces
    MAX_TRACES,          \* Maximum total traces
    OP_TYPES,           \* Set of operation types {LLM, API, AGENT, WORKFLOW}
    TRACE_LEVELS        \* Set of trace levels {DEBUG, INFO, WARN, ERROR}

\* Type definitions
TraceRecord == [
    id: STRING,
    operation_type: OP_TYPES,
    level: TRACE_LEVELS,
    timestamp: Nat,
    duration: Nat,
    metadata: SUBSET STRING,
    parent_trace: STRING \cup {""},
    status: {"PENDING", "SUCCESS", "ERROR"}
]

LangfuseState == {"CONNECTED", "DISCONNECTED", "RECONNECTING", "ERROR"}

SystemOperation == [
    id: STRING,
    type: OP_TYPES,
    start_time: Nat,
    trace_id: STRING,
    status: {"RUNNING", "COMPLETED", "FAILED"}
]

TracingConfig == [
    enabled: BOOLEAN,
    level: TRACE_LEVELS,
    buffer_size: 1..MAX_BUFFER_SIZE,
    auto_flush: BOOLEAN,
    privacy_filter: BOOLEAN
]

\* Initial state
Init ==
    /\ traces = {}
    /\ trace_buffer = <<>>
    /\ langfuse_state = "DISCONNECTED"
    /\ system_ops = {}
    /\ trace_config = [
           enabled |-> TRUE,
           level |-> "INFO",
           buffer_size |-> 10,
           auto_flush |-> TRUE,
           privacy_filter |-> TRUE
       ]

\* Actions

\* Start tracing a system operation
StartOperation(op_id, op_type) ==
    /\ trace_config.enabled = TRUE
    /\ op_id \notin {op.id : op \in system_ops}
    /\ LET new_trace_id == op_id \o "_trace"
           new_trace == [
               id |-> new_trace_id,
               operation_type |-> op_type,
               level |-> "INFO",
               timestamp |-> Len(traces) + 1,
               duration |-> 0,
               metadata |-> {},
               parent_trace |-> "",
               status |-> "PENDING"
           ]
           new_op == [
               id |-> op_id,
               type |-> op_type,
               start_time |-> Len(traces) + 1,
               trace_id |-> new_trace_id,
               status |-> "RUNNING"
           ]
       IN
       /\ traces' = traces \cup {new_trace}
       /\ system_ops' = system_ops \cup {new_op}
       /\ trace_buffer' = Append(trace_buffer, new_trace)
       /\ UNCHANGED <<langfuse_state, trace_config>>

\* Complete an operation with success
CompleteOperation(op_id, duration) ==
    /\ \E op \in system_ops : 
        /\ op.id = op_id 
        /\ op.status = "RUNNING"
        /\ LET trace_id == op.trace_id
               updated_trace == [
                   id |-> trace_id,
                   operation_type |-> op.type,
                   level |-> "INFO",
                   timestamp |-> op.start_time,
                   duration |-> duration,
                   metadata |-> {},
                   parent_trace |-> "",
                   status |-> "SUCCESS"
               ]
               updated_op == [op EXCEPT !.status = "COMPLETED"]
           IN
           /\ traces' = (traces \ {t \in traces : t.id = trace_id}) \cup {updated_trace}
           /\ system_ops' = (system_ops \ {op}) \cup {updated_op}
           /\ UNCHANGED <<trace_buffer, langfuse_state, trace_config>>

\* Fail an operation
FailOperation(op_id, error_msg) ==
    /\ \E op \in system_ops :
        /\ op.id = op_id
        /\ op.status = "RUNNING"
        /\ LET trace_id == op.trace_id
               error_trace == [
                   id |-> trace_id,
                   operation_type |-> op.type,
                   level |-> "ERROR",
                   timestamp |-> op.start_time,
                   duration |-> 0,
                   metadata |-> {error_msg},
                   parent_trace |-> "",
                   status |-> "ERROR"
               ]
               failed_op == [op EXCEPT !.status = "FAILED"]
           IN
           /\ traces' = (traces \ {t \in traces : t.id = trace_id}) \cup {error_trace}
           /\ system_ops' = (system_ops \ {op}) \cup {failed_op}
           /\ UNCHANGED <<trace_buffer, langfuse_state, trace_config>>

\* Flush buffer to Langfuse
FlushBuffer ==
    /\ langfuse_state = "CONNECTED"
    /\ Len(trace_buffer) > 0
    /\ trace_buffer' = <<>>
    /\ UNCHANGED <<traces, langfuse_state, system_ops, trace_config>>

\* Connect to Langfuse
ConnectLangfuse ==
    /\ langfuse_state \in {"DISCONNECTED", "ERROR"}
    /\ langfuse_state' = "CONNECTED"
    /\ UNCHANGED <<traces, trace_buffer, system_ops, trace_config>>

\* Handle Langfuse connection error
LangfuseError ==
    /\ langfuse_state = "CONNECTED"
    /\ langfuse_state' = "ERROR"
    /\ UNCHANGED <<traces, trace_buffer, system_ops, trace_config>>

\* Auto-flush when buffer is full
AutoFlush ==
    /\ trace_config.auto_flush = TRUE
    /\ Len(trace_buffer) >= trace_config.buffer_size
    /\ langfuse_state = "CONNECTED"
    /\ trace_buffer' = <<>>
    /\ UNCHANGED <<traces, langfuse_state, system_ops, trace_config>>

\* Update tracing configuration
UpdateConfig(new_config) ==
    /\ trace_config' = new_config
    /\ UNCHANGED <<traces, trace_buffer, langfuse_state, system_ops>>

\* Next state relation
Next ==
    \/ \E op_id \in STRING, op_type \in OP_TYPES : StartOperation(op_id, op_type)
    \/ \E op_id \in STRING, duration \in Nat : CompleteOperation(op_id, duration)
    \/ \E op_id \in STRING, error \in STRING : FailOperation(op_id, error)
    \/ FlushBuffer
    \/ ConnectLangfuse
    \/ LangfuseError
    \/ AutoFlush
    \/ \E config \in TracingConfig : UpdateConfig(config)

\* Specification
Spec == Init /\ [][Next]_<<traces, trace_buffer, langfuse_state, system_ops, trace_config>>

\* Invariants

\* Type safety
TypeInvariant ==
    /\ traces \subseteq TraceRecord
    /\ trace_buffer \in Seq(TraceRecord)
    /\ langfuse_state \in LangfuseState
    /\ system_ops \subseteq SystemOperation
    /\ trace_config \in TracingConfig

\* Resource bounds
ResourceBounds ==
    /\ Cardinality(traces) <= MAX_TRACES
    /\ Len(trace_buffer) <= MAX_BUFFER_SIZE
    /\ Cardinality(system_ops) <= MAX_TRACES

\* Trace consistency
TraceConsistency ==
    /\ \A trace \in traces : trace.id \in STRING
    /\ \A op \in system_ops : 
        \E trace \in traces : trace.id = op.trace_id

\* No duplicate trace IDs
NoDuplicateTraces ==
    \A t1, t2 \in traces : t1 # t2 => t1.id # t2.id

\* Buffer management
BufferManagement ==
    /\ Len(trace_buffer) <= trace_config.buffer_size
    /\ trace_config.auto_flush = TRUE => 
        (Len(trace_buffer) = trace_config.buffer_size => langfuse_state = "CONNECTED")

\* Main safety property
Safety == 
    /\ TypeInvariant
    /\ ResourceBounds
    /\ TraceConsistency
    /\ NoDuplicateTraces
    /\ BufferManagement

\* Liveness properties

\* Eventually flush buffer
EventuallyFlush ==
    []<>(Len(trace_buffer) = 0)

\* Eventually connect to Langfuse
EventuallyConnect ==
    []<>(langfuse_state = "CONNECTED")

\* Operations eventually complete
OperationsComplete ==
    [](\A op \in system_ops : op.status = "RUNNING" => <>(op.status \in {"COMPLETED", "FAILED"}))

\* Main liveness property
Liveness ==
    /\ EventuallyFlush
    /\ EventuallyConnect
    /\ OperationsComplete

====
