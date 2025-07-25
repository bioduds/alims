---- MODULE LangfuseTracingIntegrationSimple_TTrace_1753146793 ----
EXTENDS Sequences, LangfuseTracingIntegrationSimple, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET LangfuseTracingIntegrationSimple_TEExpression == INSTANCE LangfuseTracingIntegrationSimple_TEExpression
    IN LangfuseTracingIntegrationSimple_TEExpression!expression
----

_trace ==
    LET LangfuseTracingIntegrationSimple_TETrace == INSTANCE LangfuseTracingIntegrationSimple_TETrace
    IN LangfuseTracingIntegrationSimple_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        active_ops = ({"op5"})
        /\
        traces = ({[id |-> "op5", type |-> "LLM", state |-> "PENDING"], [id |-> "op5", type |-> "LLM", state |-> "SUCCESS"]})
        /\
        trace_buffer = (<<[id |-> "op5", type |-> "LLM", state |-> "PENDING"], [id |-> "op5", type |-> "LLM", state |-> "PENDING"]>>)
        /\
        langfuse_state = ("DISCONNECTED")
    )
----

_init ==
    /\ active_ops = _TETrace[1].active_ops
    /\ trace_buffer = _TETrace[1].trace_buffer
    /\ langfuse_state = _TETrace[1].langfuse_state
    /\ traces = _TETrace[1].traces
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ active_ops  = _TETrace[i].active_ops
        /\ active_ops' = _TETrace[j].active_ops
        /\ trace_buffer  = _TETrace[i].trace_buffer
        /\ trace_buffer' = _TETrace[j].trace_buffer
        /\ langfuse_state  = _TETrace[i].langfuse_state
        /\ langfuse_state' = _TETrace[j].langfuse_state
        /\ traces  = _TETrace[i].traces
        /\ traces' = _TETrace[j].traces

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("LangfuseTracingIntegrationSimple_TTrace_1753146793.json", _TETrace)

=============================================================================

 Note that you can extract this module `LangfuseTracingIntegrationSimple_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `LangfuseTracingIntegrationSimple_TEExpression.tla` file takes precedence 
  over the module `LangfuseTracingIntegrationSimple_TEExpression` below).

---- MODULE LangfuseTracingIntegrationSimple_TEExpression ----
EXTENDS Sequences, LangfuseTracingIntegrationSimple, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `LangfuseTracingIntegrationSimple` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        active_ops |-> active_ops
        ,trace_buffer |-> trace_buffer
        ,langfuse_state |-> langfuse_state
        ,traces |-> traces
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_active_opsUnchanged |-> active_ops = active_ops'
        
        \* Format the `active_ops` variable as Json value.
        \* ,_active_opsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(active_ops)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_active_opsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].active_ops # _TETrace[s-1].active_ops
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE LangfuseTracingIntegrationSimple_TETrace ----
\*EXTENDS IOUtils, LangfuseTracingIntegrationSimple, TLC
\*
\*trace == IODeserialize("LangfuseTracingIntegrationSimple_TTrace_1753146793.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE LangfuseTracingIntegrationSimple_TETrace ----
EXTENDS LangfuseTracingIntegrationSimple, TLC

trace == 
    <<
    ([active_ops |-> {},traces |-> {},trace_buffer |-> <<>>,langfuse_state |-> "DISCONNECTED"]),
    ([active_ops |-> {"op5"},traces |-> {[id |-> "op5", type |-> "LLM", state |-> "PENDING"]},trace_buffer |-> <<[id |-> "op5", type |-> "LLM", state |-> "PENDING"]>>,langfuse_state |-> "DISCONNECTED"]),
    ([active_ops |-> {},traces |-> {[id |-> "op5", type |-> "LLM", state |-> "SUCCESS"]},trace_buffer |-> <<[id |-> "op5", type |-> "LLM", state |-> "PENDING"]>>,langfuse_state |-> "DISCONNECTED"]),
    ([active_ops |-> {"op5"},traces |-> {[id |-> "op5", type |-> "LLM", state |-> "PENDING"], [id |-> "op5", type |-> "LLM", state |-> "SUCCESS"]},trace_buffer |-> <<[id |-> "op5", type |-> "LLM", state |-> "PENDING"], [id |-> "op5", type |-> "LLM", state |-> "PENDING"]>>,langfuse_state |-> "DISCONNECTED"])
    >>
----


=============================================================================

---- CONFIG LangfuseTracingIntegrationSimple_TTrace_1753146793 ----
CONSTANTS
    MAX_BUFFER_SIZE = 5
    MAX_TRACES = 10
    OP_IDS = { "op1" , "op2" , "op3" , "op4" , "op5" }

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Mon Jul 21 22:13:14 BRT 2025