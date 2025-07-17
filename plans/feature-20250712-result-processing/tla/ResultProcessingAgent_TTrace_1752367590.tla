---- MODULE ResultProcessingAgent_TTrace_1752367590 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ResultProcessingAgent

_expression ==
    LET ResultProcessingAgent_TEExpression == INSTANCE ResultProcessingAgent_TEExpression
    IN ResultProcessingAgent_TEExpression!expression
----

_trace ==
    LET ResultProcessingAgent_TETrace == INSTANCE ResultProcessingAgent_TETrace
    IN ResultProcessingAgent_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        next_result_id = (1)
        /\
        retry_count = (<<>>)
        /\
        raw_results = (<<>>)
        /\
        system_state = ("SHUTDOWN")
        /\
        processed_results = (<<>>)
        /\
        processing_state = (<<>>)
    )
----

_init ==
    /\ system_state = _TETrace[1].system_state
    /\ processed_results = _TETrace[1].processed_results
    /\ next_result_id = _TETrace[1].next_result_id
    /\ raw_results = _TETrace[1].raw_results
    /\ retry_count = _TETrace[1].retry_count
    /\ processing_state = _TETrace[1].processing_state
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ system_state  = _TETrace[i].system_state
        /\ system_state' = _TETrace[j].system_state
        /\ processed_results  = _TETrace[i].processed_results
        /\ processed_results' = _TETrace[j].processed_results
        /\ next_result_id  = _TETrace[i].next_result_id
        /\ next_result_id' = _TETrace[j].next_result_id
        /\ raw_results  = _TETrace[i].raw_results
        /\ raw_results' = _TETrace[j].raw_results
        /\ retry_count  = _TETrace[i].retry_count
        /\ retry_count' = _TETrace[j].retry_count
        /\ processing_state  = _TETrace[i].processing_state
        /\ processing_state' = _TETrace[j].processing_state

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ResultProcessingAgent_TTrace_1752367590.json", _TETrace)

=============================================================================

 Note that you can extract this module `ResultProcessingAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `ResultProcessingAgent_TEExpression.tla` file takes precedence 
  over the module `ResultProcessingAgent_TEExpression` below).

---- MODULE ResultProcessingAgent_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ResultProcessingAgent

expression == 
    [
        \* To hide variables of the `ResultProcessingAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        system_state |-> system_state
        ,processed_results |-> processed_results
        ,next_result_id |-> next_result_id
        ,raw_results |-> raw_results
        ,retry_count |-> retry_count
        ,processing_state |-> processing_state
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_system_stateUnchanged |-> system_state = system_state'
        
        \* Format the `system_state` variable as Json value.
        \* ,_system_stateJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(system_state)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_system_stateModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].system_state # _TETrace[s-1].system_state
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE ResultProcessingAgent_TETrace ----
\*EXTENDS IOUtils, TLC, ResultProcessingAgent
\*
\*trace == IODeserialize("ResultProcessingAgent_TTrace_1752367590.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ResultProcessingAgent_TETrace ----
EXTENDS TLC, ResultProcessingAgent

trace == 
    <<
    ([next_result_id |-> 1,retry_count |-> <<>>,raw_results |-> <<>>,system_state |-> "INITIALIZING",processed_results |-> <<>>,processing_state |-> <<>>]),
    ([next_result_id |-> 1,retry_count |-> <<>>,raw_results |-> <<>>,system_state |-> "READY",processed_results |-> <<>>,processing_state |-> <<>>]),
    ([next_result_id |-> 1,retry_count |-> <<>>,raw_results |-> <<>>,system_state |-> "SHUTDOWN",processed_results |-> <<>>,processing_state |-> <<>>])
    >>
----


=============================================================================

---- CONFIG ResultProcessingAgent_TTrace_1752367590 ----
CONSTANTS
    MaxRawResults = 3
    MaxProcessedResults = 3
    ProcessingTimeLimit = 10
    MAX_RETRIES = 2
    SUPPORTED_FORMATS = { "CSV" , "JSON" }

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
\* Generated on Sat Jul 12 21:46:31 BRT 2025