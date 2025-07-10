---- MODULE TensorCalendarVectorStorageSimple_TTrace_1752131118 ----
EXTENDS Sequences, TensorCalendarVectorStorageSimple, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET TensorCalendarVectorStorageSimple_TEExpression == INSTANCE TensorCalendarVectorStorageSimple_TEExpression
    IN TensorCalendarVectorStorageSimple_TEExpression!expression
----

_trace ==
    LET TensorCalendarVectorStorageSimple_TETrace == INSTANCE TensorCalendarVectorStorageSimple_TETrace
    IN TensorCalendarVectorStorageSimple_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        systemState = ("storing")
        /\
        tensorStore = (<<[tensor_id |-> 1, calendar_data |-> "schedule1", stored |-> TRUE], [tensor_id |-> 2, calendar_data |-> "schedule1", stored |-> TRUE]>>)
        /\
        vectorDatabase = ([collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{1}, {2}>>, embeddings |-> <<"emb_1", "emb_1">>])
        /\
        storageMetrics = ([total_stored |-> 2, storage_utilization |-> 2550])
    )
----

_init ==
    /\ vectorDatabase = _TETrace[1].vectorDatabase
    /\ systemState = _TETrace[1].systemState
    /\ tensorStore = _TETrace[1].tensorStore
    /\ storageMetrics = _TETrace[1].storageMetrics
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ vectorDatabase  = _TETrace[i].vectorDatabase
        /\ vectorDatabase' = _TETrace[j].vectorDatabase
        /\ systemState  = _TETrace[i].systemState
        /\ systemState' = _TETrace[j].systemState
        /\ tensorStore  = _TETrace[i].tensorStore
        /\ tensorStore' = _TETrace[j].tensorStore
        /\ storageMetrics  = _TETrace[i].storageMetrics
        /\ storageMetrics' = _TETrace[j].storageMetrics

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TensorCalendarVectorStorageSimple_TTrace_1752131118.json", _TETrace)

=============================================================================

 Note that you can extract this module `TensorCalendarVectorStorageSimple_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TensorCalendarVectorStorageSimple_TEExpression.tla` file takes precedence 
  over the module `TensorCalendarVectorStorageSimple_TEExpression` below).

---- MODULE TensorCalendarVectorStorageSimple_TEExpression ----
EXTENDS Sequences, TensorCalendarVectorStorageSimple, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `TensorCalendarVectorStorageSimple` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        vectorDatabase |-> vectorDatabase
        ,systemState |-> systemState
        ,tensorStore |-> tensorStore
        ,storageMetrics |-> storageMetrics
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_vectorDatabaseUnchanged |-> vectorDatabase = vectorDatabase'
        
        \* Format the `vectorDatabase` variable as Json value.
        \* ,_vectorDatabaseJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(vectorDatabase)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_vectorDatabaseModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].vectorDatabase # _TETrace[s-1].vectorDatabase
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TensorCalendarVectorStorageSimple_TETrace ----
\*EXTENDS IOUtils, TensorCalendarVectorStorageSimple, TLC
\*
\*trace == IODeserialize("TensorCalendarVectorStorageSimple_TTrace_1752131118.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TensorCalendarVectorStorageSimple_TETrace ----
EXTENDS TensorCalendarVectorStorageSimple, TLC

trace == 
    <<
    ([systemState |-> "initializing",tensorStore |-> <<[tensor_id |-> 0, calendar_data |-> "empty", stored |-> FALSE], [tensor_id |-> 0, calendar_data |-> "empty", stored |-> FALSE]>>,vectorDatabase |-> [collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{}, {}>>, embeddings |-> <<"emb_empty", "emb_empty">>],storageMetrics |-> [total_stored |-> 0, storage_utilization |-> 0]]),
    ([systemState |-> "storing",tensorStore |-> <<[tensor_id |-> 1, calendar_data |-> "schedule1", stored |-> TRUE], [tensor_id |-> 0, calendar_data |-> "empty", stored |-> FALSE]>>,vectorDatabase |-> [collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{1}, {}>>, embeddings |-> <<"emb_1", "emb_empty">>],storageMetrics |-> [total_stored |-> 1, storage_utilization |-> 50]]),
    ([systemState |-> "storing",tensorStore |-> <<[tensor_id |-> 1, calendar_data |-> "schedule1", stored |-> TRUE], [tensor_id |-> 2, calendar_data |-> "schedule1", stored |-> TRUE]>>,vectorDatabase |-> [collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{1}, {2}>>, embeddings |-> <<"emb_1", "emb_1">>],storageMetrics |-> [total_stored |-> 2, storage_utilization |-> 2550]])
    >>
----


=============================================================================

---- CONFIG TensorCalendarVectorStorageSimple_TTrace_1752131118 ----
CONSTANTS
    MaxTensors = 2
    MaxVectors = 2
    MaxCollections = 2

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
\* Generated on Thu Jul 10 04:05:18 BRT 2025