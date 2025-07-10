---- MODULE TensorCalendarVectorStorage_TTrace_1752130986 ----
EXTENDS TensorCalendarVectorStorage, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET TensorCalendarVectorStorage_TEExpression == INSTANCE TensorCalendarVectorStorage_TEExpression
    IN TensorCalendarVectorStorage_TEExpression!expression
----

_trace ==
    LET TensorCalendarVectorStorage_TETrace == INSTANCE TensorCalendarVectorStorage_TETrace
    IN TensorCalendarVectorStorage_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        embeddingCache = (<<[embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE], [embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE]>>)
        /\
        systemState = ("batch_processing")
        /\
        queryHistory = (<<>>)
        /\
        tensorStore = (<<[tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0], [tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0]>>)
        /\
        lastOperation = (1)
        /\
        vectorDatabase = ([collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{}, {}>>, metadata |-> <<<<>>, <<>>>>, embeddings |-> <<<<>>, <<>>>>, similarity_index |-> <<{}, {}>>])
        /\
        storageMetrics = ([total_stored |-> 2, cache_hits |-> 0, cache_misses |-> 0, avg_query_time |-> 0, storage_utilization |-> 100])
    )
----

_init ==
    /\ vectorDatabase = _TETrace[1].vectorDatabase
    /\ storageMetrics = _TETrace[1].storageMetrics
    /\ systemState = _TETrace[1].systemState
    /\ queryHistory = _TETrace[1].queryHistory
    /\ embeddingCache = _TETrace[1].embeddingCache
    /\ lastOperation = _TETrace[1].lastOperation
    /\ tensorStore = _TETrace[1].tensorStore
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ vectorDatabase  = _TETrace[i].vectorDatabase
        /\ vectorDatabase' = _TETrace[j].vectorDatabase
        /\ storageMetrics  = _TETrace[i].storageMetrics
        /\ storageMetrics' = _TETrace[j].storageMetrics
        /\ systemState  = _TETrace[i].systemState
        /\ systemState' = _TETrace[j].systemState
        /\ queryHistory  = _TETrace[i].queryHistory
        /\ queryHistory' = _TETrace[j].queryHistory
        /\ embeddingCache  = _TETrace[i].embeddingCache
        /\ embeddingCache' = _TETrace[j].embeddingCache
        /\ lastOperation  = _TETrace[i].lastOperation
        /\ lastOperation' = _TETrace[j].lastOperation
        /\ tensorStore  = _TETrace[i].tensorStore
        /\ tensorStore' = _TETrace[j].tensorStore

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TensorCalendarVectorStorage_TTrace_1752130986.json", _TETrace)

=============================================================================

 Note that you can extract this module `TensorCalendarVectorStorage_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TensorCalendarVectorStorage_TEExpression.tla` file takes precedence 
  over the module `TensorCalendarVectorStorage_TEExpression` below).

---- MODULE TensorCalendarVectorStorage_TEExpression ----
EXTENDS TensorCalendarVectorStorage, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `TensorCalendarVectorStorage` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        vectorDatabase |-> vectorDatabase
        ,storageMetrics |-> storageMetrics
        ,systemState |-> systemState
        ,queryHistory |-> queryHistory
        ,embeddingCache |-> embeddingCache
        ,lastOperation |-> lastOperation
        ,tensorStore |-> tensorStore
        
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
\*---- MODULE TensorCalendarVectorStorage_TETrace ----
\*EXTENDS TensorCalendarVectorStorage, IOUtils, TLC
\*
\*trace == IODeserialize("TensorCalendarVectorStorage_TTrace_1752130986.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TensorCalendarVectorStorage_TETrace ----
EXTENDS TensorCalendarVectorStorage, TLC

trace == 
    <<
    ([embeddingCache |-> <<[embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE], [embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE]>>,systemState |-> "initializing",queryHistory |-> <<>>,tensorStore |-> <<[tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0], [tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0]>>,lastOperation |-> 0,vectorDatabase |-> [collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{}, {}>>, metadata |-> <<<<>>, <<>>>>, embeddings |-> <<<<>>, <<>>>>, similarity_index |-> <<{}, {}>>],storageMetrics |-> [total_stored |-> 0, cache_hits |-> 0, cache_misses |-> 0, avg_query_time |-> 0, storage_utilization |-> 0]]),
    ([embeddingCache |-> <<[embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE], [embedding |-> <<>>, computed_at |-> 0, cache_hit |-> FALSE]>>,systemState |-> "batch_processing",queryHistory |-> <<>>,tensorStore |-> <<[tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0], [tensor_id |-> "", calendar_data |-> <<>>, stored_at |-> 0, vector_id |-> 0]>>,lastOperation |-> 1,vectorDatabase |-> [collections |-> <<"tensor_schedules", "tensor_schedules">>, vectors |-> <<{}, {}>>, metadata |-> <<<<>>, <<>>>>, embeddings |-> <<<<>>, <<>>>>, similarity_index |-> <<{}, {}>>],storageMetrics |-> [total_stored |-> 2, cache_hits |-> 0, cache_misses |-> 0, avg_query_time |-> 0, storage_utilization |-> 100]])
    >>
----


=============================================================================

---- CONFIG TensorCalendarVectorStorage_TTrace_1752130986 ----
CONSTANTS
    MaxTensors = 2
    MaxVectors = 2
    MaxCollections = 2
    MaxBatchSize = 2
    MaxQueryResults = 2
    MaxSeqLength = 2

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
\* Generated on Thu Jul 10 04:03:07 BRT 2025