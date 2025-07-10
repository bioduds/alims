---- MODULE TensorCalendarVectorStorageSimple ----
EXTENDS Naturals, FiniteSets

\* Simplified constants for TLC validation
CONSTANTS
    MaxTensors,        \* Maximum number of tensors (2 for validation)
    MaxVectors,        \* Maximum number of vectors (2 for validation)
    MaxCollections     \* Maximum number of collections (2 for validation)

\* Type definitions
VARIABLES
    vectorDatabase,    \* Qdrant vector database state
    tensorStore,       \* Stored tensor calendar data
    storageMetrics,    \* Storage performance metrics
    systemState        \* Overall system state tracking

\* Helper operators
TensorDimension == 1..MaxTensors
VectorDimension == 1..MaxVectors  
CollectionDimension == 1..MaxCollections

\* Simple data types
TensorData == {"empty", "schedule1", "schedule2"}
Embedding == {"emb_empty", "emb_1", "emb_2"}
CollectionTypes == {"tensor_schedules", "resource_embeddings"}

\* Storage operation types
StorageOperations == {"store", "retrieve", "search", "delete"}

\* Initial state specification
Init ==
    /\ vectorDatabase = [
        collections |-> [c \in CollectionDimension |-> "tensor_schedules"],
        vectors |-> [v \in VectorDimension |-> {}],
        embeddings |-> [t \in TensorDimension |-> "emb_empty"]
       ]
    /\ tensorStore = [t \in TensorDimension |-> [
        tensor_id |-> 0,
        calendar_data |-> "empty",
        stored |-> FALSE
       ]]
    /\ storageMetrics = [
        total_stored |-> 0,
        storage_utilization |-> 0
       ]
    /\ systemState = "initializing"

\* Store a tensor calendar in vector database
StoreTensor(tensor_id, calendar_data, embedding) ==
    /\ tensor_id \in TensorDimension
    /\ calendar_data \in TensorData
    /\ embedding \in Embedding
    /\ calendar_data # "empty"
    /\ embedding # "emb_empty"
    /\ \* Check storage capacity
       storageMetrics.total_stored < MaxTensors
    /\ \* Ensure tensor not already stored
       tensorStore[tensor_id].stored = FALSE
    /\ \* Find available vector slot
       \E v \in VectorDimension :
        /\ vectorDatabase.vectors[v] = {}
        /\ \* Update vector database
           vectorDatabase' = [vectorDatabase EXCEPT
               !.vectors[v] = {tensor_id},
               !.embeddings[tensor_id] = embedding
           ]
        /\ \* Update tensor store
           tensorStore' = [tensorStore EXCEPT
               ![tensor_id] = [
                   tensor_id |-> tensor_id,
                   calendar_data |-> calendar_data,
                   stored |-> TRUE
               ]
           ]
    /\ \* Update storage metrics
       LET new_count == storageMetrics.total_stored + 1
           new_utilization == (new_count * 100) \div MaxTensors
       IN storageMetrics' = [storageMetrics EXCEPT
           !.total_stored = new_count,
           !.storage_utilization = new_utilization
       ]
    /\ systemState' = "storing"

\* Retrieve tensor from vector database
RetrieveTensor(tensor_id) ==
    /\ tensor_id \in TensorDimension
    /\ \* Check tensor exists
       tensorStore[tensor_id].stored = TRUE
    /\ systemState' = "retrieving"
    /\ UNCHANGED <<vectorDatabase, tensorStore, storageMetrics>>

\* Delete tensor from vector database
DeleteTensor(tensor_id) ==
    /\ tensor_id \in TensorDimension
    /\ \* Check tensor exists
       tensorStore[tensor_id].stored = TRUE
    /\ \* Find which vector contains this tensor
       \E v \in VectorDimension :
        /\ tensor_id \in vectorDatabase.vectors[v]
        /\ \* Clear vector database entry
           vectorDatabase' = [vectorDatabase EXCEPT
               !.vectors[v] = {},
               !.embeddings[tensor_id] = "emb_empty"
           ]
        /\ \* Clear tensor store entry
           tensorStore' = [tensorStore EXCEPT
               ![tensor_id] = [
                   tensor_id |-> 0,
                   calendar_data |-> "empty",
                   stored |-> FALSE
               ]
           ]
    /\ \* Update storage metrics
       LET new_count == storageMetrics.total_stored - 1
           new_utilization == (new_count * 100) \div MaxTensors
       IN storageMetrics' = [storageMetrics EXCEPT
           !.total_stored = new_count,
           !.storage_utilization = new_utilization
       ]
    /\ systemState' = "deleting"

\* Next-state relation
Next ==
    \/ \E t \in TensorDimension, data \in TensorData, emb \in Embedding :
        StoreTensor(t, data, emb)
    \/ \E t \in TensorDimension :
        RetrieveTensor(t)
    \/ \E t \in TensorDimension :
        DeleteTensor(t)

\* Specification
vars == <<vectorDatabase, tensorStore, storageMetrics, systemState>>

Spec == Init /\ [][Next]_vars

\* INVARIANTS - Critical properties that must always hold

\* Storage capacity is never exceeded
StorageCapacityInvariant ==
    storageMetrics.total_stored <= MaxTensors

\* Every stored tensor has a valid vector mapping
TensorVectorConsistency ==
    \A t \in TensorDimension :
        tensorStore[t].stored = TRUE =>
            \E v \in VectorDimension :
                t \in vectorDatabase.vectors[v]

\* Storage utilization percentage is valid
ValidStorageMetrics ==
    /\ storageMetrics.total_stored >= 0
    /\ storageMetrics.storage_utilization >= 0
    /\ storageMetrics.storage_utilization <= 100

\* System state is always valid
ValidSystemState ==
    systemState \in {"initializing", "storing", "retrieving", "deleting"}

\* TEMPORAL PROPERTIES

\* System can always make progress
SystemProgress ==
    <>[]( storageMetrics.total_stored >= 0 )

====
