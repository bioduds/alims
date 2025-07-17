---- MODULE ResultProcessingAgent ----
(*
TLA+ Specification for Result Processing Agent - Simplified
=========================================================

This specification models the core behavior of the Result Processing Agent 
in the ALIMS system. The agent processes raw test results from laboratory 
instruments and converts them into structured, validated results.

Key Properties:
1. All raw results are processed exactly once
2. Processing maintains data integrity
3. System handles capacity limits gracefully
4. Results are properly formatted and traceable

Version: 1.0
Author: ALIMS Development Team
Date: July 12, 2025
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxRawResults,           \* Maximum number of raw results in queue
    MaxProcessedResults,     \* Maximum number of processed results
    MAX_RETRIES             \* Maximum retry attempts for failed processing

VARIABLES
    raw_results,             \* Sequence of raw result IDs
    processed_results,       \* Sequence of processed result IDs
    processing_state,        \* Function from result ID to processing state
    retry_count,             \* Function from result ID to retry count
    system_state,            \* Overall system state
    next_result_id           \* Next available result ID

\* Processing states
ProcessingStates == {
    "RAW_RECEIVED",
    "PROCESSING",
    "PROCESSED",
    "FAILED",
    "QUEUED_FOR_REVIEW"
}

\* System states
SystemStates == {
    "INITIALIZING",
    "READY",
    "PROCESSING",
    "OVERLOADED",
    "SHUTDOWN"
}

\* Initial state predicate
Init == 
    /\ raw_results = <<>>
    /\ processed_results = <<>>
    /\ processing_state = <<>>
    /\ retry_count = <<>>
    /\ system_state = "INITIALIZING"
    /\ next_result_id = 1

\* System initialization
InitializeSystem ==
    /\ system_state = "INITIALIZING"
    /\ system_state' = "READY"
    /\ UNCHANGED <<raw_results, processed_results, processing_state, 
                  retry_count, next_result_id>>

\* Receive new raw result
ReceiveRawResult ==
    /\ system_state \in {"READY", "PROCESSING"}
    /\ Len(raw_results) < MaxRawResults
    /\ raw_results' = Append(raw_results, next_result_id)
    /\ processing_state' = Append(processing_state, "RAW_RECEIVED")
    /\ retry_count' = Append(retry_count, 0)
    /\ next_result_id' = next_result_id + 1
    /\ system_state' = "PROCESSING"
    /\ UNCHANGED processed_results

\* Start processing a raw result
StartProcessing ==
    /\ system_state = "PROCESSING"
    /\ \E i \in DOMAIN processing_state :
        /\ processing_state[i] = "RAW_RECEIVED"
        /\ processing_state' = [processing_state EXCEPT ![i] = "PROCESSING"]
        /\ UNCHANGED <<raw_results, processed_results, retry_count, 
                      system_state, next_result_id>>

\* Complete processing successfully
CompleteProcessing ==
    /\ system_state = "PROCESSING"
    /\ Len(processed_results) < MaxProcessedResults
    /\ \E i \in DOMAIN processing_state :
        /\ processing_state[i] = "PROCESSING"
        /\ processing_state' = [processing_state EXCEPT ![i] = "PROCESSED"]
        /\ processed_results' = Append(processed_results, raw_results[i])
        /\ UNCHANGED <<raw_results, retry_count, system_state, next_result_id>>

\* Processing fails
ProcessingFails ==
    /\ system_state = "PROCESSING"
    /\ \E i \in DOMAIN processing_state :
        /\ processing_state[i] = "PROCESSING"
        /\ processing_state' = [processing_state EXCEPT ![i] = "FAILED"]
        /\ UNCHANGED <<raw_results, processed_results, retry_count, 
                      system_state, next_result_id>>

\* Retry failed processing
RetryProcessing ==
    /\ system_state = "PROCESSING"
    /\ \E i \in DOMAIN processing_state :
        /\ processing_state[i] = "FAILED"
        /\ retry_count[i] < MAX_RETRIES
        /\ processing_state' = [processing_state EXCEPT ![i] = "RAW_RECEIVED"]
        /\ retry_count' = [retry_count EXCEPT ![i] = retry_count[i] + 1]
        /\ UNCHANGED <<raw_results, processed_results, system_state, next_result_id>>

\* Queue processed result for review
QueueForReview ==
    /\ system_state = "PROCESSING"
    /\ \E i \in DOMAIN processing_state :
        /\ processing_state[i] = "PROCESSED"
        /\ processing_state' = [processing_state EXCEPT ![i] = "QUEUED_FOR_REVIEW"]
        /\ UNCHANGED <<raw_results, processed_results, retry_count, 
                      system_state, next_result_id>>

\* Handle system overload
HandleOverload ==
    /\ system_state = "PROCESSING"
    /\ Len(raw_results) >= MaxRawResults
    /\ system_state' = "OVERLOADED"
    /\ UNCHANGED <<raw_results, processed_results, processing_state, 
                  retry_count, next_result_id>>

\* Recover from overload
RecoverFromOverload ==
    /\ system_state = "OVERLOADED"
    /\ Len(raw_results) < MaxRawResults
    /\ system_state' = "PROCESSING"
    /\ UNCHANGED <<raw_results, processed_results, processing_state, 
                  retry_count, next_result_id>>

\* System shutdown
ShutdownSystem ==
    /\ system_state \in {"READY", "PROCESSING", "OVERLOADED"}
    /\ system_state' = "SHUTDOWN"
    /\ UNCHANGED <<raw_results, processed_results, processing_state, 
                  retry_count, next_result_id>>

\* Next state relation
Next ==
    \/ InitializeSystem
    \/ ReceiveRawResult
    \/ StartProcessing
    \/ CompleteProcessing
    \/ ProcessingFails
    \/ RetryProcessing
    \/ QueueForReview
    \/ HandleOverload
    \/ RecoverFromOverload
    \/ ShutdownSystem
    \/ UNCHANGED <<raw_results, processed_results, processing_state, 
                  retry_count, system_state, next_result_id>>  \* Stuttering

\* Specification
Spec == Init /\ [][Next]_<<raw_results, processed_results, processing_state, 
                           retry_count, system_state, next_result_id>>

\* Type invariant
TypeInvariant ==
    /\ raw_results \in Seq(Nat)
    /\ processed_results \in Seq(Nat)
    /\ processing_state \in Seq(ProcessingStates)
    /\ retry_count \in Seq(Nat)
    /\ system_state \in SystemStates
    /\ next_result_id \in Nat

\* Safety Properties

\* No result is lost during processing
NoResultLoss ==
    \A i \in DOMAIN processing_state :
        processing_state[i] = "QUEUED_FOR_REVIEW" 
        => raw_results[i] \in {processed_results[j] : j \in DOMAIN processed_results}

\* System capacity limits are respected
CapacityLimits ==
    /\ Len(raw_results) <= MaxRawResults
    /\ Len(processed_results) <= MaxProcessedResults

\* Retry logic is bounded
BoundedRetries ==
    \A i \in DOMAIN retry_count : retry_count[i] <= MAX_RETRIES

\* Processing states are consistent
StateConsistency ==
    /\ Len(processing_state) = Len(raw_results)
    /\ Len(retry_count) = Len(raw_results)
    /\ \A i \in DOMAIN processing_state : processing_state[i] \in ProcessingStates

\* No duplicate processing
NoDuplicateProcessing ==
    \A i, j \in DOMAIN processed_results :
        i # j => processed_results[i] # processed_results[j]

\* System state consistency
SystemStateConsistency ==
    /\ system_state = "READY" => Len(raw_results) = 0
    /\ system_state = "OVERLOADED" => Len(raw_results) = MaxRawResults

\* Combined Safety Invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ NoResultLoss
    /\ CapacityLimits
    /\ BoundedRetries
    /\ StateConsistency
    /\ NoDuplicateProcessing
    /\ SystemStateConsistency

\* Liveness Properties

\* System eventually initializes
EventualInitialization ==
    <>(system_state = "READY")

\* All received results are eventually processed or failed permanently
EventualProcessing ==
    \A i \in DOMAIN processing_state :
        <>(processing_state[i] \in {"QUEUED_FOR_REVIEW", "FAILED"})

\* System eventually recovers from overload
EventualRecovery ==
    [](system_state = "OVERLOADED" => <>(system_state = "PROCESSING"))

====
