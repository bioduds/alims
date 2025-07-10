------------------------------ MODULE NaturalLanguageCalendarWorkflow ------------------------------
(*
TLA+ Specification for Natural Language Calendar Workflow Integration

This specification models the integration of natural language processing 
with the TLA+ verified tensor calendar and vector storage system.

The workflow handles user requests like:
- "schedule a PCR for these samples"
- "book the confocal microscope for tomorrow"
- "reserve the sequencer for batch B001"

Key Components:
1. Natural Language Intent Parser
2. Calendar Operation Orchestrator  
3. Vector Storage Integration
4. Response Generator

Author: ALIMS Development Team
Date: January 10, 2025
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  MAX_REQUESTS,           \* Maximum concurrent requests
  MAX_PARSED_INTENTS,     \* Maximum parsed intents in system
  MAX_CALENDAR_OPS,       \* Maximum calendar operations in flight
  MAX_STORAGE_OPS,        \* Maximum storage operations in flight
  USERS,                  \* Set of users
  RESOURCES,              \* Set of schedulable resources
  INTENT_TYPES            \* Set of intent types (SCHEDULE, CANCEL, QUERY, etc.)

VARIABLES
  \* Natural Language Processing State
  nl_requests,            \* Set of incoming NL requests  
  parsed_intents,         \* Mapping: request_id -> intent_data
  intent_parser_state,    \* State of NL parser (IDLE, PARSING, ERROR)
  
  \* Calendar Orchestration State
  calendar_operations,    \* Set of calendar operations in progress
  orchestrator_state,     \* State of orchestrator (READY, ORCHESTRATING, ERROR)
  pending_schedules,      \* Queue of schedules to be processed
  
  \* Vector Storage Integration State  
  storage_requests,       \* Set of storage requests in flight
  vector_storage_state,   \* State of vector storage (AVAILABLE, BUSY, ERROR)
  stored_schedules,       \* Set of schedules stored in vector DB
  
  \* Response Generation State
  pending_responses,      \* Queue of responses to be generated
  generated_responses,    \* Set of generated responses
  response_generator_state, \* State of response generator
  
  \* System Metrics
  total_processed,        \* Total requests processed
  successful_schedules,   \* Number of successful schedules created
  failed_operations      \* Number of failed operations

\* Type definitions
RequestID == 1..MAX_REQUESTS
IntentData == [
  type: INTENT_TYPES,
  resource: RESOURCES,
  user: USERS,
  parameters: Seq(Nat),
  timestamp: Nat
]

CalendarOperation == [
  id: RequestID,
  operation: {"CREATE", "UPDATE", "DELETE", "QUERY"},
  resource: RESOURCES,
  user: USERS,
  status: {"PENDING", "IN_PROGRESS", "COMPLETED", "FAILED"}
]

StorageRequest == [
  id: RequestID,
  operation: {"STORE", "RETRIEVE", "DELETE"},
  data: Seq(Nat),
  status: {"PENDING", "IN_PROGRESS", "COMPLETED", "FAILED"}
]

Response == [
  request_id: RequestID,
  status: {"SUCCESS", "PARTIAL", "FAILED"},
  message: Seq(Nat),
  data: Seq(Nat)
]

\* Initial state predicate
Init ==
  /\ nl_requests = {}
  /\ parsed_intents = [r \in {} |-> {}]
  /\ intent_parser_state = "IDLE"
  /\ calendar_operations = {}
  /\ orchestrator_state = "READY"
  /\ pending_schedules = <<>>
  /\ storage_requests = {}
  /\ vector_storage_state = "AVAILABLE"
  /\ stored_schedules = {}
  /\ pending_responses = <<>>
  /\ generated_responses = {}
  /\ response_generator_state = "IDLE"
  /\ total_processed = 0
  /\ successful_schedules = 0
  /\ failed_operations = 0

\* Natural Language Request Processing
ReceiveNLRequest(request_id, user, content) ==
  /\ request_id \notin nl_requests
  /\ Cardinality(nl_requests) < MAX_REQUESTS
  /\ nl_requests' = nl_requests \cup {request_id}
  /\ UNCHANGED <<parsed_intents, intent_parser_state, calendar_operations,
                 orchestrator_state, pending_schedules, storage_requests,
                 vector_storage_state, stored_schedules, pending_responses,
                 generated_responses, response_generator_state, total_processed,
                 successful_schedules, failed_operations>>

\* Intent Parsing
ParseIntent(request_id, intent_type, resource, user) ==
  /\ request_id \in nl_requests
  /\ intent_parser_state = "IDLE"
  /\ Cardinality(DOMAIN parsed_intents) < MAX_PARSED_INTENTS
  /\ intent_parser_state' = "PARSING"
  /\ parsed_intents' = parsed_intents @@ 
     (request_id :> [type |-> intent_type, resource |-> resource, 
                     user |-> user, parameters |-> <<>>, timestamp |-> total_processed])
  /\ UNCHANGED <<nl_requests, calendar_operations, orchestrator_state,
                 pending_schedules, storage_requests, vector_storage_state,
                 stored_schedules, pending_responses, generated_responses,
                 response_generator_state, total_processed, successful_schedules,
                 failed_operations>>

CompleteIntentParsing ==
  /\ intent_parser_state = "PARSING"
  /\ intent_parser_state' = "IDLE"
  /\ UNCHANGED <<nl_requests, parsed_intents, calendar_operations,
                 orchestrator_state, pending_schedules, storage_requests,
                 vector_storage_state, stored_schedules, pending_responses,
                 generated_responses, response_generator_state, total_processed,
                 successful_schedules, failed_operations>>

\* Calendar Operation Orchestration  
CreateCalendarOperation(request_id, operation_type, resource, user) ==
  /\ request_id \in DOMAIN parsed_intents
  /\ orchestrator_state = "READY"
  /\ Cardinality(calendar_operations) < MAX_CALENDAR_OPS
  /\ LET op == [id |-> request_id, operation |-> operation_type,
                resource |-> resource, user |-> user, status |-> "PENDING"]
     IN calendar_operations' = calendar_operations \cup {op}
  /\ orchestrator_state' = "ORCHESTRATING"
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 pending_schedules, storage_requests, vector_storage_state,
                 stored_schedules, pending_responses, generated_responses,
                 response_generator_state, total_processed, successful_schedules,
                 failed_operations>>

ProcessCalendarOperation(op) ==
  /\ op \in calendar_operations
  /\ op.status = "PENDING"
  /\ orchestrator_state = "ORCHESTRATING"
  /\ LET updated_op == [op EXCEPT !.status = "IN_PROGRESS"]
     IN calendar_operations' = (calendar_operations \ {op}) \cup {updated_op}
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 orchestrator_state, pending_schedules, storage_requests,
                 vector_storage_state, stored_schedules, pending_responses,
                 generated_responses, response_generator_state, total_processed,
                 successful_schedules, failed_operations>>

CompleteCalendarOperation(op, success) ==
  /\ op \in calendar_operations
  /\ op.status = "IN_PROGRESS"
  /\ LET new_status == IF success THEN "COMPLETED" ELSE "FAILED"
         updated_op == [op EXCEPT !.status = new_status]
     IN calendar_operations' = (calendar_operations \ {op}) \cup {updated_op}
  /\ IF success 
     THEN /\ successful_schedules' = successful_schedules + 1
          /\ UNCHANGED failed_operations
     ELSE /\ failed_operations' = failed_operations + 1
          /\ UNCHANGED successful_schedules
  /\ IF success /\ op.operation = "CREATE" 
     THEN pending_schedules' = Append(pending_schedules, op.id)
     ELSE UNCHANGED pending_schedules
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 orchestrator_state, storage_requests, vector_storage_state,
                 stored_schedules, pending_responses, generated_responses,
                 response_generator_state, total_processed>>

\* Vector Storage Integration
CreateStorageRequest(schedule_id, operation_type) ==
  /\ schedule_id \in {op.id : op \in {o \in calendar_operations : o.status = "COMPLETED"}}
  /\ vector_storage_state = "AVAILABLE"
  /\ Cardinality(storage_requests) < MAX_STORAGE_OPS
  /\ LET req == [id |-> schedule_id, operation |-> operation_type,
                 data |-> <<schedule_id>>, status |-> "PENDING"]
     IN storage_requests' = storage_requests \cup {req}
  /\ vector_storage_state' = "BUSY"
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 calendar_operations, orchestrator_state, pending_schedules,
                 stored_schedules, pending_responses, generated_responses,
                 response_generator_state, total_processed, successful_schedules,
                 failed_operations>>

ProcessStorageRequest(req) ==
  /\ req \in storage_requests
  /\ req.status = "PENDING"
  /\ vector_storage_state = "BUSY"
  /\ LET updated_req == [req EXCEPT !.status = "IN_PROGRESS"]
     IN storage_requests' = (storage_requests \ {req}) \cup {updated_req}
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 calendar_operations, orchestrator_state, pending_schedules,
                 vector_storage_state, stored_schedules, pending_responses,
                 generated_responses, response_generator_state, total_processed,
                 successful_schedules, failed_operations>>

CompleteStorageRequest(req, success) ==
  /\ req \in storage_requests  
  /\ req.status = "IN_PROGRESS"
  /\ LET new_status == IF success THEN "COMPLETED" ELSE "FAILED"
         updated_req == [req EXCEPT !.status = new_status]
     IN storage_requests' = (storage_requests \ {req}) \cup {updated_req}
  /\ IF success /\ req.operation = "STORE"
     THEN stored_schedules' = stored_schedules \cup {req.id}
     ELSE UNCHANGED stored_schedules
  /\ vector_storage_state' = "AVAILABLE"
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 calendar_operations, orchestrator_state, pending_schedules,
                 pending_responses, generated_responses, response_generator_state,
                 total_processed, successful_schedules, failed_operations>>

\* Response Generation
GenerateResponse(request_id, status, message) ==
  /\ request_id \in DOMAIN parsed_intents
  /\ response_generator_state = "IDLE"
  /\ LET response == [request_id |-> request_id, status |-> status,
                      message |-> message, data |-> <<>>]
     IN generated_responses' = generated_responses \cup {response}
  /\ response_generator_state' = "GENERATING"
  /\ total_processed' = total_processed + 1
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 calendar_operations, orchestrator_state, pending_schedules,
                 storage_requests, vector_storage_state, stored_schedules,
                 pending_responses, successful_schedules, failed_operations>>

CompleteResponseGeneration ==
  /\ response_generator_state = "GENERATING"
  /\ response_generator_state' = "IDLE"
  /\ orchestrator_state' = "READY"
  /\ UNCHANGED <<nl_requests, parsed_intents, intent_parser_state,
                 calendar_operations, pending_schedules, storage_requests,
                 vector_storage_state, stored_schedules, pending_responses,
                 generated_responses, total_processed, successful_schedules,
                 failed_operations>>

\* System Actions
Next ==
  \/ \E request_id \in RequestID, user \in USERS:
       ReceiveNLRequest(request_id, user, <<1, 2>>)
  \/ \E request_id \in RequestID, intent_type \in INTENT_TYPES,
        resource \in RESOURCES, user \in USERS:
       ParseIntent(request_id, intent_type, resource, user)
  \/ CompleteIntentParsing
  \/ \E request_id \in RequestID, operation_type \in {"CREATE", "UPDATE", "DELETE", "QUERY"},
        resource \in RESOURCES, user \in USERS:
       CreateCalendarOperation(request_id, operation_type, resource, user)
  \/ \E op \in calendar_operations: ProcessCalendarOperation(op)
  \/ \E op \in calendar_operations, success \in BOOLEAN:
       CompleteCalendarOperation(op, success)
  \/ \E schedule_id \in RequestID, operation_type \in {"STORE", "RETRIEVE", "DELETE"}:
       CreateStorageRequest(schedule_id, operation_type)
  \/ \E req \in storage_requests: ProcessStorageRequest(req)
  \/ \E req \in storage_requests, success \in BOOLEAN:
       CompleteStorageRequest(req, success)
  \/ \E request_id \in RequestID, status \in {"SUCCESS", "PARTIAL", "FAILED"}:
       GenerateResponse(request_id, status, <<1, 2>>)
  \/ CompleteResponseGeneration

\* Specification
Spec == Init /\ [][Next]_<<nl_requests, parsed_intents, intent_parser_state,
                           calendar_operations, orchestrator_state, pending_schedules,
                           storage_requests, vector_storage_state, stored_schedules,
                           pending_responses, generated_responses, response_generator_state,
                           total_processed, successful_schedules, failed_operations>>

\* Invariants
SystemCapacityInvariant ==
  /\ Cardinality(nl_requests) <= MAX_REQUESTS
  /\ Cardinality(DOMAIN parsed_intents) <= MAX_PARSED_INTENTS
  /\ Cardinality(calendar_operations) <= MAX_CALENDAR_OPS
  /\ Cardinality(storage_requests) <= MAX_STORAGE_OPS

StateConsistencyInvariant ==
  /\ intent_parser_state \in {"IDLE", "PARSING", "ERROR"}
  /\ orchestrator_state \in {"READY", "ORCHESTRATING", "ERROR"}
  /\ vector_storage_state \in {"AVAILABLE", "BUSY", "ERROR"}
  /\ response_generator_state \in {"IDLE", "GENERATING", "ERROR"}

ProcessingInvariant ==
  /\ total_processed >= 0
  /\ successful_schedules >= 0  
  /\ failed_operations >= 0

StorageConsistencyInvariant ==
  /\ \A schedule_id \in stored_schedules:
       \E op \in calendar_operations:
         /\ op.id = schedule_id
         /\ op.status = "COMPLETED"

\* Temporal Properties
EventuallyProcessed ==
  \A request_id \in 1..MAX_REQUESTS:
    (request_id \in nl_requests) ~> 
    (\E response \in generated_responses: response.request_id = request_id)

SystemAvailability ==
  []<>(orchestrator_state = "READY" /\ vector_storage_state = "AVAILABLE")

ProgressProperty ==
  <>(successful_schedules > 0 \/ failed_operations > 0)

=============================================================================
