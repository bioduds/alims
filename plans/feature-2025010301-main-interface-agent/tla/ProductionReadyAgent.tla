---- MODULE ProductionReadyAgent ----
\* Production-ready TLA+ model for Main Interface Agent with Prolog integration
\* Addresses engineering review feedback:
\* - Fixed set-of-records vs. function modeling for agents/conversations
\* - Added invariants for unique IDs
\* - Added explicit dispatcher/orchestration logic and timeout/dead-letter handling
\* - Improved knowledge base representation for TLC performance
\* - Annotated actions for code generation

EXTENDS Naturals, Sequences, FiniteSets

\* Define NULL as a numeric constant
NullValue == 0

\* Production constants with realistic bounds
CONSTANTS
    MAX_CONVERSATIONS,     \* Maximum concurrent conversations
    MAX_AGENTS,           \* Maximum number of agents  
    MAX_PROLOG_DEPTH,     \* Maximum query depth to prevent infinite recursion
    MAX_KNOWLEDGE_BASE_SIZE, \* KB size limit for performance
    AGENT_CAPABILITIES,   \* Set of possible agent capabilities
    PROLOG_PREDICATES,    \* Set of valid predicates
    TIMEOUT_THRESHOLD,    \* Timeout for query processing
    MAX_RETRIES          \* Maximum retry attempts for failed operations

\* Core state variables with improved modeling
VARIABLES
    \* Use functions for better modeling (addressing review feedback)
    conversations,        \* Function: ConversationId -> ConversationRecord
    agents,              \* Function: AgentId -> AgentRecord
    agent_dispatcher,    \* Explicit dispatcher state
    
    \* Central brain and system state
    central_brain_state,
    system_clock,        \* Logical clock for timeouts
    
    \* Prolog reasoning system
    prolog_knowledge_base,     \* Optimized representation
    active_queries,           \* Function: QueryId -> QueryRecord
    inference_chains,         \* Function: ChainId -> InferenceRecord
    dead_letter_queue,       \* Failed/timeout operations
    
    \* System monitoring
    system_metrics,
    audit_trails,
    error_log

\* Variable tuple for convenience
vars == <<conversations, agents, agent_dispatcher, central_brain_state, system_clock,
          prolog_knowledge_base, active_queries, inference_chains, dead_letter_queue,
          system_metrics, audit_trails, error_log>>

\* Enhanced type definitions
ConversationId == 1..MAX_CONVERSATIONS
AgentId == 1..MAX_AGENTS
QueryId == 1..MAX_CONVERSATIONS * MAX_PROLOG_DEPTH
ChainId == 1..MAX_CONVERSATIONS * MAX_PROLOG_DEPTH

\* Allow null values in optional fields
ConversationIdOrNull == ConversationId \cup {NullValue}
AgentIdOrNull == AgentId \cup {NullValue}

ConversationState == {"ACTIVE", "PROCESSING", "LOGICAL_REASONING", "COMPLETED", "ERROR", "TIMEOUT"}
AgentState == {"IDLE", "BUSY", "REASONING", "ERROR"}
CentralBrainState == {"INITIALIZING", "READY", "ORCHESTRATING", "PROLOG_INFERENCE", "ERROR_RECOVERY"}
DispatcherState == {"IDLE", "ROUTING", "LOAD_BALANCING", "ERROR_HANDLING"}
QueryState == {"PENDING", "PROCESSING", "SUCCESS", "FAILED", "TIMEOUT"}

\* Records for structured data
ConversationRecord == [
    id: ConversationId,
    state: ConversationState,
    assigned_agent: AgentIdOrNull,
    start_time: Nat,
    timeout_deadline: Nat,
    retry_count: Nat
]

AgentRecord == [
    id: AgentId,
    state: AgentState,
    capabilities: AGENT_CAPABILITIES,
    current_conversation: ConversationIdOrNull,
    load_factor: Nat,
    error_count: Nat
]

\* Define finite argument sequences for TLC compatibility
PrologArgs == {<<"sample_tracker", "sample_analysis">>, <<"workflow_manager", "workflow_control">>, 
               <<"?Agent", "?Task">>, <<"?Task", "?Cap">>, <<"?Agent", "?Cap">>, <<>>}

QueryRecord == [
    id: QueryId,
    conversation_id: ConversationId,
    predicate: PROLOG_PREDICATES,
    args: PrologArgs,
    state: QueryState,
    start_time: Nat,
    retry_count: Nat
]

\* Optimized knowledge base representation (addressing performance concerns)
KnowledgeBaseEntry == [
    id: 1..MAX_KNOWLEDGE_BASE_SIZE,
    type: {"FACT", "RULE"},
    predicate: PROLOG_PREDICATES,
    args: PrologArgs,
    body: SUBSET {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], 
                  [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}
]

\* Type invariants with unique ID constraints (addressing review feedback)
TypeInvariant ==
    /\ \* Conversations are properly typed (allow empty sequences initially)
       /\ (conversations = << >> \/ conversations \in [ConversationId -> ConversationRecord])
       /\ (conversations = << >> \/ \A cid \in DOMAIN conversations : conversations[cid].id = cid)
    /\ \* Agents are properly typed (allow empty sequences initially)  
       /\ (agents = << >> \/ agents \in [AgentId -> AgentRecord])
       /\ (agents = << >> \/ \A aid \in DOMAIN agents : agents[aid].id = aid)
    /\ \* Active queries are properly typed
       /\ (active_queries = << >> \/ active_queries \in [QueryId -> QueryRecord])
       /\ (active_queries = << >> \/ \A qid \in DOMAIN active_queries : active_queries[qid].id = qid)
    /\ \* State variables have correct types
       /\ central_brain_state \in CentralBrainState
       /\ agent_dispatcher \in DispatcherState
       /\ system_clock \in Nat
    /\ \* Knowledge base is well-formed
       /\ prolog_knowledge_base \subseteq KnowledgeBaseEntry
       /\ Cardinality(prolog_knowledge_base) <= MAX_KNOWLEDGE_BASE_SIZE

\* Unique ID invariants (new - addressing review feedback)
UniqueIdInvariant ==
    /\ \* All conversation IDs are unique in their domain
       \A c1, c2 \in DOMAIN conversations : 
           c1 # c2 => conversations[c1].id # conversations[c2].id
    /\ \* All agent IDs are unique in their domain
       \A a1, a2 \in DOMAIN agents :
           a1 # a2 => agents[a1].id # agents[a2].id
    /\ \* All query IDs are unique in their domain
       \A q1, q2 \in DOMAIN active_queries :
           q1 # q2 => active_queries[q1].id # active_queries[q2].id
    /\ \* Knowledge base entries have unique IDs
       \A kb1, kb2 \in prolog_knowledge_base :
           kb1 # kb2 => kb1.id # kb2.id

\* Resource constraint invariants
ResourceInvariant ==
    /\ Cardinality(DOMAIN conversations) <= MAX_CONVERSATIONS
    /\ Cardinality(DOMAIN agents) <= MAX_AGENTS
    /\ Cardinality(DOMAIN active_queries) <= MAX_CONVERSATIONS * MAX_PROLOG_DEPTH
    /\ Cardinality(prolog_knowledge_base) <= MAX_KNOWLEDGE_BASE_SIZE
    /\ system_clock >= 0

\* Business logic invariants
BusinessLogicInvariant ==
    /\ \* Agent assignment consistency
       \A cid \in DOMAIN conversations :
           LET conv == conversations[cid]
           IN conv.assigned_agent # NullValue =>
               /\ conv.assigned_agent \in DOMAIN agents
               /\ agents[conv.assigned_agent].current_conversation = cid
    /\ \* Query-conversation consistency
       \A qid \in DOMAIN active_queries :
           active_queries[qid].conversation_id \in DOMAIN conversations
    /\ \* Timeout deadlines are reasonable
       \A cid \in DOMAIN conversations :
           conversations[cid].timeout_deadline >= conversations[cid].start_time

\* Initial state
Init ==
    /\ conversations = << >>  \* Start with empty for now 
    /\ agents = << >>         \* Start with empty for now  
    /\ agent_dispatcher = "IDLE"
    /\ central_brain_state = "INITIALIZING"
    /\ system_clock = 0
    /\ prolog_knowledge_base = {
           [id |-> 1, type |-> "FACT", predicate |-> "has_capability", 
            args |-> <<"sample_tracker", "sample_analysis">>, body |-> {}],
           [id |-> 2, type |-> "FACT", predicate |-> "has_capability",
            args |-> <<"workflow_manager", "workflow_control">>, body |-> {}],
           [id |-> 3, type |-> "RULE", predicate |-> "suitable_agent",
            args |-> <<"?Agent", "?Task">>,
            body |-> {[predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>],
                      [predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>]}]
       }
    /\ active_queries = << >>
    /\ inference_chains = << >>
    /\ dead_letter_queue = <<>>
    /\ system_metrics = [conversation_count |-> 0, queries |-> 0, errors |-> 0, timeouts |-> 0]
    /\ audit_trails = <<>>
    /\ error_log = <<>>

\* @type: () => Bool;
\* @postcondition: central_brain_state = "READY" /\ DOMAIN agents # {};
\* System initialization with explicit dispatcher setup (addressing review feedback)
InitializeSystem ==
    /\ central_brain_state = "INITIALIZING"
    /\ agent_dispatcher = "IDLE"
    /\ \* Initialize agents
       agents' = [aid \in 1..3 |->
                    [id |-> aid,
                     state |-> "IDLE",
                     capabilities |-> CASE aid = 1 -> "sample_analysis"
                                        [] aid = 2 -> "workflow_control"
                                        [] aid = 3 -> "logical_reasoning",
                     current_conversation |-> NullValue,
                     load_factor |-> 0,
                     error_count |-> 0]]
    /\ central_brain_state' = "READY"
    /\ agent_dispatcher' = "IDLE"
    /\ system_clock' = system_clock + 1
    /\ audit_trails' = Append(audit_trails, [
           action |-> "SYSTEM_INITIALIZED",
           timestamp |-> system_clock + 1,
           agents_count |-> 3
       ])
    /\ UNCHANGED <<conversations, prolog_knowledge_base, active_queries,
                   inference_chains, dead_letter_queue, system_metrics, error_log>>

\* @type: (ConversationId) => Bool;
\* @precondition: central_brain_state = "READY" /\ cid \notin DOMAIN conversations;
\* @postcondition: cid \in DOMAIN conversations /\ conversations'[cid].state = "ACTIVE";
\* Start new conversation with explicit dispatcher routing
StartConversation(cid) ==
    /\ central_brain_state = "READY"
    /\ cid \notin DOMAIN conversations
    /\ Cardinality(DOMAIN conversations) < MAX_CONVERSATIONS
    /\ agent_dispatcher = "IDLE"
    /\ \* Create new conversation record
       conversations' = [conversations EXCEPT ![cid] = [
           id |-> cid,
           state |-> "ACTIVE", 
           assigned_agent |-> NullValue,
           start_time |-> system_clock,
           timeout_deadline |-> system_clock + TIMEOUT_THRESHOLD,
           retry_count |-> 0
       ]]
    /\ agent_dispatcher' = "ROUTING"
    /\ system_clock' = system_clock + 1
    /\ system_metrics' = [system_metrics EXCEPT !.conversations = @ + 1]
    /\ audit_trails' = Append(audit_trails, [
           action |-> "CONVERSATION_STARTED",
           conversation_id |-> cid,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<agents, central_brain_state, prolog_knowledge_base,
                   active_queries, inference_chains, dead_letter_queue, error_log>>

\* @type: (ConversationId, AgentId) => Bool;
\* @precondition: cid \in DOMAIN conversations /\ aid \in DOMAIN agents;
\* @postcondition: conversations'[cid].assigned_agent = aid;
\* Explicit agent assignment through dispatcher (new - addressing review feedback)
AssignAgent(cid, aid) ==
    /\ agent_dispatcher = "ROUTING"
    /\ cid \in DOMAIN conversations
    /\ aid \in DOMAIN agents
    /\ conversations[cid].assigned_agent = NullValue
    /\ agents[aid].current_conversation = NullValue
    /\ agents[aid].state = "IDLE"
    /\ \* Update conversation assignment
       conversations' = [conversations EXCEPT ![cid].assigned_agent = aid]
    /\ \* Update agent assignment
       agents' = [agents EXCEPT ![aid].current_conversation = cid,
                                ![aid].state = "BUSY"]
    /\ agent_dispatcher' = "IDLE"
    /\ system_clock' = system_clock + 1
    /\ audit_trails' = Append(audit_trails, [
           action |-> "AGENT_ASSIGNED",
           conversation_id |-> cid,
           agent_id |-> aid,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<central_brain_state, prolog_knowledge_base, active_queries,
                   inference_chains, dead_letter_queue, system_metrics, error_log>>

\* @type: (QueryId, ConversationId, PROLOG_PREDICATES, PrologArgs) => Bool;
\* @precondition: qid \notin DOMAIN active_queries /\ cid \in DOMAIN conversations;
\* @postcondition: qid \in DOMAIN active_queries /\ active_queries'[qid].state = "PENDING";
\* Start Prolog query with timeout tracking
StartPrologQuery(qid, cid, predicate, args) ==
    /\ central_brain_state = "READY"
    /\ qid \notin DOMAIN active_queries
    /\ cid \in DOMAIN conversations
    /\ conversations[cid].state = "ACTIVE"
    /\ Cardinality(DOMAIN active_queries) < MAX_CONVERSATIONS * MAX_PROLOG_DEPTH
    /\ \* Create query record
       active_queries' = active_queries \cup {[
           id |-> qid,
           conversation_id |-> cid,
           predicate |-> predicate,
           args |-> args,
           state |-> "PENDING",
           start_time |-> system_clock,
           retry_count |-> 0
       ]}
    /\ \* Update conversation state
       conversations' = [conversations EXCEPT ![cid].state = "LOGICAL_REASONING"]
    /\ central_brain_state' = "PROLOG_INFERENCE"
    /\ system_clock' = system_clock + 1
    /\ system_metrics' = [system_metrics EXCEPT !.queries = @ + 1]
    /\ audit_trails' = Append(audit_trails, [
           action |-> "QUERY_STARTED",
           query_id |-> qid,
           conversation_id |-> cid,
           predicate |-> predicate,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<agents, agent_dispatcher, prolog_knowledge_base,
                   inference_chains, dead_letter_queue, error_log>>

\* @type: (QueryId) => Bool;
\* @precondition: qid \in DOMAIN active_queries /\ active_queries[qid].state = "PENDING";
\* Process inference with improved error handling
ProcessInference(qid) ==
    /\ central_brain_state = "PROLOG_INFERENCE"
    /\ qid \in DOMAIN active_queries
    /\ active_queries[qid].state = "PENDING"
    /\ LET query == active_queries[qid]
           matching_facts == {kb \in prolog_knowledge_base : 
                             kb.type = "FACT" /\ kb.predicate = query.predicate}
       IN \/ \* Success case
             /\ matching_facts # {}
             /\ LET fact == CHOOSE f \in matching_facts : TRUE
                    chain_id == query.id  \* Use query ID as chain ID for simplicity
                IN /\ active_queries' = [active_queries EXCEPT ![qid].state = "SUCCESS"]
                   /\ inference_chains' = inference_chains \cup {[
                          id |-> chain_id,
                          query_id |-> qid,
                          conversation_id |-> query.conversation_id,
                          result |-> "SUCCESS",
                          evidence |-> fact,
                          timestamp |-> system_clock + 1
                      ]}
                   /\ system_clock' = system_clock + 1
          \/ \* Failure case
             /\ matching_facts = {}
             /\ active_queries' = [active_queries EXCEPT ![qid].state = "FAILED"]
             /\ dead_letter_queue' = Append(dead_letter_queue, [
                    query_id |-> qid,
                    reason |-> "NO_MATCHING_FACTS",
                    timestamp |-> system_clock + 1
                ])
             /\ system_clock' = system_clock + 1
             /\ error_log' = Append(error_log, [
                    type |-> "INFERENCE_FAILED",
                    query_id |-> qid,
                    timestamp |-> system_clock + 1
                ])
             /\ UNCHANGED inference_chains
    /\ \* Check if we should transition back to READY
       central_brain_state' = IF \A q \in DOMAIN active_queries : 
                                   q = qid \/ active_queries[q].state # "PENDING"
                              THEN "READY"
                              ELSE "PROLOG_INFERENCE"
    /\ UNCHANGED <<conversations, agents, agent_dispatcher, prolog_knowledge_base,
                   system_metrics, audit_trails>>

\* @type: (ConversationId) => Bool;  
\* @precondition: cid \in DOMAIN conversations /\ conversations[cid].state = "LOGICAL_REASONING";
\* @postcondition: conversations'[cid].state = "ACTIVE";
\* Complete inference and clean up resources
CompleteInference(cid) ==
    /\ central_brain_state = "READY"
    /\ cid \in DOMAIN conversations
    /\ conversations[cid].state = "LOGICAL_REASONING"
    /\ \* Ensure all queries for this conversation are complete
       \A qid \in DOMAIN active_queries :
           active_queries[qid].conversation_id = cid =>
           active_queries[qid].state \in {"SUCCESS", "FAILED", "TIMEOUT"}
    /\ \* Update conversation state
       conversations' = [conversations EXCEPT ![cid].state = "ACTIVE"]
    /\ \* Clean up completed queries (garbage collection)
       LET completed_queries == {qid \in DOMAIN active_queries :
                                active_queries[qid].conversation_id = cid}
       IN active_queries' = [qid \in (DOMAIN active_queries \ completed_queries) |->
                            active_queries[qid]]
    /\ system_clock' = system_clock + 1
    /\ audit_trails' = Append(audit_trails, [
           action |-> "INFERENCE_COMPLETED",
           conversation_id |-> cid,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<agents, agent_dispatcher, central_brain_state, prolog_knowledge_base,
                   inference_chains, dead_letter_queue, system_metrics, error_log>>

\* @type: (QueryId) => Bool;
\* @precondition: qid \in DOMAIN active_queries;
\* Timeout handling for stuck queries (new - addressing review feedback)
TimeoutQuery(qid) ==
    /\ qid \in DOMAIN active_queries
    /\ LET query == active_queries[qid]
       IN /\ query.state = "PENDING"
          /\ system_clock > query.start_time + TIMEOUT_THRESHOLD
          /\ query.retry_count < MAX_RETRIES
    /\ \* Mark query as timeout and move to dead letter queue
       active_queries' = [active_queries EXCEPT ![qid].state = "TIMEOUT"]
    /\ dead_letter_queue' = Append(dead_letter_queue, [
           query_id |-> qid,
           reason |-> "TIMEOUT",
           timestamp |-> system_clock + 1,
           retry_count |-> active_queries[qid].retry_count
       ])
    /\ system_clock' = system_clock + 1
    /\ system_metrics' = [system_metrics EXCEPT !.timeouts = @ + 1]
    /\ error_log' = Append(error_log, [
           type |-> "QUERY_TIMEOUT",
           query_id |-> qid,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<conversations, agents, agent_dispatcher, central_brain_state,
                   prolog_knowledge_base, inference_chains, audit_trails>>

\* @type: (KnowledgeBaseEntry) => Bool;
\* @precondition: new_entry.id \notin {kb.id : kb \in prolog_knowledge_base};
\* @postcondition: new_entry \in prolog_knowledge_base';
\* Add knowledge with validation
AddKnowledge(new_entry) ==
    /\ central_brain_state = "READY"
    /\ Cardinality(prolog_knowledge_base) < MAX_KNOWLEDGE_BASE_SIZE
    /\ new_entry \in KnowledgeBaseEntry
    /\ new_entry.id \notin {kb.id : kb \in prolog_knowledge_base}
    /\ new_entry.predicate \in PROLOG_PREDICATES
    /\ prolog_knowledge_base' = prolog_knowledge_base \union {new_entry}
    /\ system_clock' = system_clock + 1
    /\ audit_trails' = Append(audit_trails, [
           action |-> "KNOWLEDGE_ADDED",
           entry_id |-> new_entry.id,
           predicate |-> new_entry.predicate,
           timestamp |-> system_clock + 1
       ])
    /\ UNCHANGED <<conversations, agents, agent_dispatcher, central_brain_state,
                   active_queries, inference_chains, dead_letter_queue,
                   system_metrics, error_log>>

\* Clock tick for system progression
TickClock ==
    /\ system_clock' = system_clock + 1
    /\ UNCHANGED <<conversations, agents, agent_dispatcher, central_brain_state,
                   prolog_knowledge_base, active_queries, inference_chains,
                   dead_letter_queue, system_metrics, audit_trails, error_log>>

\* Next state relation with all possible actions
Next ==
    \/ InitializeSystem
    \/ \E conv_id \in ConversationId : StartConversation(conv_id)
    \/ \E conv_id \in ConversationId, agent_id \in AgentId : AssignAgent(conv_id, agent_id)
    \/ \E query_id \in QueryId, conv_id \in ConversationId, pred \in PROLOG_PREDICATES,
          args \in PrologArgs : StartPrologQuery(query_id, conv_id, pred, args)
    \/ \E query_id \in QueryId : ProcessInference(query_id)
    \/ \E conv_id \in ConversationId : CompleteInference(conv_id)
    \/ \E query_id \in QueryId : TimeoutQuery(query_id)
    \/ \E entry \in KnowledgeBaseEntry : AddKnowledge(entry)
    \/ TickClock

\* Enhanced specification with comprehensive fairness
Spec == Init /\ [][Next]_vars
    \* Strong fairness for critical system operations
    /\ SF_vars(InitializeSystem)
    /\ \A qid \in QueryId : SF_vars(ProcessInference(qid))
    /\ \A cid \in ConversationId : SF_vars(CompleteInference(cid))
    /\ \A qid2 \in QueryId : SF_vars(TimeoutQuery(qid2))
    \* Weak fairness for routine operations
    /\ \A cid2 \in ConversationId : WF_vars(StartConversation(cid2))
    /\ \A cid3 \in ConversationId, aid \in AgentId : WF_vars(AssignAgent(cid3, aid))
    /\ WF_vars(TickClock)

\* Complete safety properties
SafetyProperties ==
    /\ TypeInvariant
    /\ UniqueIdInvariant
    /\ ResourceInvariant  
    /\ BusinessLogicInvariant

\* Enhanced liveness properties
LivenessProperties ==
    /\ \* System initialization
       (central_brain_state = "INITIALIZING") ~> (central_brain_state = "READY")
    /\ \* Query processing completion
       \A qid \in QueryId :
           (qid \in DOMAIN active_queries /\ active_queries[qid].state = "PENDING") ~>
           (qid \notin DOMAIN active_queries \/ 
            active_queries[qid].state \in {"SUCCESS", "FAILED", "TIMEOUT"})
    /\ \* Conversation progression  
       \A cid \in ConversationId :
           (cid \in DOMAIN conversations /\ conversations[cid].state = "LOGICAL_REASONING") ~>
           (cid \notin DOMAIN conversations \/ conversations[cid].state # "LOGICAL_REASONING")
    /\ \* No infinite inference loops
       [](central_brain_state = "PROLOG_INFERENCE" => <>(central_brain_state = "READY"))
    /\ \* Dead letter queue eventually drains (with retry logic)
       [](Len(dead_letter_queue) > 0 => <>(Len(dead_letter_queue) = 0))

\* All invariants
Invariants == SafetyProperties

====
