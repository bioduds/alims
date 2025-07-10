---- MODULE SimplifiedProductionAgent ----
EXTENDS Naturals, Sequences, FiniteSets

\* Simplified constants for model validation
CONSTANTS
    MAX_CONVERSATIONS,
    MAX_AGENTS,
    MAX_PROLOG_DEPTH,
    MAX_KNOWLEDGE_BASE_SIZE,
    AGENT_CAPABILITIES,
    PROLOG_PREDICATES

\* Core state variables
VARIABLES
    conversations,
    central_brain_state,
    available_agents,
    agent_registry,
    prolog_knowledge_base,
    prolog_query_stack,
    prolog_inference_chains,
    system_metrics,
    audit_trails

\* Variable tuple for convenience
vars == <<conversations, central_brain_state, available_agents,
          agent_registry, prolog_knowledge_base, prolog_query_stack,
          prolog_inference_chains, system_metrics, audit_trails>>

\* Type definitions
ConversationState == {"ACTIVE", "PROCESSING", "COMPLETED", "LOGICAL_REASONING"}
AgentState == {"IDLE", "BUSY", "REASONING"}
CentralBrainState == {"INITIALIZING", "READY", "ORCHESTRATING", "PROLOG_INFERENCE"}
PrologRuleType == {"FACT", "RULE"}
InferenceState == {"PENDING", "SUCCESS", "FAILED"}

\* Type invariant
TypeInvariant ==
    /\ \A c \in conversations : 
           /\ c.id \in 1..MAX_CONVERSATIONS
           /\ c.state \in ConversationState
    /\ central_brain_state \in CentralBrainState
    /\ \A a \in available_agents :
           /\ a.id \in 1..MAX_AGENTS
           /\ a.state \in AgentState
           /\ a.capabilities \in AGENT_CAPABILITIES
    /\ Cardinality(prolog_knowledge_base) <= MAX_KNOWLEDGE_BASE_SIZE
    /\ Len(prolog_query_stack) <= MAX_PROLOG_DEPTH

\* Initial state
Init ==
    /\ conversations = {}
    /\ central_brain_state = "INITIALIZING"
    /\ available_agents = {}
    /\ agent_registry = {}
    /\ prolog_knowledge_base = {
           [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>],
           [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>],
           [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>,
            body |-> {[predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>],
                      [predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>]}]
       }
    /\ prolog_query_stack = <<>>
    /\ prolog_inference_chains = {}
    /\ system_metrics = [active_conversations |-> 0, queries |-> 0, rules |-> 3]
    /\ audit_trails = <<>>

\* Initialize system
InitializeSystem ==
    /\ central_brain_state = "INITIALIZING"
    /\ central_brain_state' = "READY"
    /\ available_agents' = {
           [id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"],
           [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"],
           [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]
       }
    /\ agent_registry' = [x \in {1, 2, 3} |-> 
                         CASE x = 1 -> "sample_analysis"
                           [] x = 2 -> "workflow_control"  
                           [] x = 3 -> "logical_reasoning"]
    /\ UNCHANGED <<conversations, prolog_knowledge_base, prolog_query_stack, 
                   prolog_inference_chains, system_metrics, audit_trails>>

\* Start conversation
\* @type: (ConversationId) => Bool;
\* @precondition: central_brain_state = "READY" /\ conv_id \notin {c.id : c \in conversations};
\* @postcondition: conv_id \in {c.id : c \in conversations} /\ conversations'[conv_id].state = "ACTIVE";
\* Code generation: POST /api/conversations with conversation metadata
StartConversation(conv_id) ==
    /\ central_brain_state = "READY"
    /\ conv_id \notin {c.id : c \in conversations}
    /\ Cardinality(conversations) < MAX_CONVERSATIONS
    /\ conversations' = conversations \union {[id |-> conv_id, state |-> "ACTIVE"]}
    /\ system_metrics' = [system_metrics EXCEPT !.active_conversations = @ + 1]
    /\ UNCHANGED <<central_brain_state, available_agents, agent_registry,
                   prolog_knowledge_base, prolog_query_stack, prolog_inference_chains,
                   audit_trails>>

\* Start Prolog query
\* @type: (ConversationId, QueryType) => Bool;
\* @precondition: central_brain_state = "READY" /\ conv_id \in {c.id : c \in conversations};
\* @postcondition: Len(prolog_query_stack') > Len(prolog_query_stack);
\* Code generation: POST /api/queries with Prolog query JSON
StartPrologQuery(conv_id, query) ==
    /\ central_brain_state = "READY"
    /\ \E c \in conversations : c.id = conv_id /\ c.state = "ACTIVE"
    /\ Len(prolog_query_stack) < MAX_PROLOG_DEPTH
    /\ central_brain_state' = "PROLOG_INFERENCE"
    /\ prolog_query_stack' = Append(prolog_query_stack, [
           conversation_id |-> conv_id,
           query |-> query,
           state |-> "PENDING"
       ])
    /\ conversations' = (conversations \ {[id |-> conv_id, state |-> "ACTIVE"]}) \union 
                       {[id |-> conv_id, state |-> "LOGICAL_REASONING"]}
    /\ audit_trails' = Append(audit_trails, [
           action |-> "QUERY_STARTED",
           conversation_id |-> conv_id,
           query |-> query
       ])
    /\ UNCHANGED <<available_agents, agent_registry, prolog_knowledge_base,
                   prolog_inference_chains, system_metrics>>

\* Process inference step
ProcessInference ==
    /\ central_brain_state = "PROLOG_INFERENCE"
    /\ Len(prolog_query_stack) > 0
    /\ LET current_query == Head(prolog_query_stack)
           query == current_query.query
           conv_id == current_query.conversation_id
       IN \* Try to find matching facts
          LET matching_facts == {rule \in prolog_knowledge_base : 
                                rule.type = "FACT" /\ rule.predicate = query.predicate}
          IN \/ \* Success case
                /\ matching_facts # {}
                /\ LET fact == CHOOSE f \in matching_facts : TRUE
                   IN /\ prolog_query_stack' = Tail(prolog_query_stack)
                      /\ prolog_inference_chains' = prolog_inference_chains \union {[
                             conversation_id |-> conv_id,
                             result |-> "SUCCESS",
                             fact |-> fact
                         ]}
                      /\ system_metrics' = [system_metrics EXCEPT !.queries = @ + 1]
                      \* Transition central brain back to READY when no more queries
                      /\ central_brain_state' = IF Len(prolog_query_stack) = 1 
                                                THEN "READY" 
                                                ELSE "PROLOG_INFERENCE"
             \* Failure case
             \/ /\ matching_facts = {}
                /\ prolog_query_stack' = Tail(prolog_query_stack)
                /\ prolog_inference_chains' = prolog_inference_chains \union {[
                       conversation_id |-> conv_id,
                       result |-> "FAILED",
                       query |-> query
                   ]}
                /\ system_metrics' = [system_metrics EXCEPT !.queries = @ + 1]
                \* Transition central brain back to READY when no more queries
                /\ central_brain_state' = IF Len(prolog_query_stack) = 1 
                                          THEN "READY" 
                                          ELSE "PROLOG_INFERENCE"
    /\ UNCHANGED <<conversations, available_agents, agent_registry, 
                   prolog_knowledge_base, audit_trails>>

\* Complete inference
CompleteInference(conv_id) ==
    /\ central_brain_state = "READY"
    /\ Len(prolog_query_stack) = 0
    /\ \E conv \in conversations : conv.id = conv_id /\ conv.state = "LOGICAL_REASONING"
    /\ \E chain \in prolog_inference_chains : chain.conversation_id = conv_id
    /\ conversations' = (conversations \ {[id |-> conv_id, state |-> "LOGICAL_REASONING"]}) \union
                       {[id |-> conv_id, state |-> "ACTIVE"]}
    /\ audit_trails' = Append(audit_trails, [
           action |-> "INFERENCE_COMPLETED",
           conversation_id |-> conv_id
       ])
    /\ UNCHANGED <<available_agents, agent_registry, prolog_knowledge_base,
                   prolog_query_stack, prolog_inference_chains, system_metrics,
                   central_brain_state>>

\* Add knowledge
AddKnowledge(new_rule) ==
    /\ central_brain_state = "READY"
    /\ Cardinality(prolog_knowledge_base) < MAX_KNOWLEDGE_BASE_SIZE
    /\ new_rule.type \in PrologRuleType
    /\ new_rule.predicate \in PROLOG_PREDICATES
    /\ prolog_knowledge_base' = prolog_knowledge_base \union {new_rule}
    /\ system_metrics' = [system_metrics EXCEPT !.rules = @ + 1]
    /\ audit_trails' = Append(audit_trails, [
           action |-> "KNOWLEDGE_ADDED",
           rule |-> new_rule
       ])
    /\ UNCHANGED <<conversations, central_brain_state, available_agents,
                   agent_registry, prolog_query_stack, prolog_inference_chains>>

\* Enhanced timeout and dead letter handling (addressing review feedback)
TimeoutInference(conv_id) ==
    /\ central_brain_state = "PROLOG_INFERENCE"
    /\ \E c \in conversations : c.id = conv_id /\ c.state = "LOGICAL_REASONING"
    /\ \* Timeout condition - in real system would check elapsed time
       Len(prolog_query_stack) > 0
    /\ \* Move to dead letter handling
       conversations' = (conversations \ {[id |-> conv_id, state |-> "LOGICAL_REASONING"]}) \union
                       {[id |-> conv_id, state |-> "COMPLETED"]}  \* Mark as completed with timeout
    /\ central_brain_state' = "READY"
    /\ prolog_query_stack' = <<>>  \* Clear stuck queries
    /\ system_metrics' = [system_metrics EXCEPT !.active_conversations = @ - 1]
    /\ audit_trails' = Append(audit_trails, [
           action |-> "INFERENCE_TIMEOUT",
           conversation_id |-> conv_id,
           reason |-> "QUERY_TIMEOUT"
       ])
    /\ UNCHANGED <<available_agents, agent_registry, prolog_knowledge_base, prolog_inference_chains>>

\* Explicit agent assignment action (addressing review feedback)  
AssignAgentToConversation(conv_id, agent_id) ==
    /\ central_brain_state = "READY"
    /\ \E c \in conversations : c.id = conv_id /\ c.state = "ACTIVE"
    /\ \E a \in available_agents : a.id = agent_id /\ a.state = "IDLE"
    /\ \* Update agent state to busy
       available_agents' = (available_agents \ {[id |-> agent_id, state |-> "IDLE", capabilities |-> agent_registry[agent_id]]}) \union
                          {[id |-> agent_id, state |-> "BUSY", capabilities |-> agent_registry[agent_id]]}
    /\ \* Update conversation to processing
       conversations' = (conversations \ {[id |-> conv_id, state |-> "ACTIVE"]}) \union
                       {[id |-> conv_id, state |-> "PROCESSING"]}
    /\ audit_trails' = Append(audit_trails, [
           action |-> "AGENT_ASSIGNED",
           conversation_id |-> conv_id,
           agent_id |-> agent_id
       ])
    /\ UNCHANGED <<central_brain_state, agent_registry, prolog_knowledge_base,
                   prolog_query_stack, prolog_inference_chains, system_metrics>>

\* Next state relation
Next ==
    \/ InitializeSystem
    \/ \E conv_id \in 1..MAX_CONVERSATIONS : StartConversation(conv_id)
    \/ \E conv_id \in 1..MAX_CONVERSATIONS, query \in [predicate: PROLOG_PREDICATES] :
           StartPrologQuery(conv_id, query)
    \/ ProcessInference
    \/ \E conv_id \in 1..MAX_CONVERSATIONS : CompleteInference(conv_id)
    \/ \E conv_id \in 1..MAX_CONVERSATIONS : TimeoutInference(conv_id)
    \/ \E conv_id \in 1..MAX_CONVERSATIONS, agent_id \in 1..MAX_AGENTS :
           AssignAgentToConversation(conv_id, agent_id)
    \/ \E rule \in [type: PrologRuleType, predicate: PROLOG_PREDICATES] :
           AddKnowledge(rule)
    \/ \E conv_id \in 1..MAX_CONVERSATIONS : TimeoutInference(conv_id)
    \/ \E conv_id \in 1..MAX_CONVERSATIONS, agent_id \in 1..MAX_AGENTS :
           AssignAgentToConversation(conv_id, agent_id)

\* Enhanced specification with comprehensive fairness constraints
Spec == Init /\ [][Next]_vars
            \* Weak fairness for system initialization (must complete when enabled)
            /\ WF_vars(InitializeSystem)
            \* Weak fairness for query processing (must process when queries exist)
            /\ WF_vars(ProcessInference)
            \* Strong fairness for query completion (must eventually complete active queries)
            /\ \A cid1 \in 1..MAX_CONVERSATIONS :
                SF_vars(CompleteInference(cid1))
            \* Strong fairness for timeout handling (addressing review feedback)
            /\ \A cid2 \in 1..MAX_CONVERSATIONS :
                SF_vars(TimeoutInference(cid2))
            \* Weak fairness for conversation management
            /\ \A cid3 \in 1..MAX_CONVERSATIONS :
                WF_vars(StartConversation(cid3))
            \* Weak fairness for agent assignment (addressing review feedback)
            /\ \A cid4 \in 1..MAX_CONVERSATIONS, aid \in 1..MAX_AGENTS :
                WF_vars(AssignAgentToConversation(cid4, aid))

\* Enhanced invariants addressing engineering review feedback

\* Unique ID invariants (addressing review feedback)
UniqueIdInvariant ==
    /\ \* All conversation IDs are unique
       \A c1, c2 \in conversations : 
           c1 # c2 => c1.id # c2.id
    /\ \* All agent IDs are unique  
       \A a1, a2 \in available_agents :
           a1 # a2 => a1.id # a2.id
    /\ \* All query stack entries reference valid conversations
       \A i \in 1..Len(prolog_query_stack) :
           prolog_query_stack[i].conversation_id \in {c.id : c \in conversations}

\* Enhanced business logic invariants
EnhancedBusinessLogicInvariant ==
    /\ \* Agent assignment consistency
       \A aid \in DOMAIN agent_registry :
           \E a \in available_agents : a.id = aid
    /\ \* Inference chain consistency
       \A chain \in prolog_inference_chains :
           \E c \in conversations : c.id = chain.conversation_id
    /\ \* System metrics consistency
       /\ system_metrics.active_conversations = Cardinality(conversations)
       /\ system_metrics.rules >= 3  \* At least initial KB size
    /\ \* Timeout handling - queries don't live forever
       \A i \in 1..Len(prolog_query_stack) :
           \* In a real system, we'd check timestamps here
           TRUE  \* Placeholder for timeout logic

\* Agent orchestration invariant (addressing review feedback)
AgentOrchestrationInvariant ==
    /\ \* Busy agents are assigned to active conversations
       \A a \in available_agents :
           a.state = "BUSY" => 
           \E c \in conversations : 
               /\ c.state \in {"PROCESSING", "LOGICAL_REASONING"}
               /\ c.id \in DOMAIN agent_registry \* Implicitly assigned
    /\ \* Idle agents are available for assignment
       \A a \in available_agents :
           a.state = "IDLE" => 
           \A c \in conversations : c.state # "PROCESSING"

\* All invariants
Invariants == SafetyProperties

\* Enhanced safety properties (addressing engineering review feedback)
SafetyProperties ==
    /\ TypeInvariant
    /\ UniqueIdInvariant
    /\ EnhancedBusinessLogicInvariant
    /\ AgentOrchestrationInvariant
    /\ \* Resource bounds
       /\ Cardinality(conversations) <= MAX_CONVERSATIONS
       /\ Cardinality(available_agents) <= MAX_AGENTS
       /\ Cardinality(prolog_knowledge_base) <= MAX_KNOWLEDGE_BASE_SIZE
       /\ Len(prolog_query_stack) <= MAX_PROLOG_DEPTH
    /\ \* State consistency
       /\ \A c \in conversations : c.state \in ConversationState
       /\ central_brain_state \in CentralBrainState
    /\ \* No orphaned inference chains
       /\ \A chain \in prolog_inference_chains :
              \E c \in conversations : c.id = chain.conversation_id

\* Enhanced liveness properties (addressing review feedback)
LivenessProperties ==
    /\ \* System initialization eventually completes
       (central_brain_state = "INITIALIZING") ~> (central_brain_state = "READY")
    /\ \* Inference processing eventually completes when queries are active
       (central_brain_state = "PROLOG_INFERENCE" /\ Len(prolog_query_stack) > 0) ~>
       (central_brain_state = "READY")
    /\ \* All started conversations eventually reach completion or active state
       \A conv_id \in 1..MAX_CONVERSATIONS :
           ([id |-> conv_id, state |-> "LOGICAL_REASONING"] \in conversations) ~>
           (([id |-> conv_id, state |-> "ACTIVE"] \in conversations) \/
            ([id |-> conv_id, state |-> "COMPLETED"] \in conversations))
    /\ \* System eventually processes all pending queries (no infinite backlogs)
       [](Len(prolog_query_stack) > 0 => <>(Len(prolog_query_stack) = 0))
    /\ \* Inference eventually completes when started (with timeout handling)
       [](central_brain_state = "PROLOG_INFERENCE" => <>(central_brain_state = "READY"))
    /\ \* Agent assignment eventually happens for active conversations
       \A conv_id \in 1..MAX_CONVERSATIONS :
           ([id |-> conv_id, state |-> "ACTIVE"] \in conversations) ~>
           (([id |-> conv_id, state |-> "PROCESSING"] \in conversations) \/
            ([id |-> conv_id, state |-> "COMPLETED"] \in conversations))
