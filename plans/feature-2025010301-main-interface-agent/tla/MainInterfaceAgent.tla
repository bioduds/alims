---- MODULE MainInterfaceAgent ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Constants
CONSTANTS
    MAX_CONVERSATIONS,      \* Maximum concurrent conversations
    MAX_AGENTS,            \* Maximum number of specialized agents
    MAX_CONTEXT_DEPTH,     \* Maximum context tracking depth
    AGENT_CAPABILITIES,    \* Set of possible agent capabilities
    MESSAGE_CONTENTS,      \* Set of possible message contents
    ERROR_TYPES           \* Set of possible error types

\* State variables
VARIABLES
    conversations,         \* Set of active conversations
    central_brain_state,   \* State of the central brain orchestrator  
    available_agents,      \* Pool of available specialized agents
    agent_registry,        \* Registry mapping capabilities to agents
    conversation_contexts, \* Context tracking for each conversation
    user_requests,         \* Queue of pending user requests
    agent_responses,       \* Queue of responses from specialized agents
    system_metrics        \* Performance and health metrics

\* Type definitions
ConversationState == {"ACTIVE", "WAITING_AGENT", "PROCESSING", "COMPLETED", "ESCALATED"}
AgentState == {"IDLE", "BUSY", "ERROR", "OFFLINE"}
CentralBrainState == {"INITIALIZING", "READY", "ORCHESTRATING", "ERROR"}
RequestType == {"SAMPLE_INQUIRY", "WORKFLOW_COMMAND", "SYSTEM_QUERY", "AGENT_REQUEST"}
Priority == {"LOW", "MEDIUM", "HIGH", "CRITICAL"}

\* Type invariants
TypeInvariant ==
    /\ \A c \in conversations : 
           /\ c[1] \in 1..MAX_CONVERSATIONS     \* conversation ID
           /\ c[2] \in ConversationState        \* conversation state
           /\ c[3] \in 0..MAX_CONTEXT_DEPTH     \* turn count (bounded)
    /\ central_brain_state \in CentralBrainState
    /\ \A a \in available_agents : 
           /\ a[1] \in 1..MAX_AGENTS           \* agent ID  
           /\ a[2] \in AgentState              \* agent state
           /\ a[3] \in AGENT_CAPABILITIES      \* capabilities
    /\ Len(user_requests) <= MAX_CONVERSATIONS * 10
    /\ Len(agent_responses) <= MAX_AGENTS * 10

\* Initial state
Init ==
    /\ conversations = {}
    /\ central_brain_state = "INITIALIZING"
    /\ available_agents = {}
    /\ agent_registry = [x \in {} |-> ""]
    /\ conversation_contexts = [c \in {} |-> {}]
    /\ user_requests = <<>>
    /\ agent_responses = <<>>
    /\ system_metrics = [active_conversations |-> 0, response_time |-> 0]

\* Helper functions
GetActiveConversations == {c \in conversations : c[2] = "ACTIVE"}
GetAvailableAgents == {a \in available_agents : a[2] = "IDLE"}
GetConversationById(id) == CHOOSE c \in conversations : c[1] = id

\* Actions

\* Central Brain initialization and agent setup
InitializeCentralBrain ==
    /\ central_brain_state = "INITIALIZING"
    /\ central_brain_state' = "READY"
    /\ \* Register some basic agents during initialization
       available_agents' = {
           <<1, "IDLE", "sample_tracker">>,
           <<2, "IDLE", "workflow_manager">>
       }
    /\ agent_registry' = agent_registry @@ (1 :> "sample_tracker") @@ (2 :> "workflow_manager")
    /\ UNCHANGED <<conversations, conversation_contexts, user_requests, 
                   agent_responses, system_metrics>>

\* Register a new specialized agent
RegisterAgent(agent_id, capabilities) ==
    /\ central_brain_state = "READY"
    /\ agent_id \notin DOMAIN agent_registry
    /\ Cardinality(available_agents) < MAX_AGENTS
    /\ LET new_agent == <<agent_id, "IDLE", capabilities>>
       IN available_agents' = available_agents \union {new_agent}
    /\ agent_registry' = agent_registry @@ (agent_id :> capabilities)
    /\ UNCHANGED <<conversations, central_brain_state, conversation_contexts,
                   user_requests, agent_responses, system_metrics>>

\* Start new conversation with user
StartConversation(conv_id) ==
    /\ central_brain_state = "READY"
    /\ conv_id \notin {c[1] : c \in conversations}
    /\ Cardinality(conversations) < MAX_CONVERSATIONS
    /\ LET new_conv == <<conv_id, "ACTIVE", 0>>
       IN conversations' = conversations \union {new_conv}
    /\ conversation_contexts' = conversation_contexts @@ (conv_id :> [
           messages |-> <<>>,
           current_context |-> {},
           active_agents |-> {},
           user_intent |-> "UNKNOWN"
       ])
    /\ system_metrics' = [system_metrics EXCEPT 
           !.active_conversations = @ + 1]
    /\ UNCHANGED <<central_brain_state, available_agents, agent_registry,
                   user_requests, agent_responses>>

\* Receive user request
ReceiveUserRequest(conv_id, request_type, content, priority) ==
    /\ \E c \in conversations : c[1] = conv_id /\ c[2] = "ACTIVE"
    /\ Len(user_requests) < MAX_CONVERSATIONS * 10
    /\ user_requests' = Append(user_requests, [
           conversation_id |-> conv_id,
           type |-> request_type,
           content |-> content,
           priority |-> priority,
           timestamp |-> 1  \* Abstract timestamp
       ])
    /\ conversation_contexts' = [conversation_contexts EXCEPT 
           ![conv_id].messages = Append(@, [
               role |-> "user",
               content |-> content,
               timestamp |-> 1
           ])]
    /\ UNCHANGED <<conversations, central_brain_state, available_agents,
                   agent_registry, agent_responses, system_metrics>>

\* Central Brain analyzes request and determines which agents to orchestrate
AnalyzeAndOrchestrate ==
    /\ Len(user_requests) > 0
    /\ central_brain_state = "READY"
    /\ central_brain_state' = "ORCHESTRATING"
    /\ LET request == Head(user_requests)
           conv_id == request.conversation_id
           required_capabilities == CASE request.type = "SAMPLE_INQUIRY" -> {"sample_tracker", "workflow_manager"}
                                    [] request.type = "WORKFLOW_COMMAND" -> {"workflow_manager", "lims_coordinator"}
                                    [] request.type = "SYSTEM_QUERY" -> {"system_monitor"}
                                    [] OTHER -> {}
           idle_agents_with_caps == {agent \in available_agents : 
                                        agent[2] = "IDLE" /\ agent[3] \in required_capabilities}
           suitable_agents == {agent[1] : agent \in idle_agents_with_caps}
       IN /\ conversation_contexts' = [conversation_contexts EXCEPT
                 ![conv_id].user_intent = request.type,
                 ![conv_id].active_agents = suitable_agents]
          /\ user_requests' = Tail(user_requests)
    /\ UNCHANGED <<conversations, available_agents, agent_registry, 
                   agent_responses, system_metrics>>

\* Route request to appropriate specialized agent
RouteToAgent(agent_id, request_content) ==
    /\ central_brain_state = "ORCHESTRATING"
    /\ \E a \in available_agents : a[1] = agent_id /\ a[2] = "IDLE"
    /\ \E conv_id \in DOMAIN conversation_contexts : 
           agent_id \in conversation_contexts[conv_id].active_agents
    /\ LET old_agent == CHOOSE a \in available_agents : a[1] = agent_id /\ a[2] = "IDLE"
           new_agent == <<agent_id, "BUSY", old_agent[3]>>
       IN available_agents' = (available_agents \ {old_agent}) \union {new_agent}
    /\ UNCHANGED <<conversations, central_brain_state, agent_registry,
                   conversation_contexts, user_requests, agent_responses, 
                   system_metrics>>

\* Receive response from specialized agent
ReceiveAgentResponse(agent_id, response_content, success) ==
    /\ \E a \in available_agents : a[1] = agent_id /\ a[2] = "BUSY"
    /\ Len(agent_responses) < MAX_AGENTS * 10
    /\ agent_responses' = Append(agent_responses, [
           agent_id |-> agent_id,
           content |-> response_content,
           success |-> success,
           timestamp |-> 1
       ])
    /\ LET old_agent == CHOOSE a \in available_agents : a[1] = agent_id /\ a[2] = "BUSY"
           new_agent == <<agent_id, "IDLE", old_agent[3]>>
       IN available_agents' = (available_agents \ {old_agent}) \union {new_agent}
    /\ UNCHANGED <<conversations, central_brain_state, agent_registry,
                   conversation_contexts, user_requests, system_metrics>>

\* Synthesize agent responses and respond to user
SynthesizeAndRespond ==
    /\ Len(agent_responses) > 0
    /\ central_brain_state = "ORCHESTRATING"
    /\ central_brain_state' = "READY"
    /\ LET response == Head(agent_responses)
           \* Find conversation that requested this agent
           target_conv == CHOOSE c \in DOMAIN conversation_contexts :
                         response.agent_id \in conversation_contexts[c].active_agents
       IN /\ conversation_contexts' = [conversation_contexts EXCEPT
                 ![target_conv].messages = Append(@, [
                     role |-> "assistant",
                     content |-> response.content,
                     agent_source |-> response.agent_id,
                     timestamp |-> 1
                 ])]
          /\ agent_responses' = Tail(agent_responses)
    /\ UNCHANGED <<conversations, available_agents, agent_registry,
                   user_requests, system_metrics>>

\* Handle agent errors and escalation
HandleAgentError(agent_id, error_type) ==
    /\ \E a \in available_agents : a[1] = agent_id /\ a[2] = "BUSY"
    /\ LET old_agent == CHOOSE a \in available_agents : a[1] = agent_id /\ a[2] = "BUSY"
           new_agent == <<agent_id, "ERROR", old_agent[3]>>
       IN available_agents' = (available_agents \ {old_agent}) \union {new_agent}
    /\ \E conv_id \in DOMAIN conversation_contexts :
           /\ agent_id \in conversation_contexts[conv_id].active_agents
           /\ LET old_conv == CHOOSE c \in conversations : c[1] = conv_id
                  new_conv == <<conv_id, "ESCALATED", 0>>
              IN conversations' = (conversations \ {old_conv}) \union {new_conv}
    /\ UNCHANGED <<central_brain_state, agent_registry, conversation_contexts,
                   user_requests, agent_responses, system_metrics>>

\* Complete conversation
CompleteConversation(conv_id) ==
    /\ \E turn_count \in 0..MAX_CONTEXT_DEPTH : <<conv_id, "ACTIVE", turn_count>> \in conversations
    /\ conv_id \in DOMAIN conversation_contexts
    /\ conversation_contexts[conv_id].active_agents = {}
    /\ Len(conversation_contexts[conv_id].messages) > 1  \* Must have at least user + assistant message
    /\ LET old_conv == CHOOSE c \in conversations : c[1] = conv_id /\ c[2] = "ACTIVE"
           new_conv == <<conv_id, "COMPLETED", 0>>
       IN conversations' = (conversations \ {old_conv}) \union {new_conv}
    /\ system_metrics' = [system_metrics EXCEPT 
           !.active_conversations = @ - 1]
    /\ UNCHANGED <<central_brain_state, available_agents, agent_registry,
                   conversation_contexts, user_requests, agent_responses>>

\* Next state relation
Next ==
    \/ InitializeCentralBrain
    \/ \E aid \in 1..MAX_AGENTS, cap \in AGENT_CAPABILITIES : RegisterAgent(aid, cap)
    \/ \E cid \in 1..MAX_CONVERSATIONS : StartConversation(cid)
    \/ \E cid \in 1..MAX_CONVERSATIONS, rt \in RequestType, cont \in MESSAGE_CONTENTS, pri \in Priority : 
           ReceiveUserRequest(cid, rt, cont, pri)
    \/ AnalyzeAndOrchestrate
    \/ \E aid \in 1..MAX_AGENTS, cont \in MESSAGE_CONTENTS : RouteToAgent(aid, cont)
    \/ \E aid \in 1..MAX_AGENTS, cont \in MESSAGE_CONTENTS, succ \in BOOLEAN : 
           ReceiveAgentResponse(aid, cont, succ)
    \/ SynthesizeAndRespond
    \/ \E aid \in 1..MAX_AGENTS, err \in ERROR_TYPES : HandleAgentError(aid, err)
    \/ \E cid \in 1..MAX_CONVERSATIONS : CompleteConversation(cid)

\* Specification
Spec == Init /\ [][Next]_<<conversations, central_brain_state, available_agents,
                           agent_registry, conversation_contexts, user_requests,
                           agent_responses, system_metrics>>

\* Safety Properties

\* No conversation can be in multiple states simultaneously
ConversationStateConsistency ==
    \A c1, c2 \in conversations : (c1[1] = c2[1]) => (c1 = c2)

\* Central Brain cannot orchestrate without being ready
CentralBrainConsistency ==
    (central_brain_state = "ORCHESTRATING") => (Len(user_requests) > 0 \/ Len(agent_responses) > 0)

\* Agents cannot be both idle and busy
AgentStateConsistency ==
    \A a1, a2 \in available_agents : (a1[1] = a2[1]) => (a1 = a2)

\* Active conversations must have valid contexts
ConversationContextConsistency ==
    \A c \in conversations : 
        (c[2] = "ACTIVE") => (c[1] \in DOMAIN conversation_contexts)

\* No response overflow
ResponseQueueBounded ==
    /\ Len(user_requests) <= MAX_CONVERSATIONS * 10
    /\ Len(agent_responses) <= MAX_AGENTS * 10

\* System capacity limits
CapacityLimits ==
    /\ Cardinality(conversations) <= MAX_CONVERSATIONS
    /\ Cardinality(available_agents) <= MAX_AGENTS

\* Liveness Properties

\* User requests eventually get processed (queue doesn't grow unbounded)
RequestsEventuallyProcessed ==
    []<>(Len(user_requests) = 0)

\* Agents eventually return to idle state (system doesn't deadlock with all agents busy)
AgentsEventuallyIdle ==
    []<>(Cardinality(GetAvailableAgents) > 0)

\* Central Brain eventually returns to ready state
CentralBrainEventuallyReady ==
    (central_brain_state = "ORCHESTRATING") ~> (central_brain_state = "READY")

\* All invariants combined
Invariants ==
    /\ TypeInvariant
    /\ ConversationStateConsistency
    /\ CentralBrainConsistency
    /\ AgentStateConsistency
    /\ ConversationContextConsistency
    /\ ResponseQueueBounded
    /\ CapacityLimits

====
