-------------------------------- MODULE MainInterfaceAgentIntegration --------------------------------

\* TLA+ Specification for Main Interface Agent Integration into ALIMS System
\* This specification validates the integration of the Main Interface Agent 
\* into the main ALIMS system following the same pattern as Result Processing Agent

EXTENDS Integers, Sequences, FiniteSets, TLC

\* System constants
CONSTANTS
    MAX_CONVERSATIONS,
    MAX_AGENTS,
    MAX_REQUESTS,
    MAX_RESPONSES

\* Agent capabilities
AGENT_CAPABILITIES == {
    "sample_tracker",
    "workflow_manager", 
    "lims_coordinator",
    "system_monitor",
    "result_processor"
}

\* System states
SystemState == {
    "INITIALIZING",
    "RUNNING", 
    "STOPPING",
    "STOPPED"
}

\* Agent states
AgentState == {
    "IDLE",
    "BUSY",
    "ERROR"
}

\* Central Brain states
CentralBrainState == {
    "READY",
    "ORCHESTRATING", 
    "WAITING_FOR_RESPONSE",
    "SYNTHESIZING"
}

\* Conversation states
ConversationState == {
    "ACTIVE",
    "COMPLETED",
    "ERROR"
}

\* Request types
RequestType == {
    "SAMPLE_INQUIRY",
    "WORKFLOW_COMMAND",
    "SYSTEM_QUERY",
    "AGENT_REQUEST"
}

\* Priority levels
Priority == {
    "LOW",
    "MEDIUM", 
    "HIGH",
    "URGENT"
}

\* State variables
VARIABLES
    \* Main system state
    alims_state,
    permission_manager,
    sample_manager,
    result_processing_agent,
    
    \* Main Interface Agent state
    main_interface_agent,
    central_brain_state,
    conversations,
    available_agents,
    user_requests,
    agent_responses,
    
    \* System metrics
    system_metrics,
    error_count

\* Type invariants
TypeInv ==
    /\ alims_state \in SystemState
    /\ permission_manager \in {"READY", "NOT_READY"}
    /\ sample_manager \in {"READY", "NOT_READY"}
    /\ result_processing_agent \in {"READY", "NOT_READY"}
    /\ main_interface_agent \in {"READY", "NOT_READY", "INITIALIZING"}
    /\ central_brain_state \in CentralBrainState
    /\ conversations \in [1..MAX_CONVERSATIONS -> ConversationState]
    /\ available_agents \in [1..MAX_AGENTS -> AgentState]
    /\ user_requests \in Seq([type: RequestType, priority: Priority, conv_id: 1..MAX_CONVERSATIONS])
    /\ agent_responses \in Seq([agent_id: 1..MAX_AGENTS, conv_id: 1..MAX_CONVERSATIONS, success: BOOLEAN])
    /\ system_metrics \in [active_conversations: 0..MAX_CONVERSATIONS, total_requests: Nat, error_count: Nat]
    /\ error_count \in Nat

\* Safety properties
SafetyInv ==
    /\ \* Main Interface Agent requires dependencies to be ready
       (main_interface_agent = "READY") => (permission_manager = "READY" /\ sample_manager = "READY")
    /\ \* ALIMS system requires all components ready
       (alims_state = "RUNNING") => (main_interface_agent = "READY")
    /\ \* Central Brain consistency
       (central_brain_state \in {"ORCHESTRATING", "SYNTHESIZING"}) => (main_interface_agent = "READY")
    /\ \* Conversation consistency
       system_metrics.active_conversations <= MAX_CONVERSATIONS
    /\ \* Request queue bounded
       Len(user_requests) <= MAX_REQUESTS
    /\ \* Response queue bounded
       Len(agent_responses) <= MAX_RESPONSES

\* Initial state
Init ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "NOT_READY"
    /\ sample_manager = "NOT_READY"
    /\ result_processing_agent = "NOT_READY"
    /\ main_interface_agent = "NOT_READY"
    /\ central_brain_state = "READY"
    /\ conversations = [i \in 1..MAX_CONVERSATIONS |-> "COMPLETED"]
    /\ available_agents = [i \in 1..MAX_AGENTS |-> "IDLE"]
    /\ user_requests = <<>>
    /\ agent_responses = <<>>
    /\ system_metrics = [active_conversations |-> 0, total_requests |-> 0, error_count |-> 0]
    /\ error_count = 0

\* Initialize Permission Manager
InitPermissionManager ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "NOT_READY"
    /\ permission_manager' = "READY"
    /\ UNCHANGED <<alims_state, sample_manager, result_processing_agent, main_interface_agent,
                   central_brain_state, conversations, available_agents, user_requests, 
                   agent_responses, system_metrics, error_count>>

\* Initialize Sample Manager
InitSampleManager ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "READY"
    /\ sample_manager = "NOT_READY"
    /\ sample_manager' = "READY"
    /\ UNCHANGED <<alims_state, permission_manager, result_processing_agent, main_interface_agent,
                   central_brain_state, conversations, available_agents, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Initialize Result Processing Agent
InitResultProcessingAgent ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "READY"
    /\ sample_manager = "READY"
    /\ result_processing_agent = "NOT_READY"
    /\ result_processing_agent' = "READY"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, main_interface_agent,
                   central_brain_state, conversations, available_agents, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Initialize Main Interface Agent
InitMainInterfaceAgent ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "READY"
    /\ sample_manager = "READY"
    /\ result_processing_agent = "READY"
    /\ main_interface_agent = "NOT_READY"
    /\ main_interface_agent' = "INITIALIZING"
    /\ central_brain_state' = "READY"
    /\ \* Initialize core agents
       available_agents' = [available_agents EXCEPT ![1] = "IDLE", ![2] = "IDLE"]
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   conversations, user_requests, agent_responses, system_metrics, error_count>>

\* Complete Main Interface Agent initialization
CompleteMainInterfaceAgentInit ==
    /\ main_interface_agent = "INITIALIZING"
    /\ central_brain_state = "READY"
    /\ main_interface_agent' = "READY"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   central_brain_state, conversations, available_agents, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Start ALIMS system
StartALIMSSystem ==
    /\ alims_state = "INITIALIZING"
    /\ permission_manager = "READY"
    /\ sample_manager = "READY"
    /\ result_processing_agent = "READY"
    /\ main_interface_agent = "READY"
    /\ alims_state' = "RUNNING"
    /\ UNCHANGED <<permission_manager, sample_manager, result_processing_agent, main_interface_agent,
                   central_brain_state, conversations, available_agents, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Register agent with Main Interface Agent
RegisterAgent ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ \E agent_id \in 1..MAX_AGENTS :
        /\ available_agents[agent_id] = "IDLE"
        /\ available_agents' = [available_agents EXCEPT ![agent_id] = "IDLE"]
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, central_brain_state, conversations, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Start conversation
StartConversation ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "READY"
    /\ system_metrics.active_conversations < MAX_CONVERSATIONS
    /\ \E conv_id \in 1..MAX_CONVERSATIONS :
        /\ conversations[conv_id] = "COMPLETED"
        /\ conversations' = [conversations EXCEPT ![conv_id] = "ACTIVE"]
        /\ system_metrics' = [system_metrics EXCEPT !.active_conversations = @ + 1]
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, central_brain_state, available_agents, user_requests,
                   agent_responses, error_count>>

\* Process user request
ProcessUserRequest ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "READY"
    /\ Len(user_requests) < MAX_REQUESTS
    /\ \E req_type \in RequestType, priority \in Priority, conv_id \in 1..MAX_CONVERSATIONS :
        /\ conversations[conv_id] = "ACTIVE"
        /\ user_requests' = Append(user_requests, 
                                 [type |-> req_type, priority |-> priority, conv_id |-> conv_id])
        /\ system_metrics' = [system_metrics EXCEPT !.total_requests = @ + 1]
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, central_brain_state, conversations, available_agents,
                   agent_responses, error_count>>

\* Orchestrate agents
OrchestratorsAgents ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "READY"
    /\ Len(user_requests) > 0
    /\ central_brain_state' = "ORCHESTRATING"
    /\ \* Process the first request
       LET request == Head(user_requests) IN
       user_requests' = Tail(user_requests)
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, conversations, available_agents, agent_responses,
                   system_metrics, error_count>>

\* Route to agent
RouteToAgent ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "ORCHESTRATING"
    /\ \E agent_id \in 1..MAX_AGENTS :
        /\ available_agents[agent_id] = "IDLE"
        /\ available_agents' = [available_agents EXCEPT ![agent_id] = "BUSY"]
        /\ central_brain_state' = "WAITING_FOR_RESPONSE"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, conversations, user_requests, agent_responses,
                   system_metrics, error_count>>

\* Receive agent response
ReceiveAgentResponse ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "WAITING_FOR_RESPONSE"
    /\ Len(agent_responses) < MAX_RESPONSES
    /\ \E agent_id \in 1..MAX_AGENTS, conv_id \in 1..MAX_CONVERSATIONS, success \in BOOLEAN :
        /\ available_agents[agent_id] = "BUSY"
        /\ conversations[conv_id] = "ACTIVE"
        /\ available_agents' = [available_agents EXCEPT ![agent_id] = "IDLE"]
        /\ agent_responses' = Append(agent_responses, 
                                   [agent_id |-> agent_id, conv_id |-> conv_id, success |-> success])
        /\ central_brain_state' = "SYNTHESIZING"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, conversations, user_requests, system_metrics, error_count>>

\* Synthesize response
SynthesizeResponse ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ central_brain_state = "SYNTHESIZING"
    /\ Len(agent_responses) > 0
    /\ agent_responses' = Tail(agent_responses)
    /\ central_brain_state' = "READY"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, conversations, available_agents, user_requests,
                   system_metrics, error_count>>

\* Handle error
HandleError ==
    /\ alims_state = "RUNNING"
    /\ main_interface_agent = "READY"
    /\ error_count' = error_count + 1
    /\ system_metrics' = [system_metrics EXCEPT !.error_count = @ + 1]
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   main_interface_agent, central_brain_state, conversations, available_agents,
                   user_requests, agent_responses>>

\* Stop Main Interface Agent
StopMainInterfaceAgent ==
    /\ alims_state = "STOPPING"
    /\ main_interface_agent = "READY"
    /\ main_interface_agent' = "NOT_READY"
    /\ central_brain_state' = "READY"
    /\ UNCHANGED <<alims_state, permission_manager, sample_manager, result_processing_agent,
                   conversations, available_agents, user_requests, agent_responses,
                   system_metrics, error_count>>

\* Stop ALIMS system
StopALIMSSystem ==
    /\ alims_state = "STOPPING"
    /\ main_interface_agent = "NOT_READY"
    /\ result_processing_agent = "NOT_READY"
    /\ alims_state' = "STOPPED"
    /\ UNCHANGED <<permission_manager, sample_manager, result_processing_agent, main_interface_agent,
                   central_brain_state, conversations, available_agents, user_requests,
                   agent_responses, system_metrics, error_count>>

\* Next state relation
Next ==
    \/ InitPermissionManager
    \/ InitSampleManager
    \/ InitResultProcessingAgent
    \/ InitMainInterfaceAgent
    \/ CompleteMainInterfaceAgentInit
    \/ StartALIMSSystem
    \/ RegisterAgent
    \/ StartConversation
    \/ ProcessUserRequest
    \/ OrchestratorsAgents
    \/ RouteToAgent
    \/ ReceiveAgentResponse
    \/ SynthesizeResponse
    \/ HandleError
    \/ StopMainInterfaceAgent
    \/ StopALIMSSystem

\* Specification
Spec == Init /\ [][Next]_<<alims_state, permission_manager, sample_manager, result_processing_agent,
                            main_interface_agent, central_brain_state, conversations, available_agents,
                            user_requests, agent_responses, system_metrics, error_count>>

\* Liveness properties
LivenessProperties ==
    /\ \* System eventually starts
       <>(alims_state = "RUNNING")
    /\ \* Requests eventually processed
       [](Len(user_requests) > 0 => <>(Len(user_requests) = 0))
    /\ \* Responses eventually processed
       [](Len(agent_responses) > 0 => <>(Len(agent_responses) = 0))
    /\ \* Central Brain eventually ready
       [](central_brain_state \in {"ORCHESTRATING", "SYNTHESIZING"} => <>(central_brain_state = "READY"))

================================================================================
