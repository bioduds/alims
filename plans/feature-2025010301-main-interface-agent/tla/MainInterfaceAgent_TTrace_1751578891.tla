---- MODULE MainInterfaceAgent_TTrace_1751578891 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MainInterfaceAgent

_expression ==
    LET MainInterfaceAgent_TEExpression == INSTANCE MainInterfaceAgent_TEExpression
    IN MainInterfaceAgent_TEExpression!expression
----

_trace ==
    LET MainInterfaceAgent_TETrace == INSTANCE MainInterfaceAgent_TETrace
    IN MainInterfaceAgent_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        system_metrics = ([active_conversations |-> 0, response_time |-> 0])
        /\
        agent_registry = (<<>>)
        /\
        conversation_contexts = (<<[messages |-> <<[content |-> "sample_inquiry", timestamp |-> 1, role |-> "user"]>>, current_context |-> {}, active_agents |-> {"sample_tracker", "workflow_manager"}, user_intent |-> "SAMPLE_INQUIRY"]>>)
        /\
        central_brain_state = ("ORCHESTRATING")
        /\
        available_agents = ({})
        /\
        user_requests = (<<>>)
        /\
        agent_responses = (<<>>)
        /\
        conversations = ({<<1, "COMPLETED", 0>>})
    )
----

_init ==
    /\ system_metrics = _TETrace[1].system_metrics
    /\ available_agents = _TETrace[1].available_agents
    /\ agent_registry = _TETrace[1].agent_registry
    /\ conversations = _TETrace[1].conversations
    /\ conversation_contexts = _TETrace[1].conversation_contexts
    /\ user_requests = _TETrace[1].user_requests
    /\ central_brain_state = _TETrace[1].central_brain_state
    /\ agent_responses = _TETrace[1].agent_responses
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ system_metrics  = _TETrace[i].system_metrics
        /\ system_metrics' = _TETrace[j].system_metrics
        /\ available_agents  = _TETrace[i].available_agents
        /\ available_agents' = _TETrace[j].available_agents
        /\ agent_registry  = _TETrace[i].agent_registry
        /\ agent_registry' = _TETrace[j].agent_registry
        /\ conversations  = _TETrace[i].conversations
        /\ conversations' = _TETrace[j].conversations
        /\ conversation_contexts  = _TETrace[i].conversation_contexts
        /\ conversation_contexts' = _TETrace[j].conversation_contexts
        /\ user_requests  = _TETrace[i].user_requests
        /\ user_requests' = _TETrace[j].user_requests
        /\ central_brain_state  = _TETrace[i].central_brain_state
        /\ central_brain_state' = _TETrace[j].central_brain_state
        /\ agent_responses  = _TETrace[i].agent_responses
        /\ agent_responses' = _TETrace[j].agent_responses

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("MainInterfaceAgent_TTrace_1751578891.json", _TETrace)

=============================================================================

 Note that you can extract this module `MainInterfaceAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `MainInterfaceAgent_TEExpression.tla` file takes precedence 
  over the module `MainInterfaceAgent_TEExpression` below).

---- MODULE MainInterfaceAgent_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MainInterfaceAgent

expression == 
    [
        \* To hide variables of the `MainInterfaceAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        system_metrics |-> system_metrics
        ,available_agents |-> available_agents
        ,agent_registry |-> agent_registry
        ,conversations |-> conversations
        ,conversation_contexts |-> conversation_contexts
        ,user_requests |-> user_requests
        ,central_brain_state |-> central_brain_state
        ,agent_responses |-> agent_responses
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_system_metricsUnchanged |-> system_metrics = system_metrics'
        
        \* Format the `system_metrics` variable as Json value.
        \* ,_system_metricsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(system_metrics)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_system_metricsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].system_metrics # _TETrace[s-1].system_metrics
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE MainInterfaceAgent_TETrace ----
\*EXTENDS IOUtils, TLC, MainInterfaceAgent
\*
\*trace == IODeserialize("MainInterfaceAgent_TTrace_1751578891.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE MainInterfaceAgent_TETrace ----
EXTENDS TLC, MainInterfaceAgent

trace == 
    <<
    ([system_metrics |-> [active_conversations |-> 0, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<>>,central_brain_state |-> "INITIALIZING",available_agents |-> {},user_requests |-> <<>>,agent_responses |-> <<>>,conversations |-> {}]),
    ([system_metrics |-> [active_conversations |-> 0, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<>>,central_brain_state |-> "READY",available_agents |-> {},user_requests |-> <<>>,agent_responses |-> <<>>,conversations |-> {}]),
    ([system_metrics |-> [active_conversations |-> 1, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<[messages |-> <<>>, current_context |-> {}, active_agents |-> {}, user_intent |-> "UNKNOWN"]>>,central_brain_state |-> "READY",available_agents |-> {},user_requests |-> <<>>,agent_responses |-> <<>>,conversations |-> {<<1, "ACTIVE", 0>>}]),
    ([system_metrics |-> [active_conversations |-> 1, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<[messages |-> <<[content |-> "sample_inquiry", timestamp |-> 1, role |-> "user"]>>, current_context |-> {}, active_agents |-> {}, user_intent |-> "UNKNOWN"]>>,central_brain_state |-> "READY",available_agents |-> {},user_requests |-> <<[content |-> "sample_inquiry", priority |-> "LOW", conversation_id |-> 1, type |-> "SAMPLE_INQUIRY", timestamp |-> 1]>>,agent_responses |-> <<>>,conversations |-> {<<1, "ACTIVE", 0>>}]),
    ([system_metrics |-> [active_conversations |-> 0, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<[messages |-> <<[content |-> "sample_inquiry", timestamp |-> 1, role |-> "user"]>>, current_context |-> {}, active_agents |-> {}, user_intent |-> "UNKNOWN"]>>,central_brain_state |-> "READY",available_agents |-> {},user_requests |-> <<[content |-> "sample_inquiry", priority |-> "LOW", conversation_id |-> 1, type |-> "SAMPLE_INQUIRY", timestamp |-> 1]>>,agent_responses |-> <<>>,conversations |-> {<<1, "COMPLETED", 0>>}]),
    ([system_metrics |-> [active_conversations |-> 0, response_time |-> 0],agent_registry |-> <<>>,conversation_contexts |-> <<[messages |-> <<[content |-> "sample_inquiry", timestamp |-> 1, role |-> "user"]>>, current_context |-> {}, active_agents |-> {"sample_tracker", "workflow_manager"}, user_intent |-> "SAMPLE_INQUIRY"]>>,central_brain_state |-> "ORCHESTRATING",available_agents |-> {},user_requests |-> <<>>,agent_responses |-> <<>>,conversations |-> {<<1, "COMPLETED", 0>>}])
    >>
----


=============================================================================

---- CONFIG MainInterfaceAgent_TTrace_1751578891 ----
CONSTANTS
    MAX_CONVERSATIONS = 2
    MAX_AGENTS = 2
    MAX_CONTEXT_DEPTH = 3
    AGENT_CAPABILITIES = { "sample_tracker" , "workflow_manager" }
    MESSAGE_CONTENTS = { "sample_inquiry" , "workflow_command" }
    ERROR_TYPES = { "timeout" , "invalid_request" }

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
\* Generated on Thu Jul 03 18:41:35 BRT 2025