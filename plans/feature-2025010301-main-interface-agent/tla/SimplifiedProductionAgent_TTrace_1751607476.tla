---- MODULE SimplifiedProductionAgent_TTrace_1751607476 ----
EXTENDS Sequences, TLCExt, Toolbox, SimplifiedProductionAgent, Naturals, TLC

_expression ==
    LET SimplifiedProductionAgent_TEExpression == INSTANCE SimplifiedProductionAgent_TEExpression
    IN SimplifiedProductionAgent_TEExpression!expression
----

_trace ==
    LET SimplifiedProductionAgent_TETrace == INSTANCE SimplifiedProductionAgent_TETrace
    IN SimplifiedProductionAgent_TETrace!trace
----

_prop ==
    ~<>[](
        system_metrics = ([active_conversations |-> 3, queries |-> 1, rules |-> 4])
        /\
        prolog_query_stack = (<<>>)
        /\
        agent_registry = (<<"sample_analysis", "workflow_control", "logical_reasoning">>)
        /\
        audit_trails = (<<[action |-> "KNOWLEDGE_ADDED", rule |-> [type |-> "FACT", predicate |-> "has_capability"]], [query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, action |-> "QUERY_STARTED"]>>)
        /\
        central_brain_state = ("READY")
        /\
        available_agents = ({[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]})
        /\
        prolog_inference_chains = ({[query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, result |-> "FAILED"]})
        /\
        prolog_knowledge_base = ({[type |-> "FACT", predicate |-> "has_capability"], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]})
        /\
        conversations = ({[id |-> 1, state |-> "LOGICAL_REASONING"], [id |-> 2, state |-> "ACTIVE"], [id |-> 3, state |-> "ACTIVE"]})
    )
----

_init ==
    /\ prolog_knowledge_base = _TETrace[1].prolog_knowledge_base
    /\ available_agents = _TETrace[1].available_agents
    /\ prolog_query_stack = _TETrace[1].prolog_query_stack
    /\ agent_registry = _TETrace[1].agent_registry
    /\ central_brain_state = _TETrace[1].central_brain_state
    /\ conversations = _TETrace[1].conversations
    /\ audit_trails = _TETrace[1].audit_trails
    /\ system_metrics = _TETrace[1].system_metrics
    /\ prolog_inference_chains = _TETrace[1].prolog_inference_chains
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ prolog_knowledge_base  = _TETrace[i].prolog_knowledge_base
        /\ prolog_knowledge_base' = _TETrace[j].prolog_knowledge_base
        /\ available_agents  = _TETrace[i].available_agents
        /\ available_agents' = _TETrace[j].available_agents
        /\ prolog_query_stack  = _TETrace[i].prolog_query_stack
        /\ prolog_query_stack' = _TETrace[j].prolog_query_stack
        /\ agent_registry  = _TETrace[i].agent_registry
        /\ agent_registry' = _TETrace[j].agent_registry
        /\ central_brain_state  = _TETrace[i].central_brain_state
        /\ central_brain_state' = _TETrace[j].central_brain_state
        /\ conversations  = _TETrace[i].conversations
        /\ conversations' = _TETrace[j].conversations
        /\ audit_trails  = _TETrace[i].audit_trails
        /\ audit_trails' = _TETrace[j].audit_trails
        /\ system_metrics  = _TETrace[i].system_metrics
        /\ system_metrics' = _TETrace[j].system_metrics
        /\ prolog_inference_chains  = _TETrace[i].prolog_inference_chains
        /\ prolog_inference_chains' = _TETrace[j].prolog_inference_chains

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("SimplifiedProductionAgent_TTrace_1751607476.json", _TETrace)

=============================================================================

 Note that you can extract this module `SimplifiedProductionAgent_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `SimplifiedProductionAgent_TEExpression.tla` file takes precedence 
  over the module `SimplifiedProductionAgent_TEExpression` below).

---- MODULE SimplifiedProductionAgent_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, SimplifiedProductionAgent, Naturals, TLC

expression == 
    [
        \* To hide variables of the `SimplifiedProductionAgent` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        prolog_knowledge_base |-> prolog_knowledge_base
        ,available_agents |-> available_agents
        ,prolog_query_stack |-> prolog_query_stack
        ,agent_registry |-> agent_registry
        ,central_brain_state |-> central_brain_state
        ,conversations |-> conversations
        ,audit_trails |-> audit_trails
        ,system_metrics |-> system_metrics
        ,prolog_inference_chains |-> prolog_inference_chains
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_prolog_knowledge_baseUnchanged |-> prolog_knowledge_base = prolog_knowledge_base'
        
        \* Format the `prolog_knowledge_base` variable as Json value.
        \* ,_prolog_knowledge_baseJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(prolog_knowledge_base)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_prolog_knowledge_baseModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].prolog_knowledge_base # _TETrace[s-1].prolog_knowledge_base
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE SimplifiedProductionAgent_TETrace ----
\*EXTENDS IOUtils, SimplifiedProductionAgent, TLC
\*
\*trace == IODeserialize("SimplifiedProductionAgent_TTrace_1751607476.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE SimplifiedProductionAgent_TETrace ----
EXTENDS SimplifiedProductionAgent, TLC

trace == 
    <<
    ([system_metrics |-> [active_conversations |-> 0, queries |-> 0, rules |-> 3],prolog_query_stack |-> <<>>,agent_registry |-> {},audit_trails |-> <<>>,central_brain_state |-> "INITIALIZING",available_agents |-> {},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {}]),
    ([system_metrics |-> [active_conversations |-> 0, queries |-> 0, rules |-> 3],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {}]),
    ([system_metrics |-> [active_conversations |-> 1, queries |-> 0, rules |-> 3],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "ACTIVE"]}]),
    ([system_metrics |-> [active_conversations |-> 2, queries |-> 0, rules |-> 3],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "ACTIVE"], [id |-> 2, state |-> "ACTIVE"]}]),
    ([system_metrics |-> [active_conversations |-> 2, queries |-> 0, rules |-> 4],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<[action |-> "KNOWLEDGE_ADDED", rule |-> [type |-> "FACT", predicate |-> "has_capability"]]>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability"], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "ACTIVE"], [id |-> 2, state |-> "ACTIVE"]}]),
    ([system_metrics |-> [active_conversations |-> 2, queries |-> 0, rules |-> 4],prolog_query_stack |-> <<[state |-> "PENDING", query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1]>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<[action |-> "KNOWLEDGE_ADDED", rule |-> [type |-> "FACT", predicate |-> "has_capability"]], [query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, action |-> "QUERY_STARTED"]>>,central_brain_state |-> "PROLOG_INFERENCE",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability"], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "LOGICAL_REASONING"], [id |-> 2, state |-> "ACTIVE"]}]),
    ([system_metrics |-> [active_conversations |-> 2, queries |-> 1, rules |-> 4],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<[action |-> "KNOWLEDGE_ADDED", rule |-> [type |-> "FACT", predicate |-> "has_capability"]], [query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, action |-> "QUERY_STARTED"]>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {[query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, result |-> "FAILED"]},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability"], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "LOGICAL_REASONING"], [id |-> 2, state |-> "ACTIVE"]}]),
    ([system_metrics |-> [active_conversations |-> 3, queries |-> 1, rules |-> 4],prolog_query_stack |-> <<>>,agent_registry |-> <<"sample_analysis", "workflow_control", "logical_reasoning">>,audit_trails |-> <<[action |-> "KNOWLEDGE_ADDED", rule |-> [type |-> "FACT", predicate |-> "has_capability"]], [query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, action |-> "QUERY_STARTED"]>>,central_brain_state |-> "READY",available_agents |-> {[id |-> 1, state |-> "IDLE", capabilities |-> "sample_analysis"], [id |-> 2, state |-> "IDLE", capabilities |-> "workflow_control"], [id |-> 3, state |-> "IDLE", capabilities |-> "logical_reasoning"]},prolog_inference_chains |-> {[query |-> [predicate |-> "suitable_agent"], conversation_id |-> 1, result |-> "FAILED"]},prolog_knowledge_base |-> {[type |-> "FACT", predicate |-> "has_capability"], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"sample_tracker", "sample_analysis">>], [type |-> "FACT", predicate |-> "has_capability", args |-> <<"workflow_manager", "workflow_control">>], [type |-> "RULE", predicate |-> "suitable_agent", args |-> <<"?Agent", "?Task">>, body |-> {[predicate |-> "has_capability", args |-> <<"?Agent", "?Cap">>], [predicate |-> "requires_capability", args |-> <<"?Task", "?Cap">>]}]},conversations |-> {[id |-> 1, state |-> "LOGICAL_REASONING"], [id |-> 2, state |-> "ACTIVE"], [id |-> 3, state |-> "ACTIVE"]}])
    >>
----


=============================================================================

---- CONFIG SimplifiedProductionAgent_TTrace_1751607476 ----
CONSTANTS
    MAX_CONVERSATIONS = 3
    MAX_AGENTS = 3
    MAX_PROLOG_DEPTH = 5
    MAX_KNOWLEDGE_BASE_SIZE = 10
    AGENT_CAPABILITIES = { "sample_analysis" , "workflow_control" , "logical_reasoning" }
    PROLOG_PREDICATES = { "has_capability" , "suitable_agent" , "requires_capability" }

PROPERTY
    _prop

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
\* Generated on Fri Jul 04 02:39:05 BRT 2025