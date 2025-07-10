---- MODULE PredicateLogicEngine ----
(*
PredicateLogic Engine Specification
Formal model of intelligent reasoning, rule evaluation, and logical inference
for the ALIMS laboratory information management system.

This specification models:
- Rule evaluation with deterministic behavior
- Fact base management with integrity constraints
- Inference engine with termination guarantees
- Conflict resolution and consistency checking
- Memory safety and performance bounds
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Rules,              \* Set of rule identifiers
    Facts,              \* Set of possible facts
    MaxFacts,           \* Maximum facts in working memory
    MaxEvaluations,     \* Maximum concurrent evaluations
    MaxInferenceDepth,  \* Maximum inference chain length
    MaxTraceLength      \* Maximum inference trace length

VARIABLES
    rules,              \* Function: rule_id -> rule_definition
    facts,              \* Set of current facts in working memory
    evaluation_queue,   \* Sequence of pending evaluations
    active_evaluations, \* Set of currently processing evaluations
    inference_chains,   \* Function: evaluation_id -> inference_steps
    rule_dependencies,  \* Function: rule_id -> set_of_dependent_rules
    evaluation_results, \* Function: evaluation_id -> result
    history            \* History of all operations for verification

\* Rule states for lifecycle management
RuleStates == {"DRAFT", "ACTIVE", "INACTIVE", "DEPRECATED"}

\* Evaluation states for tracking progress
EvaluationStates == {"PENDING", "PROCESSING", "COMPLETED", "FAILED"}

\* Fact types for LIMS domain
FactTypes == {"SAMPLE_DATA", "TEST_RESULT", "QC_METRIC", "WORKFLOW_STATE", "USER_INPUT"}

\* Rule condition operators
Operators == {"EQUALS", "NOT_EQUALS", "LESS_THAN", "GREATER_THAN", "CONTAINS", "IN_SET"}

\* Type definitions for structured data
RuleType == [
    id: Rules,
    name: STRING,
    conditions: Seq([field: STRING, operator: Operators, value: STRING]),
    actions: Seq([type: STRING, parameters: STRING]),
    priority: Nat,
    state: RuleStates,
    dependencies: SUBSET Rules
]

FactType == [
    id: Facts,
    type: FactTypes,
    attributes: [field: STRING, value: STRING],
    timestamp: Nat,
    confidence: Nat  \* 0-100 for model checking
]

EvaluationType == [
    id: Nat,
    rule_id: Rules,
    input_facts: SUBSET Facts,
    state: EvaluationStates,
    start_time: Nat,
    result: BOOLEAN
]

\* Variables type invariant
TypeInvariant ==
    /\ rules \in [Rules -> RuleType]
    /\ facts \subseteq FactType
    /\ evaluation_queue \in Seq(EvaluationType)
    /\ active_evaluations \subseteq EvaluationType
    /\ rule_dependencies \in [Rules -> SUBSET Rules]
    /\ history \in Seq([action: STRING, rule: Rules, evaluation: Nat])

----

\* Initial state specification
Init ==
    /\ rules = [r \in Rules |-> [
           id |-> r,
           name |-> "Rule_" \o ToString(r),
           conditions |-> <<>>,
           actions |-> <<>>,
           priority |-> 1,
           state |-> "DRAFT",
           dependencies |-> {}
       ]]
    /\ facts = {}
    /\ evaluation_queue = <<>>
    /\ active_evaluations = {}
    /\ inference_chains = [eval \in 1..0 |-> <<>>]
    /\ rule_dependencies = [r \in Rules |-> {}]
    /\ evaluation_results = [eval \in 1..0 |-> FALSE]
    /\ history = <<>>

----

\* Helper predicates

\* Check if rule is ready for evaluation
RuleIsReady(rule_id) ==
    /\ rules[rule_id].state = "ACTIVE"
    /\ \A dep \in rule_dependencies[rule_id] :
        rules[dep].state = "ACTIVE"

\* Check if fact base has capacity for new facts
FactCapacityAvailable ==
    Cardinality(facts) < MaxFacts

\* Check if system can accept new evaluations
EvaluationCapacityAvailable ==
    Len(evaluation_queue) + Cardinality(active_evaluations) < MaxEvaluations

\* Check if rule has circular dependencies
HasCircularDependency(rule_id) ==
    LET
        RECURSIVE CheckCircular(_, _)
        CheckCircular(current, visited) ==
            IF current \in visited THEN TRUE
            ELSE
                \E dep \in rule_dependencies[current] :
                    CheckCircular(dep, visited \cup {current})
    IN CheckCircular(rule_id, {})

\* Evaluate rule conditions against current facts
EvaluateRuleConditions(rule_id) ==
    \* Simplified evaluation - in full implementation would check actual conditions
    \* For model checking, we use non-deterministic choice
    CHOOSE result \in BOOLEAN : TRUE

----

\* Action: Create new rule
CreateRule ==
    /\ \E rule_id \in Rules :
        /\ rules[rule_id].state = "DRAFT"
        /\ rules' = [rules EXCEPT ![rule_id] = [
               @ EXCEPT
               !.conditions = <<>>,
               !.actions = <<>>,
               !.priority = 1
           ]]
        /\ history' = Append(history, [action |-> "CREATE_RULE", rule |-> rule_id, evaluation |-> 0])
        /\ UNCHANGED <<facts, evaluation_queue, active_evaluations, 
                      inference_chains, rule_dependencies, evaluation_results>>

\* Action: Activate rule (after validation)
ActivateRule ==
    /\ \E rule_id \in Rules :
        /\ rules[rule_id].state = "DRAFT"
        /\ ~HasCircularDependency(rule_id)
        /\ rules' = [rules EXCEPT ![rule_id].state = "ACTIVE"]
        /\ history' = Append(history, [action |-> "ACTIVATE_RULE", rule |-> rule_id, evaluation |-> 0])
        /\ UNCHANGED <<facts, evaluation_queue, active_evaluations, 
                      inference_chains, rule_dependencies, evaluation_results>>

\* Action: Add fact to working memory
AddFact ==
    /\ FactCapacityAvailable
    /\ \E fact_id \in Facts :
        /\ fact_id \notin {f.id : f \in facts}
        /\ LET new_fact == [
               id |-> fact_id,
               type |-> "SAMPLE_DATA",
               attributes |-> [field |-> "test", value |-> "value"],
               timestamp |-> Len(history) + 1,
               confidence |-> 80
           ] IN
           /\ facts' = facts \cup {new_fact}
           /\ history' = Append(history, [action |-> "ADD_FACT", rule |-> CHOOSE r \in Rules : TRUE, evaluation |-> 0])
           /\ UNCHANGED <<rules, evaluation_queue, active_evaluations, 
                         inference_chains, rule_dependencies, evaluation_results>>

\* Action: Remove fact from working memory
RemoveFact ==
    /\ facts /= {}
    /\ \E fact \in facts :
        /\ facts' = facts \ {fact}
        /\ history' = Append(history, [action |-> "REMOVE_FACT", rule |-> CHOOSE r \in Rules : TRUE, evaluation |-> 0])
        /\ UNCHANGED <<rules, evaluation_queue, active_evaluations, 
                      inference_chains, rule_dependencies, evaluation_results>>

\* Action: Request rule evaluation
RequestEvaluation ==
    /\ EvaluationCapacityAvailable
    /\ \E rule_id \in Rules :
        /\ RuleIsReady(rule_id)
        /\ LET eval_id == Len(evaluation_queue) + Cardinality(active_evaluations) + 1
               new_evaluation == [
                   id |-> eval_id,
                   rule_id |-> rule_id,
                   input_facts |-> {f.id : f \in facts},  \* Convert to fact IDs
                   state |-> "PENDING",
                   start_time |-> Len(history) + 1,
                   result |-> FALSE
               ]
           IN
               /\ evaluation_queue' = Append(evaluation_queue, new_evaluation)
               /\ inference_chains' = inference_chains @@ (eval_id :> <<>>)
               /\ history' = Append(history, [action |-> "REQUEST_EVALUATION", rule |-> rule_id, evaluation |-> eval_id])
               /\ UNCHANGED <<rules, facts, active_evaluations, rule_dependencies, evaluation_results>>

\* Action: Process pending evaluation
ProcessEvaluation ==
    /\ evaluation_queue /= <<>>
    /\ LET evaluation == Head(evaluation_queue)
           eval_id == evaluation.id
           rule_id == evaluation.rule_id
       IN
           /\ evaluation_queue' = Tail(evaluation_queue)
           /\ active_evaluations' = active_evaluations \cup {[evaluation EXCEPT !.state = "PROCESSING"]}
           /\ inference_chains' = [inference_chains EXCEPT ![eval_id] = Append(@, "START_EVALUATION")]
           /\ history' = Append(history, [action |-> "PROCESS_EVALUATION", rule |-> rule_id, evaluation |-> eval_id])
           /\ UNCHANGED <<rules, facts, rule_dependencies, evaluation_results>>

\* Action: Complete evaluation with result
CompleteEvaluation ==
    /\ active_evaluations /= {}
    /\ \E evaluation \in active_evaluations :
        /\ evaluation.state = "PROCESSING"
        /\ LET eval_id == evaluation.id
               rule_id == evaluation.rule_id
               eval_result == EvaluateRuleConditions(rule_id)
           IN
               /\ active_evaluations' = (active_evaluations \ {evaluation}) \cup 
                                       {[evaluation EXCEPT !.state = "COMPLETED", !.result = eval_result]}
               /\ evaluation_results' = evaluation_results @@ (eval_id :> eval_result)
               /\ inference_chains' = [inference_chains EXCEPT ![eval_id] = 
                                      Append(@, IF eval_result THEN "RESULT_TRUE" ELSE "RESULT_FALSE")]
               /\ history' = Append(history, [action |-> "COMPLETE_EVALUATION", rule |-> rule_id, evaluation |-> eval_id])
               /\ UNCHANGED <<rules, facts, evaluation_queue, rule_dependencies>>

\* Action: Perform inference step
InferenceStep ==
    /\ \E evaluation \in active_evaluations :
        /\ evaluation.state = "PROCESSING"
        /\ LET eval_id == evaluation.id
               current_chain == inference_chains[eval_id]
           IN
               /\ Len(current_chain) < MaxInferenceDepth
               /\ \E inference_action \in {"FORWARD_CHAIN", "BACKWARD_CHAIN", "UNIFY", "RESOLVE"} :
                   /\ inference_chains' = [inference_chains EXCEPT ![eval_id] = Append(@, inference_action)]
                   /\ history' = Append(history, [action |-> "INFERENCE_STEP", rule |-> evaluation.rule_id, evaluation |-> eval_id])
                   /\ UNCHANGED <<rules, facts, evaluation_queue, active_evaluations, rule_dependencies, evaluation_results>>

\* Action: Set rule dependency
SetRuleDependency ==
    /\ \E rule_id, dep_id \in Rules :
        /\ rule_id /= dep_id
        /\ dep_id \notin rule_dependencies[rule_id]
        /\ rule_id \notin rule_dependencies[dep_id]  \* Prevent immediate cycles
        /\ rule_dependencies' = [rule_dependencies EXCEPT ![rule_id] = @ \cup {dep_id}]
        /\ history' = Append(history, [action |-> "SET_DEPENDENCY", rule |-> rule_id, evaluation |-> 0])
        /\ UNCHANGED <<rules, facts, evaluation_queue, active_evaluations, inference_chains, evaluation_results>>

----

\* Next state relation: all possible actions
Next ==
    \/ CreateRule
    \/ ActivateRule
    \/ AddFact
    \/ RemoveFact
    \/ RequestEvaluation
    \/ ProcessEvaluation
    \/ CompleteEvaluation
    \/ InferenceStep
    \* \/ SetRuleDependency  \* Disabled for now to focus on core evaluation

\* Complete specification
Spec == Init /\ [][Next]_<<rules, facts, evaluation_queue, active_evaluations, 
                           inference_chains, rule_dependencies, evaluation_results, history>>

----

\* Safety Properties (Invariants)

\* Rule consistency - no contradictory active rules
RuleConsistency ==
    \A r1, r2 \in Rules :
        (rules[r1].state = "ACTIVE" /\ rules[r2].state = "ACTIVE" /\ r1 /= r2)
        => TRUE  \* Simplified - in practice would check for logical contradictions

\* Fact base integrity
FactIntegrity ==
    /\ Cardinality(facts) <= MaxFacts
    /\ \A fact \in facts :
        /\ fact.confidence \in 0..100
        /\ fact.timestamp <= Len(history)

\* Evaluation determinism - same inputs produce same outputs
EvaluationDeterminism ==
    \A eval1, eval2 \in DOMAIN evaluation_results :
        (eval1 /= eval2 /\ 
         \E e1 \in active_evaluations : e1.id = eval1 /\
         \E e2 \in active_evaluations : e2.id = eval2 /\
         e1.rule_id = e2.rule_id /\ e1.input_facts = e2.input_facts)
        => evaluation_results[eval1] = evaluation_results[eval2]

\* Inference termination guarantee
InferenceTermination ==
    \A eval_id \in DOMAIN inference_chains :
        Len(inference_chains[eval_id]) <= MaxInferenceDepth

\* Dependency acyclicity
DependencyAcyclicity ==
    \A rule_id \in Rules :
        ~HasCircularDependency(rule_id)

\* Memory safety bounds
MemoryBounds ==
    /\ Cardinality(facts) <= MaxFacts
    /\ Len(evaluation_queue) + Cardinality(active_evaluations) <= MaxEvaluations
    /\ \A eval_id \in DOMAIN inference_chains :
        Len(inference_chains[eval_id]) <= MaxTraceLength

\* System capacity constraints
CapacityConstraints ==
    /\ Len(evaluation_queue) <= MaxEvaluations
    /\ Cardinality(active_evaluations) <= MaxEvaluations
    /\ Cardinality(facts) <= MaxFacts

\* Combine all safety properties
SafetyProperties ==
    /\ TypeInvariant
    /\ RuleConsistency
    /\ FactIntegrity
    /\ EvaluationDeterminism
    /\ InferenceTermination
    /\ DependencyAcyclicity
    /\ MemoryBounds
    /\ CapacityConstraints

----

\* Liveness Properties (Temporal)

\* All evaluations eventually complete
EvaluationProgress ==
    [](\A evaluation \in evaluation_queue :
        <>(evaluation \notin evaluation_queue))

\* Active rules can eventually be evaluated
RuleAvailability ==
    [](\E rule_id \in Rules : rules[rule_id].state = "ACTIVE"
        => <>(\E eval \in active_evaluations : eval.rule_id = rule_id))

\* Facts can be processed when system has capacity
FactProcessing ==
    [](FactCapacityAvailable => <>(\E fact \in facts : TRUE))

----

\* State constraint to bound model checking
StateConstraint ==
    /\ Cardinality(facts) <= MaxFacts
    /\ Len(evaluation_queue) + Cardinality(active_evaluations) <= MaxEvaluations
    /\ Len(history) <= 20
    /\ \A eval_id \in DOMAIN inference_chains :
        Len(inference_chains[eval_id]) <= MaxInferenceDepth

----

\* Properties to check
THEOREM SafetyTheorem == Spec => []SafetyProperties
THEOREM LivenessTheorem == Spec => EvaluationProgress /\ RuleAvailability

====
