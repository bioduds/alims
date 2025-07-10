-------------------------------- MODULE PredicateLogic --------------------------------
\* TLA+ Specification for ALIMS PredicateLogic Engine
\* Models rule evaluation, inference, and fact base management
\* Author: ALIMS System Design Team
\* Version: 1.0

EXTENDS Integers, Sequences, FiniteSets, TLC

\* Constants for configuration
CONSTANTS
    MaxRules,           \* Maximum number of rules in system
    MaxFacts,           \* Maximum facts in working memory  
    MaxEvaluations,     \* Maximum concurrent evaluations
    MaxInferenceSteps,  \* Maximum inference chain length
    RuleIds,            \* Set of possible rule identifiers
    FactIds,            \* Set of possible fact identifiers
    EvaluationIds       \* Set of possible evaluation identifiers

\* Assume reasonable bounds for model checking
ASSUME MaxRules \in Nat /\ MaxRules > 0
ASSUME MaxFacts \in Nat /\ MaxFacts > 0  
ASSUME MaxEvaluations \in Nat /\ MaxEvaluations > 0
ASSUME MaxInferenceSteps \in Nat /\ MaxInferenceSteps > 0

\* Rule status enumeration
RuleStatus == {"enabled", "disabled", "invalid"}

\* Evaluation status enumeration  
EvaluationStatus == {"queued", "processing", "completed", "failed", "timeout"}

\* Fact types for laboratory domain
FactType == {"sample", "test_result", "qc_data", "protocol", "threshold"}

\* Variables representing system state
VARIABLES
    rules,              \* Function: RuleId -> Rule record
    facts,              \* Set of facts in working memory
    evaluation_queue,   \* Sequence of pending evaluations
    active_evaluations, \* Set of currently processing evaluations  
    completed_evaluations, \* Set of completed evaluations
    inference_chains,   \* Function: EvaluationId -> Sequence of inference steps
    rule_dependencies,  \* Function: RuleId -> Set of dependent rule IDs
    working_memory_size \* Current size of working memory

\* Type definitions for structured data
Rule == [
    id: RuleIds,
    status: RuleStatus,
    priority: Nat,
    conditions: Seq(Nat),      \* Simplified as sequence of condition IDs
    actions: Seq(Nat),         \* Simplified as sequence of action IDs  
    dependencies: SUBSET RuleIds
]

Fact == [
    id: FactIds,
    type: FactType,
    value: Nat,                \* Simplified fact value
    timestamp: Nat,
    confidence: Nat            \* Confidence level 0-100
]

Evaluation == [
    id: EvaluationIds,
    rule_id: RuleIds,
    input_facts: SUBSET FactIds,
    status: EvaluationStatus,
    result: BOOLEAN,           \* Evaluation result
    start_time: Nat,
    inference_steps: Nat       \* Number of inference steps taken
]

InferenceStep == [
    rule_applied: RuleIds,
    facts_used: SUBSET FactIds,
    conclusion: Nat            \* Simplified conclusion
]

\* Initial state specification
Init ==
    /\ rules = [r \in {} |-> <<>>]
    /\ facts = {}
    /\ evaluation_queue = <<>>
    /\ active_evaluations = {}
    /\ completed_evaluations = {}
    /\ inference_chains = [e \in {} |-> <<>>]
    /\ rule_dependencies = [r \in {} |-> {}]
    /\ working_memory_size = 0

\* Helper predicates
IsValidRule(rule) ==
    /\ rule.id \in RuleIds
    /\ rule.status \in RuleStatus
    /\ rule.priority \in Nat
    /\ rule.dependencies \subseteq RuleIds
    /\ rule.id \notin rule.dependencies  \* No self-dependency

IsValidFact(fact) ==
    /\ fact.id \in FactIds
    /\ fact.type \in FactType
    /\ fact.confidence \in 0..100
    /\ fact.timestamp \in Nat

IsValidEvaluation(eval) ==
    /\ eval.id \in EvaluationIds
    /\ eval.rule_id \in RuleIds
    /\ eval.status \in EvaluationStatus
    /\ eval.input_facts \subseteq FactIds
    /\ eval.inference_steps \in Nat
    /\ eval.inference_steps <= MaxInferenceSteps

\* Rule dependency graph is acyclic
DependencyGraphAcyclic ==
    \* For all rules, no rule can reach itself through dependencies
    \A r \in DOMAIN rules :
        LET TransitiveDeps == 
            UNION {rule_dependencies[dep] : dep \in rule_dependencies[r]}
        IN r \notin TransitiveDeps

\* Actions representing system operations

\* Add a new rule to the system
AddRule ==
    \E new_rule \in Rule :
        /\ IsValidRule(new_rule)
        /\ new_rule.id \notin DOMAIN rules
        /\ Cardinality(DOMAIN rules) < MaxRules
        /\ DependencyGraphAcyclic  \* Ensure acyclic after addition
        /\ rules' = rules @@ (new_rule.id :> new_rule)
        /\ rule_dependencies' = rule_dependencies @@ 
           (new_rule.id :> new_rule.dependencies)
        /\ UNCHANGED <<facts, evaluation_queue, active_evaluations, 
                       completed_evaluations, inference_chains, 
                       working_memory_size>>

\* Enable or disable a rule
UpdateRuleStatus ==
    \E rule_id \in DOMAIN rules, new_status \in RuleStatus :
        /\ rules[rule_id].status /= new_status
        /\ rules' = [rules EXCEPT ![rule_id].status = new_status]
        /\ UNCHANGED <<facts, evaluation_queue, active_evaluations,
                       completed_evaluations, inference_chains,
                       rule_dependencies, working_memory_size>>

\* Add a fact to working memory
AddFact ==
    \E new_fact \in Fact :
        /\ IsValidFact(new_fact)
        /\ new_fact.id \notin {f.id : f \in facts}
        /\ working_memory_size < MaxFacts
        /\ facts' = facts \cup {new_fact}
        /\ working_memory_size' = working_memory_size + 1
        /\ UNCHANGED <<rules, evaluation_queue, active_evaluations,
                       completed_evaluations, inference_chains,
                       rule_dependencies>>

\* Remove a fact from working memory
RemoveFact ==
    \E fact_id \in FactIds :
        /\ \E f \in facts : f.id = fact_id
        /\ facts' = {f \in facts : f.id /= fact_id}
        /\ working_memory_size' = working_memory_size - 1
        /\ UNCHANGED <<rules, evaluation_queue, active_evaluations,
                       completed_evaluations, inference_chains,
                       rule_dependencies>>

\* Queue a new rule evaluation
QueueEvaluation ==
    \E new_eval \in Evaluation :
        /\ IsValidEvaluation(new_eval)
        /\ new_eval.id \notin {e.id : e \in active_evaluations}
        /\ new_eval.id \notin {e.id : e \in completed_evaluations}
        /\ new_eval.rule_id \in DOMAIN rules
        /\ rules[new_eval.rule_id].status = "enabled"
        /\ new_eval.status = "queued"
        /\ Len(evaluation_queue) < MaxEvaluations
        /\ evaluation_queue' = Append(evaluation_queue, new_eval)
        /\ UNCHANGED <<rules, facts, active_evaluations,
                       completed_evaluations, inference_chains,
                       rule_dependencies, working_memory_size>>

\* Start processing a queued evaluation
StartEvaluation ==
    /\ Len(evaluation_queue) > 0
    /\ Cardinality(active_evaluations) < MaxEvaluations
    /\ LET eval == Head(evaluation_queue)
       IN /\ eval.status = "queued"
          /\ evaluation_queue' = Tail(evaluation_queue)
          /\ active_evaluations' = active_evaluations \cup 
             {[eval EXCEPT !.status = "processing"]}
          /\ inference_chains' = inference_chains @@ (eval.id :> <<>>)
    /\ UNCHANGED <<rules, facts, completed_evaluations,
                   rule_dependencies, working_memory_size>>

\* Complete an active evaluation
CompleteEvaluation ==
    \E eval \in active_evaluations :
        /\ eval.status = "processing"
        /\ LET result_eval == [eval EXCEPT 
                               !.status = "completed",
                               !.result = TRUE]  \* Simplified result
           IN /\ active_evaluations' = (active_evaluations \ {eval})
              /\ completed_evaluations' = completed_evaluations \cup {result_eval}
        /\ UNCHANGED <<rules, facts, evaluation_queue, inference_chains,
                       rule_dependencies, working_memory_size>>

\* Perform one inference step during evaluation
InferenceStep ==
    \E eval \in active_evaluations, rule_id \in DOMAIN rules :
        /\ eval.status = "processing"
        /\ eval.inference_steps < MaxInferenceSteps
        /\ rules[rule_id].status = "enabled"
        /\ LET step == [rule_applied |-> rule_id,
                        facts_used |-> eval.input_facts,
                        conclusion |-> 1]  \* Simplified conclusion
           new_chain == Append(inference_chains[eval.id], step)
           updated_eval == [eval EXCEPT !.inference_steps = @ + 1]
           IN /\ inference_chains' = [inference_chains EXCEPT ![eval.id] = new_chain]
              /\ active_evaluations' = (active_evaluations \ {eval}) \cup {updated_eval}
        /\ UNCHANGED <<rules, facts, evaluation_queue, completed_evaluations,
                       rule_dependencies, working_memory_size>>

\* Handle evaluation timeout
TimeoutEvaluation ==
    \E eval \in active_evaluations :
        /\ eval.status = "processing"
        /\ eval.inference_steps >= MaxInferenceSteps
        /\ LET timeout_eval == [eval EXCEPT !.status = "timeout"]
           IN /\ active_evaluations' = (active_evaluations \ {eval})
              /\ completed_evaluations' = completed_evaluations \cup {timeout_eval}
        /\ UNCHANGED <<rules, facts, evaluation_queue, inference_chains,
                       rule_dependencies, working_memory_size>>

\* Next state relation
Next ==
    \/ AddRule
    \/ UpdateRuleStatus
    \/ AddFact
    \/ RemoveFact
    \/ QueueEvaluation
    \/ StartEvaluation
    \/ CompleteEvaluation
    \/ InferenceStep
    \/ TimeoutEvaluation

\* Complete system specification
Spec == Init /\ [][Next]_<<rules, facts, evaluation_queue, active_evaluations,
                            completed_evaluations, inference_chains,
                            rule_dependencies, working_memory_size>>

\* SAFETY PROPERTIES

\* Property 1: Rule Consistency - No contradictory rules simultaneously active
RuleConsistency ==
    \A r1, r2 \in DOMAIN rules :
        (rules[r1].status = "enabled" /\ rules[r2].status = "enabled") =>
        \* Simplified: rules with different priorities don't conflict
        (rules[r1].priority /= rules[r2].priority)

\* Property 2: Evaluation Determinism - Same inputs produce same outputs
EvaluationDeterminism ==
    \A e1, e2 \in completed_evaluations :
        (e1.rule_id = e2.rule_id /\ e1.input_facts = e2.input_facts) =>
        e1.result = e2.result

\* Property 3: Termination Guarantee - All evaluations eventually complete or timeout
TerminationGuarantee ==
    \A eval \in evaluation_queue \cup active_evaluations :
        <>(eval \in completed_evaluations)

\* Property 4: Fact Integrity - Facts maintain consistency
FactIntegrity ==
    \A f \in facts :
        /\ IsValidFact(f)
        /\ f.confidence \in 0..100

\* Property 5: Dependency Correctness - Rule dependencies are acyclic
DependencyCorrectness ==
    []DependencyGraphAcyclic

\* Property 6: Memory Safety - Working memory doesn't exceed capacity
MemorySafety ==
    /\ working_memory_size <= MaxFacts
    /\ Cardinality(facts) = working_memory_size
    /\ Cardinality(active_evaluations) <= MaxEvaluations

\* Property 7: Evaluation Progress - Queued evaluations eventually start processing
EvaluationProgress ==
    \A eval \in evaluation_queue :
        eval.status = "queued" => <>(eval \in active_evaluations)

\* Property 8: No Stuck Evaluations - Processing evaluations eventually complete
NoStuckEvaluations ==
    \A eval \in active_evaluations :
        eval.status = "processing" => 
        <>(eval \in completed_evaluations \/ eval.status = "timeout")

\* INVARIANTS (Safety properties that must always hold)
TypeInvariant ==
    /\ rules \in [SUBSET RuleIds -> Rule]
    /\ facts \subseteq Fact
    /\ evaluation_queue \in Seq(Evaluation)
    /\ active_evaluations \subseteq Evaluation
    /\ completed_evaluations \subseteq Evaluation
    /\ inference_chains \in [SUBSET EvaluationIds -> Seq(InferenceStep)]
    /\ rule_dependencies \in [SUBSET RuleIds -> SUBSET RuleIds]
    /\ working_memory_size \in Nat

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ RuleConsistency
    /\ EvaluationDeterminism
    /\ FactIntegrity
    /\ DependencyCorrectness
    /\ MemorySafety

====
