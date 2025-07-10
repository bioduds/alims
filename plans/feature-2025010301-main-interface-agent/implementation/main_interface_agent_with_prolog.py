"""
Enhanced Main Interface Agent with PredicateLogic-style logical reasoning capabilities.
This implementation demonstrates how to integrate logical programming concepts
into our agent orchestration system.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional, Any, Union
from enum import Enum
import uuid
import time
from collections import deque
import copy

class ConversationState(Enum):
    ACTIVE = "ACTIVE"
    WAITING_AGENT = "WAITING_AGENT"
    PROCESSING = "PROCESSING"
    COMPLETED = "COMPLETED"
    ESCALATED = "ESCALATED"
    LOGICAL_REASONING = "LOGICAL_REASONING"

class AgentState(Enum):
    IDLE = "IDLE"
    BUSY = "BUSY"
    ERROR = "ERROR"
    OFFLINE = "OFFLINE"
    REASONING = "REASONING"

class CentralBrainState(Enum):
    INITIALIZING = "INITIALIZING"
    READY = "READY"
    ORCHESTRATING = "ORCHESTRATING"
    ERROR = "ERROR"
    PREDICATE_LOGIC_INFERENCE = "PREDICATE_LOGIC_INFERENCE"

class RequestType(Enum):
    SAMPLE_INQUIRY = "SAMPLE_INQUIRY"
    WORKFLOW_COMMAND = "WORKFLOW_COMMAND"
    SYSTEM_QUERY = "SYSTEM_QUERY"
    AGENT_REQUEST = "AGENT_REQUEST"
    LOGICAL_QUERY = "LOGICAL_QUERY"

class PredicateLogicRuleType(Enum):
    FACT = "FACT"
    RULE = "RULE"
    QUERY = "QUERY"

class InferenceState(Enum):
    PENDING = "PENDING"
    UNIFIED = "UNIFIED"
    FAILED = "FAILED"
    BACKTRACK = "BACKTRACK"
    SUCCESS = "SUCCESS"

@dataclass
class PredicateLogicTerm:
    """Represents a PredicateLogic term (atom, variable, or compound)"""
    functor: str
    args: List[Union[str, 'PredicateLogicTerm']] = field(default_factory=list)
    is_variable: bool = False
    
    def __str__(self):
        if self.is_variable:
            return f"?{self.functor}"
        if not self.args:
            return self.functor
        args_str = ", ".join(str(arg) for arg in self.args)
        return f"{self.functor}({args_str})"

@dataclass
class PredicateLogicRule:
    """Represents a PredicateLogic fact or rule"""
    rule_type: PredicateLogicRuleType
    head: PredicateLogicTerm
    body: List[PredicateLogicTerm] = field(default_factory=list)
    
    def __str__(self):
        if self.rule_type == PredicateLogicRuleType.FACT:
            return f"{self.head}."
        else:
            body_str = ", ".join(str(term) for term in self.body)
            return f"{self.head} :- {body_str}."

@dataclass
class Substitution:
    """Variable substitution/unification bindings"""
    bindings: Dict[str, Union[str, PredicateLogicTerm]] = field(default_factory=dict)
    
    def bind(self, var: str, value: Union[str, PredicateLogicTerm]) -> 'Substitution':
        """Create new substitution with additional binding"""
        new_bindings = self.bindings.copy()
        new_bindings[var] = value
        return Substitution(new_bindings)
    
    def apply(self, term: PredicateLogicTerm) -> PredicateLogicTerm:
        """Apply substitution to a term"""
        if term.is_variable and term.functor in self.bindings:
            return self.bindings[term.functor]
        elif term.args:
            new_args = [self.apply(arg) if isinstance(arg, PredicateLogicTerm) else arg 
                       for arg in term.args]
            return PredicateLogicTerm(term.functor, new_args, term.is_variable)
        return term

@dataclass
class QueryFrame:
    """Represents a query frame in the inference stack"""
    conversation_id: str
    goal: PredicateLogicTerm
    state: InferenceState
    depth: int
    choice_point: int = 0
    substitution: Substitution = field(default_factory=Substitution)
    remaining_goals: List[PredicateLogicTerm] = field(default_factory=list)

@dataclass
class InferenceChain:
    """Tracks the logical inference process"""
    conversation_id: str
    original_query: PredicateLogicTerm
    result: str
    solution_bindings: Substitution = field(default_factory=Substitution)
    proof_steps: List[str] = field(default_factory=list)
    timestamp: float = field(default_factory=time.time)

class PredicateLogicEngine:
    """Simple PredicateLogic inference engine for logical reasoning"""
    
    def __init__(self):
        self.knowledge_base: List[PredicateLogicRule] = []
        self.query_stack: deque[QueryFrame] = deque()
        self.max_depth = 100
        
    def add_fact(self, predicate: str, *args) -> None:
        """Add a fact to the knowledge base"""
        terms = [PredicateLogicTerm(str(arg)) if not isinstance(arg, PredicateLogicTerm) else arg 
                for arg in args]
        fact = PredicateLogicRule(
            PredicateLogicRuleType.FACT,
            PredicateLogicTerm(predicate, terms)
        )
        self.knowledge_base.append(fact)
        
    def add_rule(self, head_pred: str, head_args: List[str], 
                 body_goals: List[Tuple[str, List[str]]]) -> None:
        """Add a rule to the knowledge base"""
        head_terms = [PredicateLogicTerm(arg, [], arg.startswith('?')) for arg in head_args]
        head = PredicateLogicTerm(head_pred, head_terms)
        
        body = []
        for pred, args in body_goals:
            arg_terms = [PredicateLogicTerm(arg, [], arg.startswith('?')) for arg in args]
            body.append(PredicateLogicTerm(pred, arg_terms))
            
        rule = PredicateLogicRule(PredicateLogicRuleType.RULE, head, body)
        self.knowledge_base.append(rule)
        
    def unify(self, term1: PrologTerm, term2: PrologTerm, 
              subst: Substitution) -> Optional[Substitution]:
        """Attempt to unify two terms"""
        # Apply current substitution
        t1 = subst.apply(term1)
        t2 = subst.apply(term2)
        
        # If either is a variable, bind it
        if t1.is_variable:
            return subst.bind(t1.functor, t2)
        if t2.is_variable:
            return subst.bind(t2.functor, t1)
            
        # Both are non-variables - must match exactly
        if t1.functor != t2.functor or len(t1.args) != len(t2.args):
            return None
            
        # Unify arguments recursively
        current_subst = subst
        for arg1, arg2 in zip(t1.args, t2.args):
            if isinstance(arg1, PrologTerm) and isinstance(arg2, PrologTerm):
                current_subst = self.unify(arg1, arg2, current_subst)
                if current_subst is None:
                    return None
            elif arg1 != arg2:
                return None
                
        return current_subst
        
    def find_matching_rules(self, goal: PrologTerm) -> List[Tuple[PrologRule, Substitution]]:
        """Find all rules that could match the goal"""
        matches = []
        for rule in self.knowledge_base:
            # Create fresh variable names for the rule
            fresh_rule = self._rename_variables(rule)
            unification = self.unify(goal, fresh_rule.head, Substitution())
            if unification is not None:
                matches.append((fresh_rule, unification))
        return matches
        
    def _rename_variables(self, rule: PrologRule) -> PrologRule:
        """Create a copy of the rule with fresh variable names"""
        suffix = str(uuid.uuid4())[:8]
        return self._rename_term_variables(rule, suffix)
        
    def _rename_term_variables(self, obj: Any, suffix: str) -> Any:
        """Recursively rename variables in a term or rule"""
        if isinstance(obj, PrologTerm):
            if obj.is_variable:
                return PrologTerm(f"{obj.functor}_{suffix}", [], True)
            else:
                new_args = [self._rename_term_variables(arg, suffix) for arg in obj.args]
                return PrologTerm(obj.functor, new_args, obj.is_variable)
        elif isinstance(obj, PrologRule):
            new_head = self._rename_term_variables(obj.head, suffix)
            new_body = [self._rename_term_variables(term, suffix) for term in obj.body]
            return PrologRule(obj.rule_type, new_head, new_body)
        elif isinstance(obj, list):
            return [self._rename_term_variables(item, suffix) for item in obj]
        else:
            return obj
            
    def query(self, conversation_id: str, goal: PrologTerm) -> Optional[InferenceChain]:
        """Execute a logical query and return the inference chain"""
        initial_frame = QueryFrame(
            conversation_id=conversation_id,
            goal=goal,
            state=InferenceState.PENDING,
            depth=0
        )
        
        self.query_stack.clear()
        self.query_stack.append(initial_frame)
        
        inference_chain = InferenceChain(
            conversation_id=conversation_id,
            original_query=goal,
            result="PENDING"
        )
        
        while self.query_stack and len(self.query_stack) < self.max_depth:
            success, result = self._process_query_step(inference_chain)
            if success:
                inference_chain.result = "SUCCESS"
                return inference_chain
            elif result == "FAILED":
                inference_chain.result = "FAILED"
                return inference_chain
                
        inference_chain.result = "TIMEOUT"
        return inference_chain
        
    def _process_query_step(self, inference_chain: InferenceChain) -> Tuple[bool, str]:
        """Process one step of the query resolution"""
        if not self.query_stack:
            return False, "FAILED"
            
        current_frame = self.query_stack.pop()
        goal = current_frame.substitution.apply(current_frame.goal)
        
        # Find matching rules
        matches = self.find_matching_rules(goal)
        
        if not matches:
            # No matches - backtrack
            inference_chain.proof_steps.append(f"Failed to match: {goal}")
            return False, "CONTINUE"
            
        # Try each match (choice points for backtracking)
        for rule, unification in matches:
            inference_chain.proof_steps.append(f"Trying rule: {rule}")
            
            if rule.rule_type == PrologRuleType.FACT:
                # Fact matches - success for this goal
                inference_chain.solution_bindings = unification
                inference_chain.proof_steps.append(f"Unified with fact: {rule.head}")
                
                # Check if there are remaining goals in the frame
                if current_frame.remaining_goals:
                    # Add next goal to stack
                    next_goal = current_frame.remaining_goals[0]
                    remaining = current_frame.remaining_goals[1:]
                    new_frame = QueryFrame(
                        conversation_id=current_frame.conversation_id,
                        goal=next_goal,
                        state=InferenceState.PENDING,
                        depth=current_frame.depth,
                        substitution=unification,
                        remaining_goals=remaining
                    )
                    self.query_stack.append(new_frame)
                    return False, "CONTINUE"
                else:
                    # No more goals - complete success
                    return True, "SUCCESS"
                    
            else:  # Rule
                # Add rule body goals to stack
                if rule.body:
                    # Add goals in reverse order (stack is LIFO)
                    for i in range(len(rule.body) - 1, -1, -1):
                        goal_frame = QueryFrame(
                            conversation_id=current_frame.conversation_id,
                            goal=rule.body[i],
                            state=InferenceState.PENDING,
                            depth=current_frame.depth + 1,
                            substitution=unification,
                            remaining_goals=rule.body[i+1:] if i < len(rule.body) - 1 else []
                        )
                        self.query_stack.append(goal_frame)
                    return False, "CONTINUE"
                else:
                    # Empty body rule (should not happen, but handle gracefully)
                    return True, "SUCCESS"
                    
        return False, "FAILED"

class EnhancedMainInterfaceAgent:
    """Main Interface Agent with Prolog-style logical reasoning capabilities"""
    
    def __init__(self, max_conversations: int = 10, max_agents: int = 20):
        self.state = CentralBrainState.INITIALIZING
        self.max_conversations = max_conversations
        self.max_agents = max_agents
        
        # Core state
        self.conversations: Dict[str, ConversationState] = {}
        self.conversation_contexts: Dict[str, Dict] = {}
        self.available_agents: Dict[str, Tuple[AgentState, str]] = {}
        self.agent_registry: Dict[str, str] = {}
        self.user_requests: deque = deque()
        self.agent_responses: deque = deque()
        
        # Enhanced with Prolog engine
        self.prolog_engine = PrologEngine()
        self.inference_chains: Dict[str, InferenceChain] = {}
        self.logical_goals: Set[str] = set()
        
        self._initialize_knowledge_base()
        
    def _initialize_knowledge_base(self):
        """Initialize the Prolog knowledge base with domain facts and rules"""
        # Add facts about agent capabilities
        self.prolog_engine.add_fact("has_capability", "sample_tracker", "sample_analysis")
        self.prolog_engine.add_fact("has_capability", "workflow_manager", "workflow_control")
        self.prolog_engine.add_fact("has_capability", "qc_analyzer", "quality_control")
        self.prolog_engine.add_fact("has_capability", "report_generator", "report_creation")
        
        # Add facts about request types and their requirements
        self.prolog_engine.add_fact("requires_capability", "sample_inquiry", "sample_analysis")
        self.prolog_engine.add_fact("requires_capability", "workflow_command", "workflow_control")
        self.prolog_engine.add_fact("requires_capability", "qc_request", "quality_control")
        
        # Add rules for agent selection
        self.prolog_engine.add_rule(
            "suitable_agent", ["?Agent", "?RequestType"],
            [
                ("requires_capability", ["?RequestType", "?Capability"]),
                ("has_capability", ["?Agent", "?Capability"])
            ]
        )
        
        # Add rules for workflow dependencies
        self.prolog_engine.add_rule(
            "depends_on", ["?WorkflowA", "?WorkflowB"],
            [
                ("workflow_step", ["?WorkflowA", "?StepA"]),
                ("workflow_step", ["?WorkflowB", "?StepB"]),
                ("step_dependency", ["?StepA", "?StepB"])
            ]
        )
        
        # Add facts about workflow steps
        self.prolog_engine.add_fact("workflow_step", "sample_processing", "sample_intake")
        self.prolog_engine.add_fact("workflow_step", "sample_processing", "qc_check")
        self.prolog_engine.add_fact("workflow_step", "sample_processing", "analysis")
        self.prolog_engine.add_fact("workflow_step", "sample_processing", "report_generation")
        
        # Add step dependencies
        self.prolog_engine.add_fact("step_dependency", "qc_check", "sample_intake")
        self.prolog_engine.add_fact("step_dependency", "analysis", "qc_check")
        self.prolog_engine.add_fact("step_dependency", "report_generation", "analysis")
        
    def initialize(self) -> bool:
        """Initialize the enhanced agent system"""
        if self.state != CentralBrainState.INITIALIZING:
            return False
            
        # Register basic agents
        self.register_agent("sample_tracker", "sample_analysis")
        self.register_agent("workflow_manager", "workflow_control")
        self.register_agent("qc_analyzer", "quality_control")
        self.register_agent("logical_reasoner", "logical_reasoning")
        
        self.state = CentralBrainState.READY
        return True
        
    def register_agent(self, agent_id: str, capabilities: str) -> bool:
        """Register a new specialized agent"""
        if len(self.available_agents) >= self.max_agents:
            return False
            
        self.available_agents[agent_id] = (AgentState.IDLE, capabilities)
        self.agent_registry[agent_id] = capabilities
        
        # Add to Prolog knowledge base
        self.prolog_engine.add_fact("has_capability", agent_id, capabilities)
        
        return True
        
    def start_conversation(self, conversation_id: str = None) -> str:
        """Start a new conversation"""
        if conversation_id is None:
            conversation_id = str(uuid.uuid4())
            
        if len(self.conversations) >= self.max_conversations:
            raise Exception("Maximum conversations reached")
            
        self.conversations[conversation_id] = ConversationState.ACTIVE
        self.conversation_contexts[conversation_id] = {
            'messages': [],
            'current_context': {},
            'active_agents': set(),
            'user_intent': 'UNKNOWN',
            'reasoning_chain': None
        }
        
        return conversation_id
        
    def send_message(self, conversation_id: str, message: str, 
                    message_type: RequestType = RequestType.SAMPLE_INQUIRY,
                    priority: str = "NORMAL") -> Dict:
        """Send a message and get response"""
        if conversation_id not in self.conversations:
            return {"success": False, "error": "Conversation not found"}
            
        # Add user message to context
        self.conversation_contexts[conversation_id]['messages'].append({
            'role': 'user',
            'content': message,
            'timestamp': time.time()
        })
        
        # Determine if this requires logical reasoning
        if message_type == RequestType.LOGICAL_QUERY or "why" in message.lower() or "explain" in message.lower():
            return self._handle_logical_query(conversation_id, message)
        else:
            return self._handle_regular_query(conversation_id, message, message_type)
            
    def _handle_logical_query(self, conversation_id: str, message: str) -> Dict:
        """Handle queries that require logical reasoning"""
        self.state = CentralBrainState.PROLOG_INFERENCE
        self.conversations[conversation_id] = ConversationState.LOGICAL_REASONING
        
        # Parse the message to create a logical query
        # For demo purposes, we'll create some example queries
        if "suitable agent" in message.lower():
            # Extract request type from message
            request_type = "sample_inquiry"  # Default
            if "workflow" in message.lower():
                request_type = "workflow_command"
            elif "qc" in message.lower() or "quality" in message.lower():
                request_type = "qc_request"
                
            goal = PrologTerm("suitable_agent", [
                PrologTerm("?Agent", [], True),
                PrologTerm(request_type)
            ])
        elif "workflow dependency" in message.lower():
            goal = PrologTerm("depends_on", [
                PrologTerm("?WorkflowA", [], True),
                PrologTerm("?WorkflowB", [], True)
            ])
        else:
            # Default query
            goal = PrologTerm("has_capability", [
                PrologTerm("?Agent", [], True),
                PrologTerm("?Capability", [], True)
            ])
            
        # Execute logical inference
        inference_chain = self.prolog_engine.query(conversation_id, goal)
        
        if inference_chain:
            self.inference_chains[conversation_id] = inference_chain
            
            # Create response based on inference result
            if inference_chain.result == "SUCCESS":
                response_content = f"Logical reasoning completed successfully. "
                if inference_chain.solution_bindings.bindings:
                    bindings_str = ", ".join([f"{k}={v}" for k, v in inference_chain.solution_bindings.bindings.items()])
                    response_content += f"Found solution: {bindings_str}"
                else:
                    response_content += "Query confirmed as true."
                    
                response_content += f"\n\nReasoning steps:\n" + "\n".join(inference_chain.proof_steps)
            else:
                response_content = f"Logical reasoning failed: {inference_chain.result}"
                if inference_chain.proof_steps:
                    response_content += f"\n\nAttempted steps:\n" + "\n".join(inference_chain.proof_steps)
        else:
            response_content = "Logical inference could not be completed"
            
        # Add response to conversation
        self.conversation_contexts[conversation_id]['messages'].append({
            'role': 'assistant',
            'content': response_content,
            'agent_source': 'logical_reasoner',
            'reasoning_chain': inference_chain.proof_steps if inference_chain else [],
            'timestamp': time.time()
        })
        
        self.state = CentralBrainState.READY
        self.conversations[conversation_id] = ConversationState.ACTIVE
        
        return {
            "success": True,
            "messages": self.conversation_contexts[conversation_id]['messages'],
            "reasoning_used": True,
            "inference_result": inference_chain.result if inference_chain else "FAILED"
        }
        
    def _handle_regular_query(self, conversation_id: str, message: str, 
                            message_type: RequestType) -> Dict:
        """Handle regular queries using traditional agent orchestration"""
        self.state = CentralBrainState.ORCHESTRATING
        
        # Determine required capabilities
        capability_map = {
            RequestType.SAMPLE_INQUIRY: "sample_analysis",
            RequestType.WORKFLOW_COMMAND: "workflow_control",
            RequestType.SYSTEM_QUERY: "system_monitoring"
        }
        
        required_capability = capability_map.get(message_type, "general")
        
        # Find suitable agents
        suitable_agents = [
            agent_id for agent_id, (state, capability) in self.available_agents.items()
            if state == AgentState.IDLE and capability == required_capability
        ]
        
        if suitable_agents:
            selected_agent = suitable_agents[0]
            
            # Generate intelligent response based on message type and content
            response_content = self._generate_intelligent_response(message, message_type)
            
            # Add response to conversation
            self.conversation_contexts[conversation_id]['messages'].append({
                'role': 'assistant',
                'content': response_content,
                'agent_source': selected_agent,
                'timestamp': time.time()
            })
        else:
            # No suitable agents available
            response_content = f"No agents available for {message_type.value}. Please try again later."
            self.conversation_contexts[conversation_id]['messages'].append({
                'role': 'assistant',
                'content': response_content,
                'agent_source': 'system',
                'timestamp': time.time()
            })
            
        self.state = CentralBrainState.READY
        
        return {
            "success": True,
            "messages": self.conversation_contexts[conversation_id]['messages'],
            "reasoning_used": False
        }
        
    def _generate_intelligent_response(self, message: str, message_type: RequestType) -> str:
        """Generate context-aware responses based on message content and type"""
        message_lower = message.lower()
        
        if message_type == RequestType.SAMPLE_INQUIRY:
            if "register" in message_lower:
                return "I'll help you register a new sample. Please provide the sample ID, type, and any special handling requirements."
            elif "track" in message_lower or "status" in message_lower:
                return "I'm checking the sample tracking system. Current samples show various stages: receiving, analysis, and reporting. Would you like details on a specific sample?"
            elif "results" in message_lower:
                return "Sample analysis results are available. I can provide detailed reports including QC data, method validation, and compliance summaries."
            else:
                return "I'm ready to assist with sample management. I can help with registration, tracking, status updates, and results reporting."
                
        elif message_type == RequestType.WORKFLOW_COMMAND:
            if "start" in message_lower:
                return "Initiating workflow sequence. I'll coordinate the sample processing pipeline including intake → QC check → analysis → reporting."
            elif "pause" in message_lower or "stop" in message_lower:
                return "Workflow paused. All active processes are safely halted. Use 'resume' to continue or 'restart' for a fresh start."
            elif "status" in message_lower:
                return "Current workflow status: 3 samples in analysis, 2 pending QC, 1 awaiting report generation. All systems operational."
            else:
                return "Workflow management ready. I can start, pause, monitor, and optimize laboratory processes."
                
        elif message_type == RequestType.LOGICAL_QUERY:
            return "Engaging logical reasoning engine. I'll use Prolog-style inference to analyze your query and provide structured logical conclusions."
            
        else:
            return f"I understand you're asking about {message_type.value}. How can I assist you specifically?"
            
    def add_prolog_rule(self, head_predicate: str, head_args: List[str], 
                       body_goals: List[Tuple[str, List[str]]] = None) -> bool:
        """Add a new Prolog rule to the knowledge base"""
        try:
            if body_goals is None:
                # Adding a fact
                self.prolog_engine.add_fact(head_predicate, *head_args)
            else:
                # Adding a rule
                self.prolog_engine.add_rule(head_predicate, head_args, body_goals)
            return True
        except Exception as e:
            print(f"Error adding Prolog rule: {e}")
            return False
            
    def query_knowledge_base(self, conversation_id: str, predicate: str, 
                           args: List[str]) -> Optional[InferenceChain]:
        """Query the Prolog knowledge base directly"""
        # Convert arguments to PrologTerms
        term_args = [PrologTerm(arg, [], arg.startswith('?')) for arg in args]
        goal = PrologTerm(predicate, term_args)
        
        return self.prolog_engine.query(conversation_id, goal)
        
    def get_conversation_messages(self, conversation_id: str) -> List[Dict]:
        """Get all messages for a conversation"""
        if conversation_id not in self.conversation_contexts:
            return []
        return self.conversation_contexts[conversation_id]['messages']
        
    def get_knowledge_base_summary(self) -> Dict:
        """Get a summary of the current knowledge base"""
        facts = [rule for rule in self.prolog_engine.knowledge_base if rule.rule_type == PrologRuleType.FACT]
        rules = [rule for rule in self.prolog_engine.knowledge_base if rule.rule_type == PrologRuleType.RULE]
        
        return {
            "total_facts": len(facts),
            "total_rules": len(rules),
            "facts": [str(fact) for fact in facts[:10]],  # Show first 10
            "rules": [str(rule) for rule in rules[:10]]   # Show first 10
        }

# Example usage and demonstration
if __name__ == "__main__":
    # Create enhanced agent
    agent = EnhancedMainInterfaceAgent()
    agent.initialize()
    
    print("Enhanced Main Interface Agent with Prolog reasoning initialized!")
    print("\nKnowledge Base Summary:")
    kb_summary = agent.get_knowledge_base_summary()
    print(f"Facts: {kb_summary['total_facts']}, Rules: {kb_summary['total_rules']}")
    
    # Start a conversation
    conv_id = agent.start_conversation()
    
    # Test regular queries
    print(f"\n--- Testing Regular Queries ---")
    response = agent.send_message(conv_id, "I need to register a new sample", RequestType.SAMPLE_INQUIRY)
    print(f"Response: {response['messages'][-1]['content']}")
    
    response = agent.send_message(conv_id, "Start the workflow process", RequestType.WORKFLOW_COMMAND)
    print(f"Response: {response['messages'][-1]['content']}")
    
    # Test logical queries
    print(f"\n--- Testing Logical Queries ---")
    response = agent.send_message(conv_id, "Which agent is suitable for sample_inquiry?", RequestType.LOGICAL_QUERY)
    print(f"Logical Response: {response['messages'][-1]['content']}")
    print(f"Reasoning used: {response['reasoning_used']}")
    print(f"Inference result: {response['inference_result']}")
    
    # Add new knowledge and test
    print(f"\n--- Adding New Knowledge ---")
    agent.add_prolog_rule("can_handle", ["?Agent", "?Task"], [
        ("has_capability", ["?Agent", "?Capability"]),
        ("requires_capability", ["?Task", "?Capability"])
    ])
    
    # Query with new rule
    inference = agent.query_knowledge_base(conv_id, "can_handle", ["?Agent", "sample_inquiry"])
    if inference and inference.result == "SUCCESS":
        print(f"Query result: {inference.solution_bindings.bindings}")
        print(f"Proof steps: {len(inference.proof_steps)} steps")
    
    print(f"\nTotal messages in conversation: {len(agent.get_conversation_messages(conv_id))}")
