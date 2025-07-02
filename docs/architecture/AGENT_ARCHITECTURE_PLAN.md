# ALims True Agent Architecture Plan

## Current Problem
The existing "agents" are NOT real agents - they're just wrapper functions around the same Gemma 3:4b model. This is fundamentally wrong.

## True Agent Requirements

### 1. Small Neural Networks (1M-10M parameters each)
- **UserInterfaceAgent**: 2M params - Natural language understanding for chat/voice
- **TaskOrchestrator**: 5M params - Task decomposition and coordination  
- **SystemController**: 3M params - Command translation and safety validation
- **PatternValidator**: 1M params - Pattern coherence checking
- **ProactiveSuggester**: 2M params - Context-aware suggestion generation

### 2. Meta-Learning Training Pipeline

#### Phase 1: Data Preparation
```python
# From SQLite event database
events = load_events_from_db()
clustered_data = cluster_events(events)  # K-means/DBSCAN
feature_vectors = extract_features(clustered_data)
```

#### Phase 2: Meta-Learning with Gemma 3:4b
```python
# Gemma 3:4b acts as the "teacher"
for cluster in clustered_data:
    # Generate labels
    labels = gemma_generate_labels(cluster)
    
    # Design network architecture
    architecture = gemma_design_network(cluster.complexity)
    
    # Create training curriculum
    curriculum = gemma_create_curriculum(cluster.patterns)
    
    # Generate training examples
    training_data = gemma_augment_data(cluster, labels)
```

#### Phase 3: Small Network Training
```python
# Train specialized networks
for agent_type in ['ui', 'orchestrator', 'system', 'pattern', 'suggestion']:
    network = create_small_network(agent_type, max_params=target_params[agent_type])
    
    # Supervised learning from Gemma labels
    train_network(network, training_data[agent_type], labels[agent_type])
    
    # Validate against holdout set
    performance = validate_network(network, holdout_data)
    
    # Check for overfitting
    overfitting_score = detect_overfitting(network, train_data, val_data)
    
    if performance > threshold and overfitting_score < max_overfitting:
        deploy_agent(network, agent_type)
```

### 3. Agent Input/Output Specifications

#### UserInterfaceAgent
```python
Input: {
    "message": str,           # User message
    "context": Dict[str, Any], # Conversation context
    "modality": str           # "text" | "voice"
}

Output: {
    "response": str,          # Generated response
    "confidence": float,      # 0.0-1.0
    "intent": str,           # Detected intent
    "requires_action": bool   # Needs system action
}
```

#### TaskOrchestrator  
```python
Input: {
    "task": str,             # Task description
    "available_agents": List[str], # Available agents
    "context": Dict[str, Any] # System context
}

Output: {
    "plan": List[Dict],      # Execution plan
    "agent_assignments": Dict, # Agent -> subtask mapping
    "estimated_time": float,  # Seconds
    "success_probability": float # 0.0-1.0
}
```

#### SystemController
```python
Input: {
    "command": str,          # Natural language command
    "user_context": Dict,    # User preferences/history
    "safety_level": str      # "low" | "medium" | "high"
}

Output: {
    "actions": List[Dict],   # System actions to execute
    "safety_score": float,   # 0.0-1.0 (higher = safer)
    "requires_confirmation": bool,
    "risk_assessment": Dict  # Detailed risk analysis
}
```

#### PatternValidator
```python
Input: {
    "pattern": Dict,         # Pattern to validate
    "context": Dict,         # System context
    "other_patterns": List[Dict] # Related patterns
}

Output: {
    "is_valid": bool,        # Pattern validity
    "confidence": float,     # Validation confidence
    "conflicts": List[str],  # Conflicting patterns
    "suggestions": List[str] # Improvement suggestions
}
```

#### ProactiveSuggester
```python
Input: {
    "user_state": Dict,      # Current user context
    "recent_activity": List[Dict], # Recent events
    "time_context": Dict     # Time/schedule info
}

Output: {
    "suggestions": List[Dict], # Proactive suggestions
    "priorities": List[float], # Suggestion priorities
    "timing": List[str],      # When to show suggestions
    "rationale": List[str]    # Why each suggestion
}
```

## Implementation Steps

### Step 1: Data Pipeline
1. ✅ Event database exists (`data/alims_events.db`)
2. ❌ Need clustering system for event data
3. ❌ Need feature extraction from clusters
4. ❌ Need training/validation data splits

### Step 2: Meta-Learning System
1. ❌ Gemma 3:4b teacher system for label generation
2. ❌ Architecture design system (network topology)
3. ❌ Curriculum learning system (training progression)
4. ❌ Data augmentation system (synthetic examples)

### Step 3: Small Network Training
1. ❌ PyTorch/TensorFlow training pipeline
2. ❌ Overfitting detection system
3. ❌ Performance validation system
4. ❌ Model compression/quantization

### Step 4: Agent Deployment
1. ❌ Model serving infrastructure
2. ❌ Input/output validation
3. ❌ Performance monitoring
4. ❌ Continuous learning system

## Key Differences from Current System

### Current (Wrong) ❌
```python
# All "agents" just call the same model
response = await self.central_brain.ollama_client.generate_response(prompt)
```

### Proposed (Correct) ✅
```python
# Each agent is a specialized neural network
class UserInterfaceAgent(nn.Module):
    def __init__(self):
        super().__init__()
        self.encoder = nn.TransformerEncoder(...)  # 2M params
        self.classifier = nn.Linear(...)
        
    def forward(self, input_ids, attention_mask):
        # Actual neural network inference
        return self.classifier(self.encoder(input_ids))

# Load trained weights
agent = UserInterfaceAgent()
agent.load_state_dict(torch.load('models/ui_agent.pth'))

# Direct inference (no LLM calls)
output = agent(input_tensor)
```

## Success Metrics

1. **Training Success**: Each agent achieves >90% accuracy on validation set
2. **Overfitting Control**: Validation accuracy within 5% of training accuracy  
3. **Performance**: Agent inference <100ms per request
4. **Specialization**: Each agent clearly outperforms others in its domain
5. **Resource Efficiency**: Total agent memory <100MB (vs 4GB for Gemma)

## Timeline

- **Week 1**: Data clustering and feature extraction
- **Week 2**: Meta-learning system with Gemma 3:4b teacher
- **Week 3**: Small network training pipeline
- **Week 4**: Agent validation and deployment system
- **Week 5**: Integration testing and performance optimization

This is the proper way to build AI agents - not wrapper functions around LLMs! 