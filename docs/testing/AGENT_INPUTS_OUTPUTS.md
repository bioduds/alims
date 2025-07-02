# ALims AI Agents: Inputs and Outputs Reference

This document provides a comprehensive overview of the inputs and outputs for each of the 5 AI agents in ALims.

## 🎭 1. UserInterfaceAgent

**Purpose**: Natural language processing and user interactions

### **Main Methods & I/O**

#### `process_chat_message(message, context)`
**Input:**
```python
message: str                    # User's chat message
context: Optional[Dict] = {     # Optional context
    "user_id": str,
    "context_type": str,        # "chat", "voice", etc.
    "interaction_type": str,
    "requires_action": bool
}
```

**Output:**
```python
{
    "success": bool,            # True if processed successfully
    "message": str,             # AI response text
    "agent": "user_interface",  # Agent identifier
    "interaction_id": int,      # Unique interaction number
    "response_time": float,     # Processing time in seconds
    "context_used": bool,       # Whether context was utilized
    "error": str               # Error message if success=False
}
```

#### `handle_voice_command(command, context)`
**Input:**
```python
command: str                   # Voice command text
context: Optional[Dict] = {    # Voice-specific context
    "interaction_type": "voice_command",
    "requires_action": True
}
```

**Output:**
```python
{
    "success": bool,
    "message": str,
    "input_type": "voice",     # Indicates voice input
    "system_action": Dict,     # If system action suggested
    "error": str
}
```

#### `generate_proactive_suggestions(context)`
**Input:**
```python
context: Optional[Dict] = {
    "user_patterns": List[str],    # ["productivity", "task_management"]
    "time_of_day": str,           # "morning", "afternoon", "evening"
    "system_state": Dict
}
```

**Output:**
```python
List[str]  # List of suggestion strings
# Example: ["Consider organizing your downloads folder", 
#          "Time for a 5-minute break", 
#          "Review your daily goals"]
```

#### `explain_system_action(action)`
**Input:**
```python
action: Dict = {
    "action": str,              # "file_organization", "system_update"
    "target": str,              # "/downloads", "system"
    "method": str,              # "smart_categorization"
    "parameters": Dict
}
```

**Output:**
```python
str  # User-friendly explanation
# Example: "I'm organizing your downloads folder by grouping 
#          similar files together to help you find things faster."
```

---

## 🎭 2. AgentOrchestrator

**Purpose**: Complex task coordination and delegation

### **Main Methods & I/O**

#### `coordinate_task(task_description, context)`
**Input:**
```python
task_description: str          # "Analyze user productivity and optimize workflow"
context: Optional[Dict] = {
    "user_data": Dict,         # {"daily_tasks": 15, "completion_rate": 0.8}
    "priority": str,           # "low", "normal", "high", "urgent"
    "deadline": str,
    "resources": Dict
}
```

**Output:**
```python
{
    "success": bool,
    "task_id": str,            # "task_0001"
    "orchestration_plan": {
        "plan": {
            "subtasks": List[Dict],
            "agent_assignments": Dict,
            "dependencies": List[str]
        }
    },
    "results": Dict,           # Execution results
    "execution_time": float,   # Time in seconds
    "agents_used": List[str],  # ["user_interface", "system_controller"]
    "error": str
}
```

#### `delegate_to_agent(agent_id, subtask)`
**Input:**
```python
agent_id: str                  # "user_interface", "system_controller"
subtask: Dict = {
    "id": str,                 # "test_subtask"
    "description": str,        # "Generate user-friendly summary"
    "input_data": Dict,        # {"metrics": {"tasks": 10, "completed": 8}}
    "priority": str,
    "deadline": str
}
```

**Output:**
```python
{
    "success": bool,
    "agent": str,              # Agent that handled the task
    "result": Any,             # Agent-specific result
    "execution_time": float,
    "error": str
}
```

#### `synthesize_results(agent_results)`
**Input:**
```python
agent_results: List[Dict] = [
    {"agent": "ui", "result": "User needs better time management"},
    {"agent": "system", "result": "System can automate 3 tasks"},
    {"agent": "pattern", "result": "Productivity peaks at 10 AM"}
]
```

**Output:**
```python
{
    "success": bool,
    "synthesized_result": str,     # Combined insights
    "confidence_score": float,     # 0.0-1.0
    "recommendations": List[str],  # Action items
    "supporting_evidence": Dict
}
```

#### `monitor_task_progress(task_id)`
**Input:**
```python
task_id: str  # "task_0001"
```

**Output:**
```python
{
    "success": bool,
    "task_id": str,
    "status": str,             # "pending", "in_progress", "completed", "failed"
    "progress": float,         # 0.0-1.0
    "completed_subtasks": int,
    "total_subtasks": int,
    "estimated_completion": str,  # ISO timestamp
    "current_step": str
}
```

---

## 🎛️ 3. SystemController

**Purpose**: Command translation and system action execution

### **Main Methods & I/O**

#### `translate_user_command(user_command, user_context)`
**Input:**
```python
user_command: str              # "Show me all running processes"
user_context: Dict = {
    "user_id": str,
    "security_level": str,     # "standard", "elevated", "restricted"
    "permissions": List[str],
    "current_directory": str
}
```

**Output:**
```python
SystemAction  # Complex dataclass with:
{
    "action_id": str,          # "action_0001"
    "intent_analysis": {
        "primary_goal": str,
        "command_type": CommandType,  # QUERY, ACTION, CONFIGURATION
        "complexity_level": ComplexityLevel,  # SIMPLE, MODERATE, COMPLEX
        "parameters": Dict,
        "confidence_score": float
    },
    "capability_assessment": {
        "required_capabilities": List[str],
        "available_resources": Dict,
        "feasibility_score": int,     # 1-10
        "required_agents": List[str],
        "resource_requirements": Dict
    },
    "safety_validation": {
        "risk_level": RiskLevel,      # LOW, MEDIUM, HIGH, CRITICAL
        "safety_concerns": List[str],
        "permission_requirements": List[str],
        "validation_status": ValidationStatus,
        "warnings": List[str]
    },
    "action_plan": {
        "execution_steps": List[Dict],
        "estimated_duration": float,
        "success_criteria": List[str],
        "rollback_plan": List[Dict],
        "dependencies": List[str]
    },
    "recommended_action": ActionType,  # EXECUTE, REQUEST_CONFIRMATION, DENY
    "justification": str,
    "user_feedback": str,
    "next_steps": List[str],
    "created_at": datetime
}
```

#### `execute_system_action(action)`
**Input:**
```python
action: SystemAction  # From translate_user_command()
```

**Output:**
```python
{
    "success": bool,
    "action_id": str,
    "execution_results": Dict,
    "steps_completed": int,
    "steps_failed": int,
    "execution_time": float,
    "rollback_performed": bool,
    "error": str
}
```

#### `validate_action_safety(action)`
**Input:**
```python
action: SystemAction
```

**Output:**
```python
bool  # True if safe to execute, False otherwise
```

#### `get_system_capabilities()`
**Input:**
```python
# No input parameters
```

**Output:**
```python
{
    "agent_management": {
        "can_create_agents": bool,
        "can_modify_agents": bool,
        "can_remove_agents": bool,
        "max_agents": int
    },
    "file_operations": {
        "can_read": bool,
        "can_write": bool,
        "can_execute": bool,
        "restricted_paths": List[str]
    },
    "system_control": {
        "can_restart_services": bool,
        "can_modify_config": bool,
        "can_install_software": bool
    },
    "resource_limits": {
        "max_memory_mb": int,
        "max_cpu_percent": float,
        "max_disk_gb": float
    }
}
```

---

## 🔍 4. PatternValidator

**Purpose**: Pattern classification validation and coherence

### **Main Methods & I/O**

#### `validate_single_pattern(pattern)`
**Input:**
```python
pattern: PatternClassification = {
    "pattern_id": str,         # "test_pattern_001"
    "category": str,           # "PRODUCTIVITY", "COMMUNICATION"
    "subcategory": str,        # "task_management", "email_handling"
    "confidence": float,       # 0.0-1.0
    "source_agent": str,       # "test_agent"
    "timestamp": datetime,
    "metadata": Dict
}
```

**Output:**
```python
ValidationResult = {
    "is_coherent": bool,
    "consistency_score": float,    # 0.0-1.0
    "quality_score": float,        # 0.0-1.0
    "conflicts_detected": List[str],
    "recommendations": List[str]
}
```

#### `cross_validate_agents(pattern_id, classifications)`
**Input:**
```python
pattern_id: str                # "shared_pattern_001"
classifications: List[PatternClassification]  # Multiple agent classifications
```

**Output:**
```python
{
    "pattern_id": str,
    "agent_count": int,
    "consistency_score": float,
    "conflicts": int,
    "recommended_classification": {
        "category": str,
        "confidence": float,
        "agent_count": int,
        "agreement_level": float
    },
    "actions_required": List[Dict]
}
```

#### `system_audit()`
**Input:**
```python
# No input parameters
```

**Output:**
```python
{
    "audit_id": str,
    "timestamp": str,              # ISO format
    "total_patterns": int,
    "system_health": str,          # "EXCELLENT", "GOOD", "FAIR", "POOR"
    "coherence_metrics": {
        "overall_consistency": float,
        "conflict_count": int,
        "quality_average": float,
        "improvement_areas": List[str]
    },
    "critical_actions": List[Dict],
    "recommendations": List[str]
}
```

#### `resolve_conflicts(pattern_id)`
**Input:**
```python
pattern_id: str  # Pattern with known conflicts
```

**Output:**
```python
{
    "pattern_id": str,
    "conflicts_resolved": int,
    "final_classification": Dict,
    "resolution_actions": List[Dict],
    "error": str  # If no conflicts found
}
```

---

## 💡 5. ProactiveSuggestionEngine

**Purpose**: Context-aware suggestion generation

### **Main Methods & I/O**

#### `generate_suggestions(context)`
**Input:**
```python
context: SuggestionContext = {
    "user_id": str,
    "current_activity": str,       # "coding", "writing", "research"
    "time_of_day": str,           # "morning", "afternoon", "evening"
    "day_of_week": str,           # "monday", "tuesday", etc.
    "recent_patterns": List[str],  # ["productivity", "development"]
    "productivity_metrics": {
        "focus_time": int,         # minutes
        "tasks_completed": int,
        "interruptions": int
    },
    "user_preferences": {
        "notification_style": str,  # "minimal", "detailed"
        "preferred_times": List[str]
    },
    "available_time": int,         # minutes
    "energy_level": str,          # "low", "medium", "high"
    "focus_areas": List[str]      # ["python", "ai_development"]
}
```

**Output:**
```python
List[ProactiveSuggestion] = [
    {
        "suggestion_id": str,
        "suggestion_type": SuggestionType,  # PRODUCTIVITY, WORKFLOW_OPTIMIZATION
        "priority": SuggestionPriority,     # LOW, NORMAL, HIGH, URGENT
        "timing": SuggestionTiming,         # IMMEDIATE, NEXT_SESSION, DAILY_DIGEST
        "title": str,
        "description": str,
        "rationale": str,
        "actionable_steps": List[str],
        "expected_benefit": str,
        "confidence_score": float,          # 0.0-1.0
        "created_at": datetime,
        "expires_at": datetime,
        "status": SuggestionStatus,         # PENDING, DELIVERED, ACCEPTED
        "context_triggers": List[str],
        "user_feedback": Optional[str],
        "effectiveness_score": Optional[float]
    }
]
```

#### `get_immediate_suggestions(user_id, max_count)`
**Input:**
```python
user_id: str
max_count: int = 3  # Maximum suggestions to return
```

**Output:**
```python
List[ProactiveSuggestion]  # Ready-to-show suggestions
```

#### `process_user_feedback(feedback)`
**Input:**
```python
feedback: SuggestionFeedback = {
    "suggestion_id": str,
    "user_id": str,
    "feedback_type": str,          # "accepted", "dismissed", "modified"
    "feedback_text": Optional[str],
    "effectiveness_rating": Optional[int],  # 1-5 scale
    "timestamp": datetime
}
```

**Output:**
```python
{
    "success": bool,
    "message": str,
    "updated_preferences": bool,
    "error": str
}
```

#### `get_suggestion_metrics()`
**Input:**
```python
# No input parameters
```

**Output:**
```python
SuggestionMetrics = {
    "total_suggestions": int,
    "delivered_suggestions": int,
    "accepted_suggestions": int,
    "dismissed_suggestions": int,
    "average_confidence": float,
    "average_effectiveness": float,
    "user_satisfaction": float,
    "response_rate": float
}
```

---

## 🔄 Inter-Agent Communication

### **Common Data Flow Patterns**

1. **User Request → UserInterfaceAgent → AgentOrchestrator → SystemController**
   ```
   User: "Optimize my workflow"
   → UI processes natural language
   → Orchestrator creates task plan
   → System executes safe actions
   ```

2. **Pattern Detection → PatternValidator → ProactiveSuggestionEngine**
   ```
   System detects user pattern
   → Validator ensures coherence
   → Suggestion engine generates recommendations
   ```

3. **Cross-Agent Validation**
   ```
   Multiple agents classify same pattern
   → PatternValidator resolves conflicts
   → System maintains coherence
   ```

### **Shared Data Structures**

- **Context Objects**: Passed between agents for continuity
- **Timestamps**: All outputs include ISO format timestamps
- **Success/Error Pattern**: Consistent `{"success": bool, "error": str}` structure
- **Agent Identification**: All outputs include agent identifier
- **Confidence Scores**: 0.0-1.0 scale for AI-generated content

This comprehensive I/O reference enables developers to understand exactly what data each agent expects and produces, facilitating integration and debugging.