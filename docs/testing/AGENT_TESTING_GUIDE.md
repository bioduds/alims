# ALims AI Agents Testing Guide

This guide shows you how to test the 5 AI agents that exist in ALims and verify their functionality.

## 🤖 The 5 AI Agents

Based on code analysis, ALims has these **5 actual AI agents**:

1. **UserInterfaceAgent** - Natural language processing and user interactions
2. **AgentOrchestrator** - Complex task coordination and delegation  
3. **SystemController** - Command translation and system action execution
4. **PatternValidator** - Pattern classification validation and coherence
5. **ProactiveSuggestionEngine** - Context-aware suggestion generation

> **Note**: The chat previously reported 6 agents, but `VoiceInterface` is a system component for voice I/O, not an AI agent.

## 🧪 Testing Methods

### Method 1: Comprehensive Test Suite (Recommended)

Use the comprehensive test script that tests all agents:

```bash
# Test all agents
python test_all_agents.py

# Test specific agent only
python test_all_agents.py --agent ui
python test_all_agents.py --agent orchestrator  
python test_all_agents.py --agent system
python test_all_agents.py --agent pattern
python test_all_agents.py --agent suggestion
python test_all_agents.py --agent integration

# Verbose output
python test_all_agents.py --verbose
```

### Method 2: Individual Agent Tests

Test specific agents using existing test files:

```bash
# Test PatternValidator specifically
python test_pattern_validator.py

# Test complete system integration
python test_complete_system.py
```

### Method 3: Interactive Chat Testing

Test agents through the chat interface:

```bash
# Start the chat interface
python test_chat_standalone.py
```

Then ask questions like:
- "How many agents are active?" (should report 5, not 6)
- "What can each agent do?"
- "Help me organize my tasks" (tests UserInterfaceAgent)
- "Show system status" (tests SystemController)

## 📋 What Each Test Covers

### 1. UserInterfaceAgent Tests
- ✅ Chat message processing
- ✅ Voice command handling  
- ✅ Proactive suggestion generation
- ✅ System action explanation

### 2. AgentOrchestrator Tests
- ✅ Complex task coordination
- ✅ Agent delegation
- ✅ Result synthesis
- ✅ Task monitoring

### 3. SystemController Tests
- ✅ Command translation
- ✅ Safety validation
- ✅ System capabilities assessment
- ✅ Safe action execution

### 4. PatternValidator Tests
- ✅ Single pattern validation
- ✅ Cross-agent validation
- ✅ System coherence audit
- ✅ Validation metrics

### 5. ProactiveSuggestionEngine Tests
- ✅ Suggestion generation
- ✅ Immediate suggestions
- ✅ Feedback processing
- ✅ Suggestion metrics

### 6. Integration Tests
- ✅ UI → Orchestrator → System flow
- ✅ Pattern validation pipeline
- ✅ Multi-agent status coordination

## 🚀 Quick Start Testing

1. **Prerequisites**:
   ```bash
   # Make sure ALims system is running
   ./launch_alims.sh start
   
   # Ensure Ollama is running
   ollama serve
   ```

2. **Run comprehensive tests**:
   ```bash
   python test_all_agents.py
   ```

3. **Expected output**:
   ```
   🧪 RUNNING COMPREHENSIVE AGENT TEST SUITE
   ============================================================
   🚀 Setting up ALims Agent Testing Environment
   ✅ Ollama client ready
   ✅ Central AI Brain initialized
      - Agents available: 5
   
   🎭 TESTING USER INTERFACE AGENT
   ✅ UserInterfaceAgent: 4/4 tests passed
   
   🎭 TESTING AGENT ORCHESTRATOR  
   ✅ AgentOrchestrator: 4/4 tests passed
   
   🎛️ TESTING SYSTEM CONTROLLER
   ✅ SystemController: 4/4 tests passed
   
   🔍 TESTING PATTERN VALIDATOR
   ✅ PatternValidator: 4/4 tests passed
   
   💡 TESTING PROACTIVE SUGGESTION ENGINE
   ✅ ProactiveSuggestionEngine: 4/4 tests passed
   
   🤝 TESTING AGENT INTEGRATION
   ✅ Agent Integration: 3/3 tests passed
   
   📊 COMPREHENSIVE TEST RESULTS
   Agents Tested: 6/6
   Tests Passed: 23/23  
   Success Rate: 100.0%
   ```

## 🔍 Troubleshooting

### Common Issues

1. **"Ollama client not healthy"**
   ```bash
   # Start Ollama service
   ollama serve
   
   # Pull required model
   ollama pull gemma3:4b
   ```

2. **"Agent not available"**
   ```bash
   # Restart ALims system
   ./launch_alims.sh restart
   ```

3. **Import errors**
   ```bash
   # Activate virtual environment
   source alims_env/bin/activate
   
   # Install dependencies
   pip install -r requirements.txt
   ```

### Debugging Individual Agents

Test agents individually to isolate issues:

```bash
# Test just the UserInterfaceAgent
python test_all_agents.py --agent ui --verbose

# Test just the PatternValidator
python test_pattern_validator.py
```

## 📊 Understanding Test Results

### Success Indicators
- ✅ **Green checkmarks**: Tests passed
- 📊 **Success rate**: Percentage of tests that passed
- 🎯 **Agent count**: Should show 5 agents available

### Failure Indicators  
- ❌ **Red X marks**: Tests failed
- ⚠️ **Warnings**: Non-critical issues
- 🚨 **Errors**: Critical failures requiring attention

### Sample Successful Output
```
✅ UserInterfaceAgent: 4/4 tests passed
  ✅ Chat Message Processing: Response length: 156
  ✅ Voice Command Handling: Input type: voice
  ✅ Proactive Suggestions: Generated 3 suggestions
  ✅ System Action Explanation: Explanation length: 89
```

## 🎯 Verification Checklist

After running tests, verify:

- [ ] All 5 agents are detected and initialized
- [ ] Each agent passes its core functionality tests
- [ ] Inter-agent communication works (integration tests pass)
- [ ] No critical errors in the output
- [ ] Chat interface reports correct agent count (5, not 6)

## 📝 Creating Custom Tests

To test specific functionality:

```python
# Example: Test UserInterfaceAgent with custom message
import asyncio
from app.ai.central_brain import CentralAIBrain

async def custom_test():
    config = {
        "ai_brain": {"model_name": "gemma3:4b"},
        "context_management": {}
    }
    
    brain = CentralAIBrain(config)
    await brain.start()
    
    # Test custom interaction
    result = await brain.user_interface.process_chat_message(
        "Your custom test message here",
        {"user_id": "test_user"}
    )
    
    print(f"Response: {result}")
    await brain.stop()

# Run the test
asyncio.run(custom_test())
```

## 🔧 Advanced Testing

### Performance Testing
```bash
# Run tests with timing
time python test_all_agents.py

# Test under load (multiple concurrent tests)
for i in {1..5}; do python test_all_agents.py --agent ui & done; wait
```

### Memory Usage Testing
```bash
# Monitor memory during tests
python -m memory_profiler test_all_agents.py
```

### Integration with ALims System
```bash
# Test while ALims is running
./launch_alims.sh start
python test_all_agents.py
./launch_alims.sh stop
```

This comprehensive testing approach ensures all 5 AI agents are working correctly and helps identify any issues with their functionality or integration. 