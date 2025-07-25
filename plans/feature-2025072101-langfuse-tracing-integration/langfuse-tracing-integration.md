# Langfuse Tracing Integration for ALIMS

## Overview
Implement comprehensive Langfuse tracing for all ALIMS operations including:
- LangGraph workflow executions
- API calls (internal and external)
- Ollama LLM interactions
- Agent conversations and state changes
- System events and errors

## Requirements
1. **Trace all LLM interactions** - Ollama calls, agent responses
2. **Trace LangGraph workflows** - state transitions, node executions
3. **Trace API operations** - requests, responses, errors
4. **Trace agent activities** - conversations, decisions, state changes
5. **Performance monitoring** - latency, token usage, errors
6. **Privacy compliance** - configurable data filtering

## Architecture
- **Langfuse Client** - singleton pattern for app-wide tracing
- **Decorators** - automatic tracing of functions
- **Context propagation** - trace correlation across async operations
- **Batch processing** - efficient data transmission to Langfuse
- **Error handling** - graceful degradation when tracing fails

## Integration Points
1. `ollama_integration.py` - LLM call tracing
2. `main_interface_agent.py` - conversation tracing
3. LangGraph workflows - state transition tracing
4. API gateways - request/response tracing
5. Background tasks - async operation tracing

## Success Criteria
- All LLM calls visible in Langfuse dashboard
- Complete conversation flows traceable
- Performance metrics available
- Zero impact on core functionality
- Configurable tracing levels
