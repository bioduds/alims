#!/usr/bin/env python3
"""
Main Interface Agent Debug Integration
Integrates the advanced debugging system into the Main Interface Agent
"""

import asyncio
import json
from datetime import datetime
from typing import Any, Dict, List, Optional

from .debug_system import get_debug_tracer, trace_agent_call, DebugLevel

class MainInterfaceAgentDebugMixin:
    """Mixin to add debugging capabilities to Main Interface Agent"""
    
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.debug_tracer = get_debug_tracer()
        self.agent_id = getattr(self, 'agent_id', 'main_interface_001')
        
        # Initialize debugging
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="INIT",
            message="Main Interface Agent initialized with debugging",
            data={
                "class": self.__class__.__name__,
                "capabilities": getattr(self, 'capabilities', [])
            },
            level=DebugLevel.INFO
        )

    @trace_agent_call("MainInterfaceAgent")
    async def debug_process_message(self, conversation_id: str, message: str, user_id: str = None, **kwargs):
        """Process message with full debugging"""
        
        # Update agent state
        self.debug_tracer.update_agent_state(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            state_update={
                "current_conversation": conversation_id,
                "processing_message": True,
                "last_message_time": datetime.now().isoformat()
            },
            conversation_id=conversation_id
        )
        
        # Trace message reception
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="RECEIVE_MESSAGE",
            message=f"Processing user message: {message[:100]}...",
            data={
                "message": message,
                "user_id": user_id,
                "conversation_id": conversation_id,
                "message_length": len(message)
            },
            level=DebugLevel.INFO,
            conversation_id=conversation_id
        )
        
        try:
            # Call the original process method
            result = await self._original_process_message(conversation_id, message, user_id, **kwargs)
            
            # Trace successful processing
            self.debug_tracer.trace_agent_event(
                agent_id=self.agent_id,
                agent_type="MainInterfaceAgent",
                event_type="PROCESS_SUCCESS",
                message=f"Successfully processed message, generated {len(result.get('messages', []))} responses",
                data={
                    "result_type": type(result).__name__,
                    "response_count": len(result.get('messages', [])),
                    "success": result.get('success', False)
                },
                level=DebugLevel.INFO,
                conversation_id=conversation_id
            )
            
            return result
            
        except Exception as e:
            # Trace processing error
            self.debug_tracer.trace_agent_event(
                agent_id=self.agent_id,
                agent_type="MainInterfaceAgent",
                event_type="PROCESS_ERROR",
                message=f"Error processing message: {str(e)}",
                data={
                    "error": str(e),
                    "error_type": type(e).__name__,
                    "message": message
                },
                level=DebugLevel.ERROR,
                conversation_id=conversation_id
            )
            raise
        finally:
            # Update state
            self.debug_tracer.update_agent_state(
                agent_id=self.agent_id,
                agent_type="MainInterfaceAgent", 
                state_update={"processing_message": False},
                conversation_id=conversation_id
            )

    def debug_agent_orchestration(self, agent_responses: List[Dict], conversation_id: str):
        """Debug agent orchestration process"""
        
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="ORCHESTRATION_START",
            message=f"Orchestrating {len(agent_responses)} agent responses",
            data={
                "agent_count": len(agent_responses),
                "agents": [resp.get('agent_id', 'unknown') for resp in agent_responses]
            },
            level=DebugLevel.DEBUG,
            conversation_id=conversation_id
        )
        
        # Trace each agent response
        for i, response in enumerate(agent_responses):
            self.debug_tracer.trace_agent_event(
                agent_id=self.agent_id,
                agent_type="MainInterfaceAgent",
                event_type="AGENT_RESPONSE_RECEIVED",
                message=f"Agent {response.get('agent_id', 'unknown')} response: {response.get('content', '')[:100]}",
                data={
                    "agent_id": response.get('agent_id'),
                    "response_index": i,
                    "content": response.get('content', ''),
                    "success": response.get('success', False),
                    "processing_time": response.get('processing_time', 0)
                },
                level=DebugLevel.DEBUG,
                conversation_id=conversation_id
            )

    def debug_memory_operation(self, operation: str, query: str, results: Any, conversation_id: str):
        """Debug memory system operations"""
        
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="MEMORY_OPERATION",
            message=f"Memory {operation}: {query[:100]}",
            data={
                "operation": operation,
                "query": query,
                "result_count": len(results) if isinstance(results, (list, tuple)) else 1,
                "result_type": type(results).__name__
            },
            level=DebugLevel.DEBUG,
            conversation_id=conversation_id
        )

    def debug_ai_generation(self, prompt: str, response: str, model: str, conversation_id: str):
        """Debug AI generation process"""
        
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="AI_GENERATION",
            message=f"AI {model} generated response ({len(response)} chars)",
            data={
                "model": model,
                "prompt_length": len(prompt),
                "response_length": len(response),
                "prompt_preview": prompt[:200],
                "response_preview": response[:200]
            },
            level=DebugLevel.DEBUG,
            conversation_id=conversation_id
        )

    def debug_tla_verification(self, operation: str, state: Dict, result: bool, conversation_id: str):
        """Debug TLA+ verification steps"""
        
        self.debug_tracer.trace_agent_event(
            agent_id=self.agent_id,
            agent_type="MainInterfaceAgent",
            event_type="TLA_VERIFICATION",
            message=f"TLA+ {operation}: {'PASSED' if result else 'FAILED'}",
            data={
                "operation": operation,
                "verification_passed": result,
                "state_snapshot": state
            },
            level=DebugLevel.INFO if result else DebugLevel.ERROR,
            conversation_id=conversation_id
        )

    def get_debug_conversation_summary(self, conversation_id: str) -> Dict[str, Any]:
        """Get debugging summary for a conversation"""
        
        trace_data = self.debug_tracer.get_conversation_trace(conversation_id)
        
        # Analyze trace data
        event_types = {}
        error_count = 0
        agent_interactions = set()
        
        for event in trace_data:
            event_type = event['event_type']
            event_types[event_type] = event_types.get(event_type, 0) + 1
            
            if event['level'] == 'ERROR':
                error_count += 1
            
            if 'agent_id' in event.get('data', {}):
                agent_interactions.add(event['data']['agent_id'])
        
        return {
            "conversation_id": conversation_id,
            "total_events": len(trace_data),
            "event_types": event_types,
            "error_count": error_count,
            "agent_interactions": list(agent_interactions),
            "duration_seconds": self._calculate_conversation_duration(trace_data),
            "trace_events": trace_data
        }

    def _calculate_conversation_duration(self, trace_data: List[Dict]) -> float:
        """Calculate conversation duration from trace data"""
        if len(trace_data) < 2:
            return 0.0
        
        start_time = datetime.fromisoformat(trace_data[0]['timestamp'])
        end_time = datetime.fromisoformat(trace_data[-1]['timestamp'])
        return (end_time - start_time).total_seconds()

# Debugging FastAPI endpoint helpers
class DebugEndpoints:
    """FastAPI endpoints for debugging"""
    
    @staticmethod
    def get_debug_status():
        """Get overall debug system status"""
        tracer = get_debug_tracer()
        
        return {
            "debug_active": True,
            "total_events": len(tracer.trace_events),
            "active_conversations": list(tracer.active_conversations.keys()),
            "tracked_agents": list(tracer.agent_states.keys()),
            "performance_summary": tracer.get_performance_summary()
        }
    
    @staticmethod
    def get_conversation_debug(conversation_id: str):
        """Get debug data for specific conversation"""
        tracer = get_debug_tracer()
        return tracer.export_trace_data(conversation_id=conversation_id)
    
    @staticmethod
    def get_agent_state(agent_id: str):
        """Get current agent state"""
        tracer = get_debug_tracer()
        return tracer.get_agent_state(agent_id)

if __name__ == "__main__":
    print("🔍 Main Interface Agent Debug Integration loaded!")
