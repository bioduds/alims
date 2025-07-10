"""
Unified Memory Tensor System - High-Level Interface
Revolutionary 4D Memory Architecture Integration Layer

This module provides the high-level interface for integrating the Unified Memory
Tensor system with agents, tensor calendar, and other ALIMS components.
"""

import asyncio
import logging
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Union, AsyncContextManager
from contextlib import asynccontextmanager
import uuid

from backend.app.tensor_calendar.memory_models import (
    UnifiedMemory, MemoryType, MemoryScope, ModalityType,
    TemporalContext, SemanticContext, ConversationalContext,
    WorkflowContext, MemoryQuery, MemorySearchResult,
    MemoryTensorConfiguration
)
from backend.app.tensor_calendar.unified_memory_tensor import UnifiedMemoryTensorEngine

logger = logging.getLogger(__name__)


class MemoryTensorSystem:
    """
    High-level interface for the Unified Memory Tensor system
    
    This class provides a simple, intuitive API for agents and other components
    to interact with the revolutionary 4D memory architecture.
    """
    
    def __init__(self, config: Optional[MemoryTensorConfiguration] = None):
        self.config = config or MemoryTensorConfiguration()
        self.engine: Optional[UnifiedMemoryTensorEngine] = None
        self._initialized = False
        
    async def initialize(self) -> None:
        """Initialize the memory tensor system"""
        if self._initialized:
            return
            
        self.engine = UnifiedMemoryTensorEngine(self.config)
        await self.engine.initialize()
        self._initialized = True
        
        logger.info("Memory Tensor System initialized successfully")
    
    async def shutdown(self) -> None:
        """Shutdown the memory tensor system"""
        if self.engine:
            await self.engine.shutdown()
        self._initialized = False
        
        logger.info("Memory Tensor System shutdown complete")
    
    # Conversation Memory Interface
    
    async def remember_conversation(
        self,
        speaker: str,
        message: str,
        conversation_id: str,
        turn_number: int,
        response_to: Optional[str] = None,
        sentiment: Optional[str] = None,
        intent: Optional[str] = None,
        topics: Optional[List[str]] = None,
        entities: Optional[List[str]] = None
    ) -> UnifiedMemory:
        """
        Remember a conversation turn in the unified memory tensor
        
        This creates a conversation memory that's immediately searchable across
        all dimensions: semantic, temporal, contextual, and modal.
        """
        if not self._initialized:
            await self.initialize()
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.CONVERSATION,
            scope=MemoryScope.SESSION,
            primary_text=message,
            temporal_context=TemporalContext(
                timestamp=datetime.now(),
                timezone="UTC"
            ),
            semantic_context=SemanticContext(
                topics=topics or [],
                entities=entities or [],
                confidence=0.9
            ),
            conversational_context=ConversationalContext(
                speaker=speaker,
                conversation_id=conversation_id,
                turn_number=turn_number,
                response_to=response_to,
                sentiment=sentiment,
                intent=intent
            )
        )
        
        return await self.engine.store_memory(memory)
    
    async def remember_fact(
        self,
        fact: str,
        topics: Optional[List[str]] = None,
        entities: Optional[List[str]] = None,
        confidence: float = 1.0,
        source: str = "system",
        scope: MemoryScope = MemoryScope.PERSISTENT
    ) -> UnifiedMemory:
        """
        Remember a fact in the unified memory tensor
        
        Facts become part of the agent's permanent knowledge base,
        searchable by content, topics, entities, and time learned.
        """
        if not self._initialized:
            await self.initialize()
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.FACT,
            scope=scope,
            primary_text=fact,
            temporal_context=TemporalContext(
                timestamp=datetime.now(),
                timezone="UTC"
            ),
            semantic_context=SemanticContext(
                topics=topics or [],
                entities=entities or [],
                confidence=confidence
            ),
            source=source,
            confidence=confidence
        )
        
        return await self.engine.store_memory(memory)
    
    async def remember_decision(
        self,
        decision: str,
        reasoning: str,
        outcome: Optional[str] = None,
        confidence: float = 1.0,
        workflow_id: Optional[str] = None,
        related_memories: Optional[List[str]] = None
    ) -> UnifiedMemory:
        """
        Remember a decision made by the agent
        
        Decisions become part of the agent's decision history,
        enabling learning from past choices and consistency.
        """
        if not self._initialized:
            await self.initialize()
        
        decision_text = f"Decision: {decision}\nReasoning: {reasoning}"
        if outcome:
            decision_text += f"\nOutcome: {outcome}"
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.DECISION,
            scope=MemoryScope.PERSISTENT,
            primary_text=decision_text,
            temporal_context=TemporalContext(
                timestamp=datetime.now(),
                timezone="UTC"
            ),
            semantic_context=SemanticContext(
                topics=["decision-making", "reasoning"],
                confidence=confidence
            ),
            workflow_context=WorkflowContext(
                workflow_id=workflow_id or "unknown",
                step_number=1,
                operation_type="decision",
                success=True
            ) if workflow_id else None,
            related_memories=related_memories or [],
            confidence=confidence
        )
        
        return await self.engine.store_memory(memory)
    
    async def remember_event(
        self,
        event_title: str,
        event_description: str,
        start_time: datetime,
        duration: Optional[timedelta] = None,
        participants: Optional[List[str]] = None,
        location: Optional[str] = None,
        event_type: str = "meeting"
    ) -> UnifiedMemory:
        """
        Remember a calendar event in the unified memory tensor
        
        Events become searchable by time, participants, topics, and content,
        linking calendar and conversational memory seamlessly.
        """
        if not self._initialized:
            await self.initialize()
        
        event_text = f"{event_title}\n{event_description}"
        if location:
            event_text += f"\nLocation: {location}"
        if participants:
            event_text += f"\nParticipants: {', '.join(participants)}"
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.EVENT,
            scope=MemoryScope.PERSISTENT,
            primary_text=event_text,
            temporal_context=TemporalContext(
                timestamp=start_time,
                duration=duration,
                timezone="UTC",
                temporal_tags=[event_type, "calendar"]
            ),
            semantic_context=SemanticContext(
                topics=[event_type, "calendar", "event"],
                entities=participants or [],
                confidence=1.0
            ),
            metadata={
                "event_type": event_type,
                "location": location,
                "participants": participants or []
            }
        )
        
        return await self.engine.store_memory(memory)
    
    async def remember_observation(
        self,
        observation: str,
        context: str = "general",
        confidence: float = 0.8,
        sensor_data: Optional[Dict[str, Any]] = None
    ) -> UnifiedMemory:
        """
        Remember an environmental observation
        
        Observations capture the agent's awareness of its environment,
        building situational awareness over time.
        """
        if not self._initialized:
            await self.initialize()
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.OBSERVATION,
            scope=MemoryScope.CONTEXTUAL,
            primary_text=observation,
            temporal_context=TemporalContext(
                timestamp=datetime.now(),
                timezone="UTC",
                temporal_tags=["observation", context]
            ),
            semantic_context=SemanticContext(
                topics=["observation", context],
                confidence=confidence
            ),
            content={
                ModalityType.TEXT: observation,
                ModalityType.NUMERICAL: sensor_data or {}
            },
            confidence=confidence
        )
        
        return await self.engine.store_memory(memory)
    
    # Natural Language Query Interface
    
    async def recall(self, query: str, max_results: int = 10) -> List[MemorySearchResult]:
        """
        Natural language memory recall
        
        Example queries:
        - "What did John say about the project last week?"
        - "Show me all decisions made during urgent workflows"
        - "Find conversations about AI that happened after the presentation"
        """
        if not self._initialized:
            await self.initialize()
        
        memory_query = MemoryQuery(
            text_query=query,
            max_results=max_results,
            sort_by="relevance"
        )
        
        return await self.engine.execute_query(memory_query)
    
    async def recall_by_time(
        self,
        query: str,
        time_range: Optional[tuple[datetime, datetime]] = None,
        relative_time: Optional[str] = None,
        max_results: int = 10
    ) -> List[MemorySearchResult]:
        """
        Time-aware memory recall
        
        Examples:
        - recall_by_time("project updates", relative_time="last week")
        - recall_by_time("meeting notes", time_range=(start_date, end_date))
        """
        if not self._initialized:
            await self.initialize()
        
        memory_query = MemoryQuery(
            text_query=query,
            time_range=time_range,
            relative_time=relative_time,
            max_results=max_results,
            sort_by="time"
        )
        
        return await self.engine.execute_query(memory_query)
    
    async def recall_conversation(
        self,
        conversation_id: str,
        query: Optional[str] = None,
        max_results: int = 50
    ) -> List[MemorySearchResult]:
        """
        Recall memories from a specific conversation
        
        Maintains conversation context and continuity across sessions.
        """
        if not self._initialized:
            await self.initialize()
        
        memory_query = MemoryQuery(
            text_query=query,
            conversation_id=conversation_id,
            memory_types=[MemoryType.CONVERSATION],
            max_results=max_results,
            sort_by="time"
        )
        
        return await self.engine.execute_query(memory_query)
    
    async def recall_facts(
        self,
        topic: Optional[str] = None,
        entities: Optional[List[str]] = None,
        max_results: int = 20
    ) -> List[MemorySearchResult]:
        """
        Recall facts from the knowledge base
        
        Enables agents to access learned knowledge efficiently.
        """
        if not self._initialized:
            await self.initialize()
        
        memory_query = MemoryQuery(
            text_query=topic,
            entities=entities or [],
            memory_types=[MemoryType.FACT],
            memory_scopes=[MemoryScope.PERSISTENT],
            max_results=max_results,
            sort_by="relevance"
        )
        
        return await self.engine.execute_query(memory_query)
    
    async def recall_decisions(
        self,
        context: Optional[str] = None,
        workflow_id: Optional[str] = None,
        max_results: int = 10
    ) -> List[MemorySearchResult]:
        """
        Recall past decisions for consistency and learning
        
        Helps agents make consistent decisions and learn from experience.
        """
        if not self._initialized:
            await self.initialize()
        
        memory_query = MemoryQuery(
            text_query=context,
            workflow_id=workflow_id,
            memory_types=[MemoryType.DECISION],
            max_results=max_results,
            sort_by="time"
        )
        
        return await self.engine.execute_query(memory_query)
    
    # Advanced Memory Operations
    
    async def find_related_memories(
        self,
        memory_id: str,
        max_results: int = 10
    ) -> List[MemorySearchResult]:
        """
        Find memories related to a specific memory
        
        Discovers connections and relationships automatically.
        """
        if not self._initialized:
            await self.initialize()
        
        base_memory = await self.engine.get_memory(memory_id)
        if not base_memory:
            return []
        
        memory_query = MemoryQuery(
            text_query=base_memory.primary_text,
            semantic_similarity_threshold=0.8,
            max_results=max_results + 1,  # +1 to exclude the base memory
            sort_by="relevance"
        )
        
        results = await self.engine.execute_query(memory_query)
        
        # Filter out the base memory itself
        return [r for r in results if r.memory.id != memory_id]
    
    async def update_memory_importance(
        self,
        memory_id: str,
        importance_score: float
    ) -> bool:
        """
        Update the importance score of a memory
        
        Allows manual tuning of memory importance for retention.
        """
        if not self._initialized:
            await self.initialize()
        
        return await self.engine.update_memory(memory_id, {
            "importance_score": max(0.0, min(1.0, importance_score))
        }) is not None
    
    async def forget_memory(self, memory_id: str) -> bool:
        """
        Forget (delete) a specific memory
        
        Provides controlled forgetting for privacy or relevance.
        """
        if not self._initialized:
            await self.initialize()
        
        return await self.engine.delete_memory(memory_id)
    
    # System Information and Health
    
    async def get_memory_stats(self) -> Dict[str, Any]:
        """Get statistics about the memory tensor system"""
        if not self._initialized:
            await self.initialize()
        
        system_state = self.engine.get_system_state()
        invariants = self.engine.validate_invariants()
        
        return {
            "total_memories": system_state["memory_count"],
            "memory_types": await self._get_memory_type_distribution(),
            "system_health": all(invariants.values()),
            "invariants": invariants,
            "component_states": system_state["component_states"],
            "metrics": system_state["memory_metrics"],
            "recent_activity": {
                "queries_processed": system_state["memory_metrics"]["query_count"],
                "consolidations_completed": system_state["memory_metrics"]["consolidation_count"]
            }
        }
    
    async def _get_memory_type_distribution(self) -> Dict[str, int]:
        """Get distribution of memory types"""
        if not self.engine:
            return {}
        
        distribution = {}
        for memory in self.engine._memory_store.values():
            memory_type = memory.memory_type.value
            distribution[memory_type] = distribution.get(memory_type, 0) + 1
        
        return distribution
    
    # Context Managers for Convenient Usage
    
    @asynccontextmanager
    async def conversation_context(
        self,
        conversation_id: str,
        speaker: str
    ) -> AsyncContextManager["ConversationMemoryContext"]:
        """
        Context manager for conversation memory
        
        Usage:
        async with memory_system.conversation_context("conv_001", "alice") as conv:
            await conv.remember("Hello, how are you?")
            await conv.remember("I'm doing well, thanks!")
        """
        if not self._initialized:
            await self.initialize()
        
        context = ConversationMemoryContext(
            memory_system=self,
            conversation_id=conversation_id,
            speaker=speaker
        )
        
        yield context
    
    @asynccontextmanager
    async def workflow_context(
        self,
        workflow_id: str,
        workflow_type: str = "general"
    ) -> AsyncContextManager["WorkflowMemoryContext"]:
        """
        Context manager for workflow memory
        
        Usage:
        async with memory_system.workflow_context("wf_001", "data_analysis") as wf:
            await wf.remember_step("Loaded dataset", success=True)
            await wf.remember_decision("Use random forest", "Best accuracy on validation")
        """
        if not self._initialized:
            await self.initialize()
        
        context = WorkflowMemoryContext(
            memory_system=self,
            workflow_id=workflow_id,
            workflow_type=workflow_type
        )
        
        yield context


class ConversationMemoryContext:
    """Context manager for conversation-specific memory operations"""
    
    def __init__(self, memory_system: MemoryTensorSystem, conversation_id: str, speaker: str):
        self.memory_system = memory_system
        self.conversation_id = conversation_id
        self.speaker = speaker
        self.turn_number = 1
    
    async def remember(
        self,
        message: str,
        response_to: Optional[str] = None,
        sentiment: Optional[str] = None,
        intent: Optional[str] = None,
        topics: Optional[List[str]] = None,
        entities: Optional[List[str]] = None
    ) -> UnifiedMemory:
        """Remember a message in this conversation context"""
        memory = await self.memory_system.remember_conversation(
            speaker=self.speaker,
            message=message,
            conversation_id=self.conversation_id,
            turn_number=self.turn_number,
            response_to=response_to,
            sentiment=sentiment,
            intent=intent,
            topics=topics,
            entities=entities
        )
        
        self.turn_number += 1
        return memory
    
    async def recall(self, query: Optional[str] = None, max_results: int = 20) -> List[MemorySearchResult]:
        """Recall memories from this conversation"""
        return await self.memory_system.recall_conversation(
            conversation_id=self.conversation_id,
            query=query,
            max_results=max_results
        )


class WorkflowMemoryContext:
    """Context manager for workflow-specific memory operations"""
    
    def __init__(self, memory_system: MemoryTensorSystem, workflow_id: str, workflow_type: str):
        self.memory_system = memory_system
        self.workflow_id = workflow_id
        self.workflow_type = workflow_type
        self.step_number = 1
    
    async def remember_step(
        self,
        description: str,
        success: bool = True,
        error_message: Optional[str] = None,
        performance_metrics: Optional[Dict[str, float]] = None
    ) -> UnifiedMemory:
        """Remember a workflow step"""
        step_text = f"Step {self.step_number}: {description}"
        if not success and error_message:
            step_text += f"\nError: {error_message}"
        
        memory = UnifiedMemory(
            id=str(uuid.uuid4()),
            memory_type=MemoryType.WORKFLOW,
            scope=MemoryScope.SESSION,
            primary_text=step_text,
            temporal_context=TemporalContext(
                timestamp=datetime.now(),
                timezone="UTC",
                temporal_tags=[self.workflow_type, "workflow"]
            ),
            semantic_context=SemanticContext(
                topics=[self.workflow_type, "workflow", "step"],
                confidence=1.0
            ),
            workflow_context=WorkflowContext(
                workflow_id=self.workflow_id,
                step_number=self.step_number,
                operation_type=self.workflow_type,
                success=success,
                error_message=error_message,
                performance_metrics=performance_metrics or {}
            )
        )
        
        stored_memory = await self.memory_system.engine.store_memory(memory)
        self.step_number += 1
        return stored_memory
    
    async def remember_decision(
        self,
        decision: str,
        reasoning: str,
        outcome: Optional[str] = None,
        confidence: float = 1.0
    ) -> UnifiedMemory:
        """Remember a decision made during this workflow"""
        return await self.memory_system.remember_decision(
            decision=decision,
            reasoning=reasoning,
            outcome=outcome,
            confidence=confidence,
            workflow_id=self.workflow_id
        )


# Singleton instance for global access
_memory_tensor_system: Optional[MemoryTensorSystem] = None


async def get_memory_system(config: Optional[MemoryTensorConfiguration] = None) -> MemoryTensorSystem:
    """Get the global memory tensor system instance"""
    global _memory_tensor_system
    
    if _memory_tensor_system is None:
        _memory_tensor_system = MemoryTensorSystem(config)
        await _memory_tensor_system.initialize()
    
    return _memory_tensor_system


async def shutdown_memory_system() -> None:
    """Shutdown the global memory tensor system"""
    global _memory_tensor_system
    
    if _memory_tensor_system:
        await _memory_tensor_system.shutdown()
        _memory_tensor_system = None
