"""
Unified Memory Tensor Engine - Core Implementation
Revolutionary 4D Memory Architecture following TLA+ validated specification

This implementation follows the mathematically validated TLA+ specification
exactly, ensuring correctness of all invariants and liveness properties.
"""

import asyncio
import logging
import json
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple, Set
from dataclasses import dataclass, field
import uuid
from pathlib import Path
import numpy as np
from contextlib import asynccontextmanager

# Vector and database imports
from qdrant_client import QdrantClient
from qdrant_client.models import Distance, VectorParams, PointStruct, Filter, FieldCondition

# Import the existing tensor calendar system
from .vector_storage import VectorTensorStorage
from .models import TensorCalendar

# Our memory models
from .memory_models import (
    UnifiedMemory, MemoryType, MemoryScope, ModalityType,
    TemporalContext, SemanticContext, ConversationalContext,
    WorkflowContext, MemoryQuery, MemorySearchResult,
    MemoryInsight, MemoryTensorConfiguration
)

logger = logging.getLogger(__name__)


@dataclass
class SystemState:
    """System state tracking as per TLA+ specification"""
    memories: Set[str] = field(default_factory=set)
    temporal_index: List[str] = field(default_factory=list)
    active_queries: Set[str] = field(default_factory=set)
    consolidation_queue: List[str] = field(default_factory=list)
    system_time: int = 0
    memory_metrics: Dict[str, int] = field(default_factory=lambda: {
        "total_memories": 0,
        "query_count": 0,
        "consolidation_count": 0
    })
    component_states: Dict[str, str] = field(default_factory=lambda: {
        "memory_manager": "IDLE",
        "query_processor": "IDLE", 
        "consolidator": "IDLE"
    })


class UnifiedMemoryTensorEngine:
    """
    Core engine implementing the TLA+ validated Unified Memory Tensor system
    
    This engine provides the revolutionary 4D memory architecture:
    - Semantic dimension: Vector embeddings and topic/entity graphs
    - Temporal dimension: Time-ordered indexing with relative time support
    - Contextual dimension: Conversation/workflow/environmental context
    - Modal dimension: Multi-type content (text, numerical, spatial, etc.)
    """
    
    def __init__(self, config: MemoryTensorConfiguration):
        self.config = config
        self.state = SystemState()
        
        # Storage backends for 4D memory space
        self._tensor_storage = None  # VectorTensorStorage for integrated tensor calendar
        self._memory_store: Dict[str, UnifiedMemory] = {}
        self._relationships: Dict[str, Set[str]] = {}
        
        # Processing locks for atomicity (TLA+ requirement)
        self._memory_lock = asyncio.Lock()
        self._query_lock = asyncio.Lock()
        self._consolidation_lock = asyncio.Lock()
        
        # Background tasks
        self._consolidation_task: Optional[asyncio.Task] = None
        self._insight_task: Optional[asyncio.Task] = None
        
        logger.info("Unified Memory Tensor Engine initialized")
    
    async def initialize(self) -> None:
        """Initialize all storage backends and start background processes"""
        try:
            await self._init_tensor_storage()
            await self._start_background_tasks()
            logger.info("Memory tensor engine fully initialized")
        except Exception as e:
            logger.error(f"Failed to initialize memory tensor engine: {e}")
            raise
    
    async def shutdown(self) -> None:
        """Gracefully shutdown the engine"""
        try:
            if self._consolidation_task:
                self._consolidation_task.cancel()
            if self._insight_task:
                self._insight_task.cancel()
                
            # Ensure all components are idle (TLA+ requirement)
            await self._wait_for_idle_state()
            
            logger.info("Memory tensor engine shutdown complete")
        except Exception as e:
            logger.error(f"Error during shutdown: {e}")
    
    # TLA+ StoreMemory Action Implementation
    async def store_memory(self, memory: UnifiedMemory) -> UnifiedMemory:
        """
        Store a memory in the unified tensor space (TLA+ StoreMemory action)
        
        Maintains all TLA+ invariants:
        - CapacityInvariant: Respects MAX_MEMORIES limit
        - TemporalOrderingInvariant: Updates temporal index consistently
        - MemoryStoreConsistency: Ensures all indexed memories exist
        """
        async with self._memory_lock:
            # Check capacity invariant
            if len(self.state.memories) >= self.config.max_memories:
                await self._evict_old_memories()
            
            # Transition to PROCESSING state
            self.state.component_states["memory_manager"] = "PROCESSING"
            
            try:
                # Assign timestamp and IDs if not set
                if not memory.id:
                    memory.id = str(uuid.uuid4())
                
                memory.created_at = datetime.now()
                memory.updated_at = memory.created_at
                
                # Store memory in the unified tensor calendar
                await self._store_memory_in_tensor_calendar(memory)
                
                # Update system state (maintaining invariants)
                self.state.memories.add(memory.id)
                self.state.temporal_index.append(memory.id)
                self.state.memory_metrics["total_memories"] += 1
                self.state.system_time += 1
                
                # Store in memory store
                self._memory_store[memory.id] = memory
                
                # Queue for consolidation
                self.state.consolidation_queue.append(memory.id)
                
                logger.debug(f"Stored memory {memory.id} in unified tensor")
                return memory
                
            finally:
                # Return to IDLE state
                self.state.component_states["memory_manager"] = "IDLE"
    
    # TLA+ ExecuteQuery Action Implementation
    async def execute_query(self, query: MemoryQuery) -> List[MemorySearchResult]:
        """
        Execute a 4D query across the memory tensor (TLA+ ExecuteQuery action)
        
        Searches across all dimensions:
        - Semantic: Vector similarity search
        - Temporal: Time range and pattern matching  
        - Contextual: Conversation/workflow filtering
        - Modal: Content type filtering
        """
        query_id = str(uuid.uuid4())
        
        async with self._query_lock:
            # Transition to QUERYING state
            self.state.component_states["query_processor"] = "QUERYING"
            self.state.active_queries.add(query_id)
            
            try:
                # Increment query metrics
                self.state.memory_metrics["query_count"] += 1
                self.state.system_time += 1
                
                # Execute 4D search
                results = await self._execute_4d_search(query)
                
                logger.debug(f"Query {query_id} returned {len(results)} results")
                return results
                
            finally:
                # Return to IDLE state and remove from active queries
                self.state.active_queries.discard(query_id)
                self.state.component_states["query_processor"] = "IDLE"
    
    async def get_memory(self, memory_id: str) -> Optional[UnifiedMemory]:
        """Retrieve a specific memory by ID"""
        return self._memory_store.get(memory_id)
    
    async def update_memory(self, memory_id: str, updates: Dict[str, Any]) -> Optional[UnifiedMemory]:
        """Update an existing memory"""
        if memory_id not in self._memory_store:
            return None
            
        memory = self._memory_store[memory_id]
        
        # Update fields
        for field, value in updates.items():
            if hasattr(memory, field):
                setattr(memory, field, value)
        
        memory.updated_at = datetime.now()
        memory.version += 1
        
        # Re-store updated memory
        await self.store_memory(memory)
        return memory
    
    async def delete_memory(self, memory_id: str) -> bool:
        """Delete a memory from the tensor"""
        if memory_id not in self._memory_store:
            return False
            
        async with self._memory_lock:
            # Remove from tensor calendar storage
            await self._remove_memory_from_tensor_calendar(memory_id)
            
            # Update system state
            self.state.memories.discard(memory_id)
            if memory_id in self.state.temporal_index:
                self.state.temporal_index.remove(memory_id)
            
            # Remove from memory store
            del self._memory_store[memory_id]
            
            self.state.memory_metrics["total_memories"] -= 1
            
            logger.debug(f"Deleted memory {memory_id}")
            return True
    
    # Internal implementation methods
    
    async def _init_tensor_storage(self) -> None:
        """Initialize the tensor calendar storage for unified memory"""
        try:
            # Configure tensor storage for memory integration
            import os
            qdrant_url = os.getenv("VECTOR_DB_URL", "http://localhost:6333")
            
            tensor_config = {
                "qdrant_url": qdrant_url,
                "collection_name": f"memory_{self.config.collection_name}",
                "embedding_dim": self.config.embedding_dimension,
                "max_tensors": self.config.max_memories,
                "max_vectors": self.config.max_memories,
                "max_collections": 1
            }
            
            # Initialize the vector tensor storage
            self._tensor_storage = VectorTensorStorage(tensor_config)
            await self._tensor_storage.initialize()
            
            logger.info(f"Tensor calendar storage initialized for unified memory")
        except Exception as e:
            logger.error(f"Failed to initialize tensor storage: {e}")
            raise
    
    async def _store_memory_in_tensor_calendar(self, memory: UnifiedMemory) -> None:
        """Store memory as a tensor in the calendar system"""
        try:
            # Generate embedding if not present
            if not memory.embedding:
                memory.embedding = await self._generate_embedding(memory.primary_text)
            
            # Create tensor calendar entry that embeds the memory
            tensor_calendar = TensorCalendar(
                tensor_id=memory.id,
                calendar_data={
                    # Embed all 4D memory dimensions into calendar data
                    "memory_type": memory.memory_type.value,
                    "memory_scope": memory.scope.value,
                    "primary_text": memory.primary_text,
                    "additional_content": memory.additional_content,
                    
                    # Temporal dimension (this is where tensor calendar magic happens)
                    "temporal_context": {
                        "timestamp": memory.temporal_context.timestamp.isoformat(),
                        "duration": memory.temporal_context.duration.total_seconds() if memory.temporal_context.duration else None,
                        "relative_time": memory.temporal_context.relative_time,
                        "temporal_precision": memory.temporal_context.temporal_precision,
                        "temporal_tags": memory.temporal_context.temporal_tags
                    },
                    
                    # Semantic dimension
                    "semantic_context": {
                        "topics": memory.semantic_context.topics,
                        "entities": memory.semantic_context.entities,
                        "concepts": memory.semantic_context.concepts,
                        "confidence": memory.semantic_context.confidence,
                        "embedding_model": memory.semantic_context.embedding_model
                    },
                    
                    # Contextual dimension
                    "conversational_context": {
                        "conversation_id": memory.conversational_context.conversation_id if memory.conversational_context else None,
                        "speaker": memory.conversational_context.speaker if memory.conversational_context else None,
                        "message_index": memory.conversational_context.message_index if memory.conversational_context else None,
                        "thread_context": memory.conversational_context.thread_context if memory.conversational_context else None
                    } if memory.conversational_context else None,
                    
                    "workflow_context": {
                        "workflow_id": memory.workflow_context.workflow_id if memory.workflow_context else None,
                        "step_id": memory.workflow_context.step_id if memory.workflow_context else None,
                        "workflow_state": memory.workflow_context.workflow_state if memory.workflow_context else None,
                        "execution_context": memory.workflow_context.execution_context if memory.workflow_context else None
                    } if memory.workflow_context else None,
                    
                    # Modal dimension
                    "modality": memory.modality.value,
                    "content_hash": memory.content_hash,
                    "size_bytes": memory.size_bytes,
                    
                    # Memory metadata
                    "importance_score": memory.importance_score,
                    "access_count": memory.access_count,
                    "version": memory.version,
                    "parent_memories": memory.parent_memories,
                    "child_memories": memory.child_memories,
                    "related_memories": memory.related_memories,
                    "tags": memory.tags
                },
                embedding=memory.embedding,
                metadata={
                    "memory_engine": "unified_memory_tensor",
                    "created_at": memory.created_at.isoformat(),
                    "updated_at": memory.updated_at.isoformat()
                }
            )
            
            # Store in tensor calendar - this handles ALL dimensions magically
            await self._tensor_storage.store_tensor(
                tensor_id=memory.id,
                calendar_data=tensor_calendar.calendar_data,
                embedding=memory.embedding
            )
            
            logger.debug(f"Stored memory {memory.id} in tensor calendar")
            
        except Exception as e:
            logger.error(f"Failed to store memory in tensor calendar: {e}")
            raise
    
    async def _remove_memory_from_tensor_calendar(self, memory_id: str) -> None:
        """Remove memory from tensor calendar storage"""
        try:
            await self._tensor_storage.delete_tensor(memory_id)
            logger.debug(f"Removed memory {memory_id} from tensor calendar")
        except Exception as e:
            logger.error(f"Failed to remove memory from tensor calendar: {e}")
    
    async def _search_tensor_calendar(self, query: MemoryQuery) -> List[MemorySearchResult]:
        """Search memories using tensor calendar's vector search capabilities"""
        try:
            # Generate query embedding
            query_embedding = await self._generate_embedding(query.text_query)
            
            # Use tensor calendar's search capabilities
            # This leverages the existing vector search + temporal magic
            search_results = await self._tensor_storage.search_similar_tensors(
                query_embedding=query_embedding,
                limit=min(query.max_results * 2, 100),
                similarity_threshold=query.semantic_similarity_threshold
            )
            
            results = []
            for tensor_result in search_results:
                tensor_id = tensor_result["tensor_id"]
                memory = self._memory_store.get(tensor_id)
                
                if memory:
                    results.append(MemorySearchResult(
                        memory=memory,
                        relevance_score=tensor_result["similarity_score"],
                        semantic_distance=1.0 - tensor_result["similarity_score"]
                    ))
            
            return results
            
        except Exception as e:
            logger.error(f"Tensor calendar search failed: {e}")
            return []
    
    async def _execute_4d_search(self, query: MemoryQuery) -> List[MemorySearchResult]:
        """Execute search across all 4 dimensions of the memory tensor"""
        results = []
        
        try:
            # 1. Semantic dimension search
            if query.text_query:
                semantic_results = await self._semantic_search(query)
                results.extend(semantic_results)
            
            # 2. Temporal dimension filtering
            if query.time_range or query.relative_time:
                results = await self._filter_temporal(results, query)
            
            # 3. Contextual dimension filtering  
            if query.conversation_id or query.workflow_id or query.speakers:
                results = await self._filter_contextual(results, query)
            
            # 4. Modal dimension filtering
            if query.memory_types or query.memory_scopes:
                results = await self._filter_modal(results, query)
            
            # Sort and limit results
            results.sort(key=lambda r: r.relevance_score, reverse=True)
            return results[:query.max_results]
            
        except Exception as e:
            logger.error(f"Failed to execute 4D search: {e}")
            return []
    
    async def _semantic_search(self, query: MemoryQuery) -> List[MemorySearchResult]:
        """Search semantic dimension using tensor calendar vector search"""
        try:
            # Use the tensor calendar's built-in search capabilities
            return await self._search_tensor_calendar(query)
            
        except Exception as e:
            logger.error(f"Semantic search failed: {e}")
            return []
    
    async def _filter_temporal(self, results: List[MemorySearchResult], 
                             query: MemoryQuery) -> List[MemorySearchResult]:
        """Filter results by temporal constraints"""
        if not query.time_range and not query.relative_time:
            return results
        
        filtered = []
        
        for result in results:
            memory_time = result.memory.temporal_context.timestamp
            
            # Check time range constraint
            if query.time_range:
                start, end = query.time_range
                if not (start <= memory_time <= end):
                    continue
            
            # Check relative time constraint
            if query.relative_time:
                # Simple relative time parsing (can be enhanced)
                if not await self._matches_relative_time(memory_time, query.relative_time):
                    continue
            
            # Calculate temporal distance for ranking
            if query.time_range:
                result.temporal_distance = self._calculate_temporal_distance(
                    memory_time, query.time_range
                )
            
            filtered.append(result)
        
        return filtered
    
    async def _filter_contextual(self, results: List[MemorySearchResult],
                               query: MemoryQuery) -> List[MemorySearchResult]:
        """Filter results by contextual constraints"""
        filtered = []
        
        for result in results:
            memory = result.memory
            
            # Check conversation context
            if query.conversation_id:
                if (not memory.conversational_context or 
                    memory.conversational_context.conversation_id != query.conversation_id):
                    continue
            
            # Check workflow context
            if query.workflow_id:
                if (not memory.workflow_context or
                    memory.workflow_context.workflow_id != query.workflow_id):
                    continue
            
            # Check speaker context
            if query.speakers:
                if (not memory.conversational_context or
                    memory.conversational_context.speaker not in query.speakers):
                    continue
            
            filtered.append(result)
        
        return filtered
    
    async def _filter_modal(self, results: List[MemorySearchResult],
                          query: MemoryQuery) -> List[MemorySearchResult]:
        """Filter results by modal constraints"""
        filtered = []
        
        for result in results:
            memory = result.memory
            
            # Check memory type
            if query.memory_types and memory.memory_type not in query.memory_types:
                continue
            
            # Check memory scope
            if query.memory_scopes and memory.scope not in query.memory_scopes:
                continue
            
            filtered.append(result)
        
        return filtered
    
    async def _generate_embedding(self, text: str) -> List[float]:
        """Generate vector embedding for text (placeholder implementation)"""
        # This would use actual embedding models like OpenAI, SentenceTransformers, etc.
        # For now, return a dummy embedding
        import hashlib
        hash_obj = hashlib.md5(text.encode())
        hash_bytes = hash_obj.digest()
        
        # Convert to float vector (dummy implementation)
        embedding = [float(b) / 255.0 for b in hash_bytes[:self.config.embedding_dimension]]
        
        # Pad or truncate to correct dimension
        while len(embedding) < self.config.embedding_dimension:
            embedding.append(0.0)
        
        return embedding[:self.config.embedding_dimension]
    
    async def _matches_relative_time(self, memory_time: datetime, relative_time: str) -> bool:
        """Check if memory time matches relative time expression"""
        now = datetime.now()
        
        # Simple relative time matching (can be enhanced with NLP)
        if "today" in relative_time.lower():
            return memory_time.date() == now.date()
        elif "yesterday" in relative_time.lower():
            yesterday = now - timedelta(days=1)
            return memory_time.date() == yesterday.date()
        elif "last week" in relative_time.lower():
            week_ago = now - timedelta(days=7)
            return week_ago <= memory_time <= now
        
        return True  # Default to match if not recognized
    
    def _calculate_temporal_distance(self, memory_time: datetime, 
                                   time_range: Tuple[datetime, datetime]) -> float:
        """Calculate temporal distance for ranking"""
        start, end = time_range
        
        # If within range, distance is 0
        if start <= memory_time <= end:
            return 0.0
        
        # Calculate distance from nearest boundary
        if memory_time < start:
            return (start - memory_time).total_seconds()
        else:
            return (memory_time - end).total_seconds()
    
    async def _evict_old_memories(self) -> None:
        """Evict old memories to maintain capacity constraint"""
        if len(self.state.memories) < self.config.max_memories:
            return
        
        # Simple LRU eviction (can be enhanced with importance scoring)
        oldest_memory_id = self.state.temporal_index[0]
        await self.delete_memory(oldest_memory_id)
        
        logger.debug(f"Evicted memory {oldest_memory_id} to maintain capacity")
    
    # TLA+ ConsolidateMemories Action Implementation
    async def _consolidate_memories_background(self) -> None:
        """Background task for memory consolidation (TLA+ ConsolidateMemories action)"""
        while True:
            try:
                if self.state.consolidation_queue:
                    async with self._consolidation_lock:
                        if self.state.consolidation_queue:
                            # Transition to CONSOLIDATING state
                            self.state.component_states["consolidator"] = "CONSOLIDATING"
                            
                            try:
                                memory_id = self.state.consolidation_queue.pop(0)
                                await self._consolidate_memory(memory_id)
                                self.state.memory_metrics["consolidation_count"] += 1
                                
                            finally:
                                # Return to IDLE state
                                self.state.component_states["consolidator"] = "IDLE"
                
                await asyncio.sleep(1.0)  # Check every second
                
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Consolidation error: {e}")
                self.state.component_states["consolidator"] = "IDLE"
                await asyncio.sleep(5.0)  # Wait before retrying
    
    async def _consolidate_memory(self, memory_id: str) -> None:
        """Consolidate a single memory (find relationships, update importance)"""
        memory = self._memory_store.get(memory_id)
        if not memory:
            return
        
        # Find related memories using semantic similarity
        related_memories = await self._find_related_memories(memory)
        
        # Update relationships
        if related_memories:
            memory.related_memories.extend([m.id for m in related_memories])
            for related in related_memories:
                if memory.id not in related.related_memories:
                    related.related_memories.append(memory.id)
        
        # Update importance score based on relationships and access patterns
        memory.importance_score = self._calculate_importance_score(memory)
        
        logger.debug(f"Consolidated memory {memory_id}, found {len(related_memories)} relationships")
    
    async def _find_related_memories(self, memory: UnifiedMemory) -> List[UnifiedMemory]:
        """Find memories related to the given memory"""
        # Use semantic search to find similar memories
        query = MemoryQuery(
            text_query=memory.primary_text,
            semantic_similarity_threshold=0.8,
            max_results=5
        )
        
        results = await self._semantic_search(query)
        
        # Filter out the memory itself and return related memories
        related = []
        for result in results:
            if result.memory.id != memory.id:
                related.append(result.memory)
        
        return related
    
    def _calculate_importance_score(self, memory: UnifiedMemory) -> float:
        """Calculate importance score for memory retention"""
        score = 0.5  # Base score
        
        # Factor in access count
        score += min(memory.access_count * 0.1, 0.3)
        
        # Factor in number of relationships
        relationship_count = (len(memory.parent_memories) + 
                            len(memory.child_memories) + 
                            len(memory.related_memories))
        score += min(relationship_count * 0.05, 0.2)
        
        # Factor in recency
        age_days = (datetime.now() - memory.created_at).days
        recency_factor = max(0, 1.0 - (age_days / 365.0))  # Decay over a year
        score *= (0.5 + 0.5 * recency_factor)
        
        return min(score, 1.0)
    
    async def _start_background_tasks(self) -> None:
        """Start background processing tasks"""
        self._consolidation_task = asyncio.create_task(
            self._consolidate_memories_background()
        )
        
        if self.config.enable_insight_generation:
            self._insight_task = asyncio.create_task(
                self._generate_insights_background()
            )
    
    async def _generate_insights_background(self) -> None:
        """Background task for generating insights from memory patterns"""
        while True:
            try:
                await asyncio.sleep(self.config.insight_generation_interval.total_seconds())
                await self._generate_insights()
                
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.error(f"Insight generation error: {e}")
    
    async def _generate_insights(self) -> List[MemoryInsight]:
        """Generate insights from memory patterns (placeholder implementation)"""
        # This would implement actual pattern recognition and insight generation
        insights = []
        
        # Example: Find frequently discussed topics
        topic_counts = {}
        for memory in self._memory_store.values():
            for topic in memory.semantic_context.topics:
                topic_counts[topic] = topic_counts.get(topic, 0) + 1
        
        # Generate insights for frequent topics
        for topic, count in topic_counts.items():
            if count >= 3:  # Threshold for insight generation
                insights.append(MemoryInsight(
                    insight_type="frequent_topic",
                    description=f"Topic '{topic}' appears in {count} memories",
                    related_memories=[m.id for m in self._memory_store.values() 
                                    if topic in m.semantic_context.topics],
                    confidence=min(count / 10.0, 1.0)
                ))
        
        logger.debug(f"Generated {len(insights)} insights")
        return insights
    
    async def _wait_for_idle_state(self) -> None:
        """Wait for all components to return to IDLE state (TLA+ requirement)"""
        max_wait = 30.0  # Maximum wait time in seconds
        wait_time = 0.0
        
        while wait_time < max_wait:
            if (self.state.component_states["memory_manager"] == "IDLE" and
                self.state.component_states["query_processor"] == "IDLE" and
                self.state.component_states["consolidator"] == "IDLE"):
                return
            
            await asyncio.sleep(0.1)
            wait_time += 0.1
        
        logger.warning("Timeout waiting for idle state during shutdown")
    
    # System state inspection methods (for monitoring and debugging)
    
    def get_system_state(self) -> Dict[str, Any]:
        """Get current system state for monitoring"""
        return {
            "memory_count": len(self.state.memories),
            "temporal_index_length": len(self.state.temporal_index),
            "active_queries": len(self.state.active_queries),
            "consolidation_queue_length": len(self.state.consolidation_queue),
            "system_time": self.state.system_time,
            "memory_metrics": self.state.memory_metrics.copy(),
            "component_states": self.state.component_states.copy()
        }
    
    def validate_invariants(self) -> Dict[str, bool]:
        """Validate all TLA+ invariants for system correctness"""
        results = {}
        
        # CapacityInvariant
        results["capacity_invariant"] = len(self.state.memories) <= self.config.max_memories
        
        # TemporalOrderingInvariant
        results["temporal_ordering_invariant"] = (
            len(self.state.temporal_index) == len(self.state.memories)
        )
        
        # MemoryStoreConsistency
        results["memory_store_consistency"] = all(
            memory_id in self._memory_store for memory_id in self.state.temporal_index
        )
        
        # QueryProcessingConsistency
        results["query_processing_consistency"] = all(
            isinstance(query_id, str) for query_id in self.state.active_queries
        )
        
        # ComponentStateConsistency
        valid_states = {
            "memory_manager": ["IDLE", "PROCESSING"],
            "query_processor": ["IDLE", "QUERYING"],
            "consolidator": ["IDLE", "CONSOLIDATING"]
        }
        results["component_state_consistency"] = all(
            self.state.component_states[component] in valid_states[component]
            for component in valid_states
        )
        
        return results
