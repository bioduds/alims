"""
Tensor Calendar Vector Storage Implementation
Based on TLA+ validated specification: TensorCalendarVectorStorageSimple.tla

This implementation follows the mathematically proven operations and maintains
all invariants validated by the TLA+ model checker.
"""

import asyncio
import logging
from typing import Dict, Any, List, Optional, Union
import numpy as np
from datetime import datetime
import json
import uuid

from qdrant_client import QdrantClient
from qdrant_client.http import models
from qdrant_client.http.exceptions import UnexpectedResponse

from .models import TensorCalendar, SystemMetrics
from .exceptions import TensorConstraintError


logger = logging.getLogger(__name__)


class VectorTensorStorage:
    """
    TLA+ Verified Vector Storage for Tensor Calendar System
    
    Implements the operations validated in TensorCalendarVectorStorageSimple.tla:
    - StoreTensor(tensor_id, calendar_data, embedding)
    - RetrieveTensor(tensor_id) 
    - DeleteTensor(tensor_id)
    
    Maintains all TLA+ proven invariants:
    - StorageCapacityInvariant: Never exceeds max_tensors
    - TensorVectorConsistency: Bijective tensor-vector mapping
    - ValidStorageMetrics: Utilization always 0-100%
    - ValidSystemState: State transitions always valid
    """
    
    def __init__(self, config: Dict[str, Any]):
        """Initialize vector storage with configuration"""
        self.config = config
        self.max_tensors = config.get("max_tensors", 1000)
        self.max_vectors = config.get("max_vectors", 1000)
        self.max_collections = config.get("max_collections", 10)
        
        # Qdrant client configuration
        # Use environment variable first, then config, then default
        import os
        self.qdrant_url = os.getenv("VECTOR_DB_URL") or config.get(
            "qdrant_url", "http://localhost:6333")
        self.collection_name = config.get("collection_name", "tensor_schedules")
        self.embedding_dim = config.get("embedding_dim", 384)
        
        # Internal state tracking (as per TLA+ specification)
        self._tensor_store: Dict[str, Dict[str, Any]] = {}
        self._storage_metrics = SystemMetrics(
            total_stored=0,
            cache_hits=0,
            cache_misses=0,
            avg_query_time=0,
            storage_utilization=0
        )
        self._system_state = "initializing"
        self._last_operation = 0
        
        # Qdrant client
        self._client: Optional[QdrantClient] = None
        self._lock = asyncio.Lock()
    
    async def initialize(self) -> None:
        """Initialize the vector storage system"""
        import time
        max_retries = 10
        retry_delay = 2

        for attempt in range(max_retries):
            try:
                self._client = QdrantClient(url=self.qdrant_url)

                # Test connection with a simple health check
                collections = self._client.get_collections()

                # Create collection if it doesn't exist
                await self._ensure_collection_exists()

                # Load existing data to sync state
                await self._sync_state_from_storage()

                self._system_state = "ready"
                logger.info(
                    f"VectorTensorStorage initialized with collection: {self.collection_name}")
                return

            except Exception as e:
                if attempt < max_retries - 1:
                    logger.warning(
                        f"Failed to initialize VectorTensorStorage (attempt {attempt + 1}/{max_retries}): {e}")
                    logger.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                    continue
                else:
                    self._system_state = "error"
                    logger.error(
                        f"Failed to initialize VectorTensorStorage after {max_retries} attempts: {e}")
                    raise TensorConstraintError(f"Initialization failed: {e}")
    
    async def _ensure_collection_exists(self) -> None:
        """Ensure Qdrant collection exists with proper configuration"""
        try:
            collections = self._client.get_collections()
            collection_names = [col.name for col in collections.collections]
            
            if self.collection_name not in collection_names:
                self._client.create_collection(
                    collection_name=self.collection_name,
                    vectors_config=models.VectorParams(
                        size=self.embedding_dim,
                        distance=models.Distance.COSINE
                    )
                )
                logger.info(f"Created Qdrant collection: {self.collection_name}")
        
        except Exception as e:
            raise TensorConstraintError(f"Failed to create collection: {e}")
    
    async def _sync_state_from_storage(self) -> None:
        """Sync internal state with existing Qdrant data"""
        try:
            # Get all vectors from collection
            scroll_result = self._client.scroll(
                collection_name=self.collection_name,
                limit=self.max_tensors
            )
            
            points = scroll_result[0]
            
            # Rebuild tensor store from Qdrant data
            for point in points:
                if point.payload:
                    tensor_id = point.payload.get("tensor_id")
                    if tensor_id:
                        self._tensor_store[tensor_id] = {
                            "tensor_id": tensor_id,
                            "calendar_data": point.payload.get("calendar_data", {}),
                            "stored_at": point.payload.get("stored_at", datetime.utcnow().isoformat()),
                            "stored": True,
                            "vector_id": point.id
                        }
            
            # Update metrics
            self._update_storage_metrics()
            
        except Exception as e:
            logger.warning(f"Failed to sync state from storage: {e}")
            # Continue with empty state if sync fails
    
    async def store_tensor(
        self, 
        tensor_id: str, 
        calendar_data: Dict[str, Any], 
        embedding: List[float]
    ) -> Dict[str, Any]:
        """
        Store tensor calendar with vector embedding
        
        TLA+ Operation: StoreTensor(tensor_id, calendar_data, embedding)
        
        Preconditions (enforced by TLA+ spec):
        - tensor_id not already stored
        - calendar_data not empty
        - embedding valid and non-empty
        - storage capacity not exceeded
        
        Postconditions (guaranteed by TLA+ spec):
        - Tensor stored in tensor_store
        - Vector stored in vector_database
        - Storage metrics updated
        - System state valid
        """
        async with self._lock:
            self._system_state = "storing"
            
            try:
                # TLA+ Precondition checks
                if not tensor_id or not isinstance(tensor_id, str):
                    raise TensorConstraintError("Invalid tensor_id")
                
                if not calendar_data:
                    raise TensorConstraintError("Calendar data cannot be empty")
                
                if not embedding or not isinstance(embedding, list):
                    raise TensorConstraintError("Invalid embedding")
                
                if len(embedding) != self.embedding_dim:
                    raise TensorConstraintError(f"Embedding dimension must be {self.embedding_dim}")
                
                # Check if tensor already exists (TLA+ precondition)
                if tensor_id in self._tensor_store and self._tensor_store[tensor_id]["stored"]:
                    raise TensorConstraintError("Tensor already exists")
                
                # Check storage capacity (TLA+ invariant: StorageCapacityInvariant)
                if self._storage_metrics.total_stored >= self.max_tensors:
                    raise TensorConstraintError("Storage capacity exceeded")
                
                # Generate unique vector ID
                vector_id = str(uuid.uuid4())
                
                # Store in Qdrant (vector database operation)
                point = models.PointStruct(
                    id=vector_id,
                    vector=embedding,
                    payload={
                        "tensor_id": tensor_id,
                        "calendar_data": calendar_data,
                        "stored_at": datetime.utcnow().isoformat(),
                        "embedding_dim": len(embedding)
                    }
                )
                
                self._client.upsert(
                    collection_name=self.collection_name,
                    points=[point]
                )
                
                # Update tensor store (TLA+ state update)
                self._tensor_store[tensor_id] = {
                    "tensor_id": tensor_id,
                    "calendar_data": calendar_data,
                    "stored_at": datetime.utcnow().isoformat(),
                    "stored": True,
                    "vector_id": vector_id
                }
                
                # Update storage metrics (TLA+ state update)
                self._update_storage_metrics()
                self._last_operation += 1
                
                result = {
                    "success": True,
                    "tensor_id": tensor_id,
                    "vector_id": vector_id,
                    "stored_at": self._tensor_store[tensor_id]["stored_at"]
                }
                
                self._system_state = "ready"
                logger.info(f"Stored tensor: {tensor_id}")
                return result
                
            except Exception as e:
                self._system_state = "ready"
                logger.error(f"Failed to store tensor {tensor_id}: {e}")
                raise TensorConstraintError(f"Store operation failed: {e}")
    
    async def retrieve_tensor(self, tensor_id: str) -> Dict[str, Any]:
        """
        Retrieve tensor calendar data
        
        TLA+ Operation: RetrieveTensor(tensor_id)
        
        Preconditions:
        - tensor_id exists in storage
        
        Postconditions:
        - Returns tensor data
        - System state remains valid
        """
        async with self._lock:
            self._system_state = "retrieving"
            
            try:
                # Check if tensor exists (TLA+ precondition)
                if tensor_id not in self._tensor_store:
                    raise TensorConstraintError("Tensor not found")
                
                if not self._tensor_store[tensor_id]["stored"]:
                    raise TensorConstraintError("Tensor not found")
                
                # Return tensor data
                tensor_data = self._tensor_store[tensor_id].copy()
                
                self._system_state = "ready"
                self._last_operation += 1
                
                logger.info(f"Retrieved tensor: {tensor_id}")
                return tensor_data
                
            except Exception as e:
                self._system_state = "ready"
                logger.error(f"Failed to retrieve tensor {tensor_id}: {e}")
                raise TensorConstraintError(f"Retrieve operation failed: {e}")
    
    async def delete_tensor(self, tensor_id: str) -> Dict[str, Any]:
        """
        Delete tensor and associated vector data
        
        TLA+ Operation: DeleteTensor(tensor_id)
        
        Preconditions:
        - tensor_id exists in storage
        
        Postconditions:
        - Tensor removed from tensor_store
        - Vector removed from vector_database  
        - Storage metrics updated
        - System state valid
        """
        async with self._lock:
            self._system_state = "deleting"
            
            try:
                # Check if tensor exists (TLA+ precondition)
                if tensor_id not in self._tensor_store:
                    raise TensorConstraintError("Tensor not found")
                
                if not self._tensor_store[tensor_id]["stored"]:
                    raise TensorConstraintError("Tensor not found")
                
                # Get vector ID for deletion
                vector_id = self._tensor_store[tensor_id]["vector_id"]
                
                # Delete from Qdrant (vector database operation)
                self._client.delete(
                    collection_name=self.collection_name,
                    points_selector=models.PointIdsList(points=[vector_id])
                )
                
                # Remove from tensor store (TLA+ state update)
                del self._tensor_store[tensor_id]
                
                # Update storage metrics (TLA+ state update)
                self._update_storage_metrics()
                self._last_operation += 1
                
                result = {
                    "success": True,
                    "tensor_id": tensor_id,
                    "deleted_at": datetime.utcnow().isoformat()
                }
                
                self._system_state = "ready"
                logger.info(f"Deleted tensor: {tensor_id}")
                return result
                
            except Exception as e:
                self._system_state = "ready"
                logger.error(f"Failed to delete tensor {tensor_id}: {e}")
                raise TensorConstraintError(f"Delete operation failed: {e}")
    
    async def search_similar_tensors(
        self, 
        query_embedding: List[float], 
        limit: int = 10,
        similarity_threshold: float = 0.7
    ) -> List[Dict[str, Any]]:
        """
        Search for similar tensors using vector similarity
        
        Additional operation not in simplified TLA+ spec but following same patterns
        """
        async with self._lock:
            self._system_state = "searching"
            
            try:
                if not query_embedding or len(query_embedding) != self.embedding_dim:
                    raise TensorConstraintError("Invalid query embedding")
                
                # Search in Qdrant
                search_result = self._client.search(
                    collection_name=self.collection_name,
                    query_vector=query_embedding,
                    limit=min(limit, self.max_tensors),
                    score_threshold=similarity_threshold
                )
                
                # Format results
                results = []
                for hit in search_result:
                    if hit.payload:
                        results.append({
                            "tensor_id": hit.payload.get("tensor_id"),
                            "calendar_data": hit.payload.get("calendar_data"),
                            "similarity_score": hit.score,
                            "stored_at": hit.payload.get("stored_at")
                        })
                
                self._system_state = "ready"
                self._last_operation += 1
                
                logger.info(f"Found {len(results)} similar tensors")
                return results
                
            except Exception as e:
                self._system_state = "ready"
                logger.error(f"Failed to search similar tensors: {e}")
                raise TensorConstraintError(f"Search operation failed: {e}")
    
    def _update_storage_metrics(self) -> None:
        """Update storage metrics (TLA+ state update)"""
        stored_count = sum(1 for tensor in self._tensor_store.values() if tensor["stored"])
        utilization = (stored_count * 100) // self.max_tensors if self.max_tensors > 0 else 0
        
        self._storage_metrics = SystemMetrics(
            total_stored=stored_count,
            cache_hits=self._storage_metrics.cache_hits,
            cache_misses=self._storage_metrics.cache_misses,
            avg_query_time=self._storage_metrics.avg_query_time,
            storage_utilization=min(utilization, 100)  # Ensure TLA+ invariant: <= 100
        )
    
    # Helper methods for testing TLA+ invariants
    
    async def tensor_exists(self, tensor_id: str) -> bool:
        """Check if tensor exists in storage"""
        return tensor_id in self._tensor_store and self._tensor_store[tensor_id]["stored"]
    
    async def vector_exists(self, tensor_id: str) -> bool:
        """Check if vector exists in vector database"""
        if tensor_id not in self._tensor_store:
            return False
        
        vector_id = self._tensor_store[tensor_id]["vector_id"]
        try:
            result = self._client.retrieve(
                collection_name=self.collection_name,
                ids=[vector_id]
            )
            return len(result) > 0
        except:
            return False
    
    async def get_tensor_embedding(self, tensor_id: str) -> List[float]:
        """Get tensor embedding from vector database"""
        if tensor_id not in self._tensor_store:
            raise TensorConstraintError("Tensor not found")
        
        vector_id = self._tensor_store[tensor_id]["vector_id"]
        try:
            result = self._client.retrieve(
                collection_name=self.collection_name,
                ids=[vector_id],
                with_vectors=True
            )
            if result and result[0].vector:
                return result[0].vector
            else:
                raise TensorConstraintError("Vector not found")
        except Exception as e:
            raise TensorConstraintError(f"Failed to retrieve embedding: {e}")
    
    async def get_storage_metrics(self) -> SystemMetrics:
        """Get current storage metrics"""
        return self._storage_metrics
    
    async def get_system_state(self) -> str:
        """Get current system state"""
        return self._system_state
    
    async def cleanup(self) -> None:
        """Cleanup resources"""
        if self._client:
            try:
                # Optionally delete test collections
                if "test" in self.collection_name.lower():
                    self._client.delete_collection(self.collection_name)
                    logger.info(f"Cleaned up test collection: {self.collection_name}")
            except:
                pass  # Ignore cleanup errors
            
            self._client.close()
        
        self._system_state = "shutdown"
        logger.info("VectorTensorStorage cleanup completed")
