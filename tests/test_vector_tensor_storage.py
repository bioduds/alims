"""
Test Suite for Tensor Calendar Vector Storage Integration
Based on TLA+ validated specification: TensorCalendarVectorStorageSimple.tla

This test suite ensures that the Python implementation follows the mathematically
proven properties from the TLA+ specification.
"""

import pytest
from unittest.mock import Mock, patch, AsyncMock
import asyncio
from typing import Dict, Any, List, Optional
import numpy as np

# We'll implement these modules based on TLA+ spec
from backend.app.tensor_calendar.vector_storage import VectorTensorStorage
from backend.app.tensor_calendar.models import TensorCalendar, SystemMetrics
from backend.app.tensor_calendar.exceptions import TensorConstraintError


class TestVectorTensorStorageInvariants:
    """Test all TLA+ validated invariants"""
    
    @pytest.fixture
    async def storage(self):
        """Create storage instance with test configuration"""
        config = {
            "max_tensors": 5,
            "max_vectors": 5,
            "max_collections": 3,
            "qdrant_url": "http://localhost:6333",
            "collection_name": "test_tensor_schedules"
        }
        storage = VectorTensorStorage(config)
        await storage.initialize()
        yield storage
        await storage.cleanup()
    
    @pytest.fixture
    def sample_tensor_data(self):
        """Sample tensor calendar data"""
        return {
            "tensor_id": "tensor_001",
            "calendar_data": {
                "schedule_type": "laboratory",
                "time_slots": ["09:00-10:00", "14:00-15:00"],
                "resources": ["microscope_1", "centrifuge_2"],
                "samples": ["sample_A", "sample_B"]
            },
            "embedding": np.random.rand(384).tolist()  # Typical embedding dimension
        }

    async def test_storage_capacity_invariant(self, storage, sample_tensor_data):
        """
        TLA+ Invariant: StorageCapacityInvariant
        Verify storage never exceeds maximum tensor capacity
        """
        max_tensors = storage.config["max_tensors"]
        
        # Store tensors up to capacity
        stored_ids = []
        for i in range(max_tensors):
            tensor_data = sample_tensor_data.copy()
            tensor_data["tensor_id"] = f"tensor_{i:03d}"
            
            result = await storage.store_tensor(
                tensor_data["tensor_id"],
                tensor_data["calendar_data"],
                tensor_data["embedding"]
            )
            assert result["success"] is True
            stored_ids.append(tensor_data["tensor_id"])
        
        # Verify capacity limit is enforced
        overflow_tensor = sample_tensor_data.copy()
        overflow_tensor["tensor_id"] = "tensor_overflow"
        
        with pytest.raises(TensorConstraintError, match="Storage capacity exceeded"):
            await storage.store_tensor(
                overflow_tensor["tensor_id"],
                overflow_tensor["calendar_data"],
                overflow_tensor["embedding"]
            )
        
        # Verify metrics reflect capacity limit
        metrics = await storage.get_storage_metrics()
        assert metrics.total_stored == max_tensors
        assert metrics.storage_utilization == 100
    
    async def test_tensor_vector_consistency(self, storage, sample_tensor_data):
        """
        TLA+ Invariant: TensorVectorConsistency
        Every stored tensor has valid vector database mapping
        """
        tensor_id = sample_tensor_data["tensor_id"]
        
        # Store tensor
        await storage.store_tensor(
            tensor_id,
            sample_tensor_data["calendar_data"],
            sample_tensor_data["embedding"]
        )
        
        # Verify tensor exists in tensor store
        tensor_exists = await storage.tensor_exists(tensor_id)
        assert tensor_exists is True
        
        # Verify corresponding vector exists in vector database
        vector_exists = await storage.vector_exists(tensor_id)
        assert vector_exists is True
        
        # Verify embedding consistency
        stored_embedding = await storage.get_tensor_embedding(tensor_id)
        np.testing.assert_array_almost_equal(
            stored_embedding,
            sample_tensor_data["embedding"],
            decimal=6
        )
        
        # Delete tensor and verify both are removed
        await storage.delete_tensor(tensor_id)
        
        assert await storage.tensor_exists(tensor_id) is False
        assert await storage.vector_exists(tensor_id) is False
    
    async def test_valid_storage_metrics(self, storage, sample_tensor_data):
        """
        TLA+ Invariant: ValidStorageMetrics
        Storage utilization percentages remain within valid bounds (0-100%)
        """
        # Initial state
        metrics = await storage.get_storage_metrics()
        assert 0 <= metrics.storage_utilization <= 100
        assert metrics.total_stored >= 0
        
        # Store some tensors
        for i in range(3):
            tensor_data = sample_tensor_data.copy()
            tensor_data["tensor_id"] = f"test_tensor_{i}"
            await storage.store_tensor(
                tensor_data["tensor_id"],
                tensor_data["calendar_data"],
                tensor_data["embedding"]
            )
            
            # Check metrics remain valid after each operation
            metrics = await storage.get_storage_metrics()
            assert 0 <= metrics.storage_utilization <= 100
            assert metrics.total_stored >= 0
            assert metrics.total_stored == i + 1
        
        # Delete tensors and verify metrics
        for i in range(3):
            await storage.delete_tensor(f"test_tensor_{i}")
            metrics = await storage.get_storage_metrics()
            assert 0 <= metrics.storage_utilization <= 100
            assert metrics.total_stored >= 0
    
    async def test_valid_system_state(self, storage, sample_tensor_data):
        """
        TLA+ Invariant: ValidSystemState
        System state always remains in valid transitions
        """
        valid_states = {
            "initializing", "storing", "retrieving", "deleting", "ready"
        }
        
        # Check initial state
        state = await storage.get_system_state()
        assert state in valid_states
        
        # Perform operations and verify state transitions
        tensor_id = sample_tensor_data["tensor_id"]
        
        # Store operation
        await storage.store_tensor(
            tensor_id,
            sample_tensor_data["calendar_data"],
            sample_tensor_data["embedding"]
        )
        state = await storage.get_system_state()
        assert state in valid_states
        
        # Retrieve operation
        await storage.retrieve_tensor(tensor_id)
        state = await storage.get_system_state()
        assert state in valid_states
        
        # Delete operation
        await storage.delete_tensor(tensor_id)
        state = await storage.get_system_state()
        assert state in valid_states


class TestVectorTensorStorageOperations:
    """Test core operations from TLA+ specification"""
    
    @pytest.fixture
    async def storage(self):
        """Create storage instance"""
        config = {
            "max_tensors": 10,
            "max_vectors": 10,
            "max_collections": 5,
            "qdrant_url": "http://localhost:6333",
            "collection_name": "test_operations"
        }
        storage = VectorTensorStorage(config)
        await storage.initialize()
        yield storage
        await storage.cleanup()
    
    async def test_store_tensor_operation(self, storage):
        """
        Test StoreTensor operation from TLA+ spec
        """
        tensor_id = "test_store_001"
        calendar_data = {
            "type": "lab_schedule",
            "sessions": [
                {"time": "09:00", "duration": 60, "resource": "microscope"},
                {"time": "14:00", "duration": 90, "resource": "centrifuge"}
            ]
        }
        embedding = np.random.rand(384).tolist()
        
        # Execute store operation
        result = await storage.store_tensor(tensor_id, calendar_data, embedding)
        
        # Verify operation success
        assert result["success"] is True
        assert result["tensor_id"] == tensor_id
        
        # Verify data is stored correctly
        retrieved_data = await storage.retrieve_tensor(tensor_id)
        assert retrieved_data["tensor_id"] == tensor_id
        assert retrieved_data["calendar_data"] == calendar_data
        
        # Verify embedding is stored
        stored_embedding = await storage.get_tensor_embedding(tensor_id)
        np.testing.assert_array_almost_equal(stored_embedding, embedding)
    
    async def test_retrieve_tensor_operation(self, storage):
        """
        Test RetrieveTensor operation from TLA+ spec
        """
        tensor_id = "test_retrieve_001"
        calendar_data = {"schedule": "test_data"}
        embedding = np.random.rand(256).tolist()
        
        # Store tensor first
        await storage.store_tensor(tensor_id, calendar_data, embedding)
        
        # Test retrieval
        retrieved = await storage.retrieve_tensor(tensor_id)
        
        assert retrieved["tensor_id"] == tensor_id
        assert retrieved["calendar_data"] == calendar_data
        assert "stored_at" in retrieved
        assert retrieved["stored"] is True
        
        # Test retrieval of non-existent tensor
        with pytest.raises(TensorConstraintError, match="Tensor not found"):
            await storage.retrieve_tensor("non_existent_tensor")
    
    async def test_delete_tensor_operation(self, storage):
        """
        Test DeleteTensor operation from TLA+ spec
        """
        tensor_id = "test_delete_001"
        calendar_data = {"schedule": "delete_test"}
        embedding = np.random.rand(128).tolist()
        
        # Store tensor
        await storage.store_tensor(tensor_id, calendar_data, embedding)
        
        # Verify tensor exists
        assert await storage.tensor_exists(tensor_id) is True
        assert await storage.vector_exists(tensor_id) is True
        
        # Delete tensor
        result = await storage.delete_tensor(tensor_id)
        assert result["success"] is True
        assert result["tensor_id"] == tensor_id
        
        # Verify tensor is completely removed
        assert await storage.tensor_exists(tensor_id) is False
        assert await storage.vector_exists(tensor_id) is False
        
        # Verify metrics updated
        metrics = await storage.get_storage_metrics()
        assert metrics.total_stored == 0
        
        # Test deletion of non-existent tensor
        with pytest.raises(TensorConstraintError, match="Tensor not found"):
            await storage.delete_tensor("non_existent_tensor")


class TestVectorTensorStorageTemporalProperties:
    """Test temporal properties from TLA+ specification"""
    
    @pytest.fixture
    async def storage(self):
        """Create storage instance"""
        config = {
            "max_tensors": 3,
            "max_vectors": 3,
            "max_collections": 2,
            "qdrant_url": "http://localhost:6333",
            "collection_name": "test_temporal"
        }
        storage = VectorTensorStorage(config)
        await storage.initialize()
        yield storage
        await storage.cleanup()
    
    async def test_system_progress_property(self, storage):
        """
        TLA+ Property: SystemProgress
        System can always make forward progress
        """
        # Perform sequence of operations that should always progress
        operations = [
            ("store", "tensor_1", {"data": "test1"}, np.random.rand(64).tolist()),
            ("retrieve", "tensor_1", None, None),
            ("store", "tensor_2", {"data": "test2"}, np.random.rand(64).tolist()),
            ("delete", "tensor_1", None, None),
            ("store", "tensor_3", {"data": "test3"}, np.random.rand(64).tolist()),
            ("retrieve", "tensor_2", None, None),
            ("delete", "tensor_2", None, None),
            ("delete", "tensor_3", None, None),
        ]
        
        for operation, tensor_id, calendar_data, embedding in operations:
            initial_state = await storage.get_system_state()
            
            if operation == "store":
                result = await storage.store_tensor(tensor_id, calendar_data, embedding)
                assert result["success"] is True
            elif operation == "retrieve":
                result = await storage.retrieve_tensor(tensor_id)
                assert result["tensor_id"] == tensor_id
            elif operation == "delete":
                result = await storage.delete_tensor(tensor_id)
                assert result["success"] is True
            
            # Verify system can always transition to a valid state
            final_state = await storage.get_system_state()
            valid_states = {"ready", "storing", "retrieving", "deleting"}
            assert final_state in valid_states


class TestVectorTensorStorageEdgeCases:
    """Test edge cases and error conditions"""
    
    @pytest.fixture
    async def storage(self):
        """Create storage instance"""
        config = {
            "max_tensors": 2,
            "max_vectors": 2,
            "max_collections": 1,
            "qdrant_url": "http://localhost:6333",
            "collection_name": "test_edge_cases"
        }
        storage = VectorTensorStorage(config)
        await storage.initialize()
        yield storage
        await storage.cleanup()
    
    async def test_duplicate_tensor_storage(self, storage):
        """Test storing tensor with duplicate ID"""
        tensor_id = "duplicate_test"
        calendar_data1 = {"version": 1}
        calendar_data2 = {"version": 2}
        embedding = np.random.rand(32).tolist()
        
        # Store first tensor
        result1 = await storage.store_tensor(tensor_id, calendar_data1, embedding)
        assert result1["success"] is True
        
        # Attempt to store duplicate
        with pytest.raises(TensorConstraintError, match="Tensor already exists"):
            await storage.store_tensor(tensor_id, calendar_data2, embedding)
    
    async def test_invalid_embedding_dimensions(self, storage):
        """Test storing tensor with invalid embedding"""
        tensor_id = "invalid_embedding_test"
        calendar_data = {"test": "data"}
        
        # Test empty embedding
        with pytest.raises(TensorConstraintError, match="Invalid embedding"):
            await storage.store_tensor(tensor_id, calendar_data, [])
        
        # Test non-numeric embedding
        with pytest.raises(TensorConstraintError, match="Invalid embedding"):
            await storage.store_tensor(tensor_id, calendar_data, ["not", "numeric"])
    
    async def test_empty_calendar_data(self, storage):
        """Test storing tensor with empty calendar data"""
        tensor_id = "empty_data_test"
        embedding = np.random.rand(16).tolist()
        
        with pytest.raises(TensorConstraintError, match="Calendar data cannot be empty"):
            await storage.store_tensor(tensor_id, {}, embedding)
    
    async def test_concurrent_operations(self, storage):
        """Test concurrent operations maintain consistency"""
        async def store_tensor(tensor_id: str):
            calendar_data = {"concurrent_test": tensor_id}
            embedding = np.random.rand(32).tolist()
            return await storage.store_tensor(tensor_id, calendar_data, embedding)
        
        # Attempt concurrent stores
        tasks = [
            store_tensor("concurrent_1"),
            store_tensor("concurrent_2")
        ]
        
        results = await asyncio.gather(*tasks, return_exceptions=True)
        
        # Verify at least one succeeded and consistency is maintained
        successes = [r for r in results if isinstance(r, dict) and r.get("success")]
        assert len(successes) >= 1
        
        # Verify storage metrics are consistent
        metrics = await storage.get_storage_metrics()
        assert metrics.total_stored == len(successes)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
