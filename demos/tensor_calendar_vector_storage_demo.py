"""
Integration test for TLA+ verified Tensor Calendar Vector Storage
Demonstrates the complete system working with Qdrant vector database
"""

import asyncio
import numpy as np
import logging
from typing import Dict, Any

from backend.app.tensor_calendar import VectorTensorStorage, TensorConstraintError

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


async def test_tensor_calendar_vector_storage():
    """
    Integration test demonstrating TLA+ verified operations
    """
    # Configuration for vector storage
    config = {
        "max_tensors": 10,
        "max_vectors": 10, 
        "max_collections": 5,
        "qdrant_url": "http://localhost:6333",
        "collection_name": "demo_tensor_schedules",
        "embedding_dim": 384
    }
    
    # Initialize storage
    storage = VectorTensorStorage(config)
    
    try:
        # Initialize connection to Qdrant
        await storage.initialize()
        logger.info("✅ Vector storage initialized successfully")
        
        # Test data: Laboratory scheduling scenarios
        test_tensors = [
            {
                "tensor_id": "lab_schedule_001",
                "calendar_data": {
                    "schedule_type": "microscopy_session",
                    "date": "2025-07-10",
                    "time_slots": [
                        {"start": "09:00", "end": "10:30", "resource": "confocal_microscope_1"},
                        {"start": "14:00", "end": "15:30", "resource": "confocal_microscope_1"}
                    ],
                    "samples": ["sample_cell_culture_A", "sample_tissue_B"],
                    "researcher": "dr_smith",
                    "workflow": "live_cell_imaging"
                },
                "embedding": np.random.rand(384).tolist()
            },
            {
                "tensor_id": "lab_schedule_002", 
                "calendar_data": {
                    "schedule_type": "pcr_workflow",
                    "date": "2025-07-10",
                    "time_slots": [
                        {"start": "10:00", "end": "12:00", "resource": "thermal_cycler_2"},
                        {"start": "15:00", "end": "17:00", "resource": "gel_electrophoresis"}
                    ],
                    "samples": ["dna_sample_001", "dna_sample_002", "dna_sample_003"],
                    "researcher": "dr_jones",
                    "workflow": "gene_amplification"
                },
                "embedding": np.random.rand(384).tolist()
            },
            {
                "tensor_id": "lab_schedule_003",
                "calendar_data": {
                    "schedule_type": "mass_spec_analysis",
                    "date": "2025-07-11",
                    "time_slots": [
                        {"start": "08:00", "end": "11:00", "resource": "lcms_system_1"}
                    ],
                    "samples": ["protein_extract_A", "protein_extract_B"],
                    "researcher": "dr_wilson", 
                    "workflow": "protein_identification"
                },
                "embedding": np.random.rand(384).tolist()
            }
        ]
        
        # Test 1: Store tensor calendars (TLA+ StoreTensor operation)
        logger.info("\n🧪 Test 1: Storing tensor calendars...")
        for tensor_data in test_tensors:
            result = await storage.store_tensor(
                tensor_data["tensor_id"],
                tensor_data["calendar_data"], 
                tensor_data["embedding"]
            )
            logger.info(f"✅ Stored tensor: {result['tensor_id']}")
        
        # Verify storage metrics
        metrics = await storage.get_storage_metrics()
        logger.info(f"📊 Storage metrics: {metrics.total_stored} tensors, {metrics.storage_utilization}% utilization")
        
        # Test 2: Retrieve tensor calendars (TLA+ RetrieveTensor operation)
        logger.info("\n🔍 Test 2: Retrieving tensor calendars...")
        for tensor_data in test_tensors:
            retrieved = await storage.retrieve_tensor(tensor_data["tensor_id"])
            logger.info(f"✅ Retrieved tensor: {retrieved['tensor_id']}")
            assert retrieved["calendar_data"] == tensor_data["calendar_data"]
        
        # Test 3: Search similar tensors (vector similarity search)
        logger.info("\n🔎 Test 3: Searching for similar tensors...")
        query_embedding = test_tensors[0]["embedding"]  # Use first tensor as query
        similar_tensors = await storage.search_similar_tensors(
            query_embedding, 
            limit=5,
            similarity_threshold=0.5
        )
        logger.info(f"✅ Found {len(similar_tensors)} similar tensors")
        for tensor in similar_tensors:
            logger.info(f"   - {tensor['tensor_id']}: similarity {tensor['similarity_score']:.3f}")
        
        # Test 4: Test TLA+ invariants
        logger.info("\n🔒 Test 4: Verifying TLA+ invariants...")
        
        # StorageCapacityInvariant
        assert metrics.total_stored <= config["max_tensors"]
        logger.info("✅ StorageCapacityInvariant: Storage within capacity limits")
        
        # TensorVectorConsistency  
        for tensor_data in test_tensors:
            tensor_id = tensor_data["tensor_id"]
            tensor_exists = await storage.tensor_exists(tensor_id)
            vector_exists = await storage.vector_exists(tensor_id)
            assert tensor_exists == vector_exists  # Bijective mapping
        logger.info("✅ TensorVectorConsistency: Tensor-vector mappings consistent")
        
        # ValidStorageMetrics
        assert 0 <= metrics.storage_utilization <= 100
        assert metrics.total_stored >= 0
        logger.info("✅ ValidStorageMetrics: All metrics within valid ranges")
        
        # ValidSystemState
        system_state = await storage.get_system_state()
        valid_states = {"ready", "storing", "retrieving", "deleting", "searching"}
        assert system_state in valid_states
        logger.info(f"✅ ValidSystemState: System in valid state '{system_state}'")
        
        # Test 5: Delete tensor calendars (TLA+ DeleteTensor operation)
        logger.info("\n🗑️  Test 5: Deleting tensor calendars...")
        for tensor_data in test_tensors:
            result = await storage.delete_tensor(tensor_data["tensor_id"])
            logger.info(f"✅ Deleted tensor: {result['tensor_id']}")
        
        # Verify all tensors deleted
        final_metrics = await storage.get_storage_metrics()
        assert final_metrics.total_stored == 0
        logger.info("✅ All tensors successfully deleted")
        
        # Test 6: Error condition tests (TLA+ constraint violations)
        logger.info("\n⚠️  Test 6: Testing error conditions...")
        
        # Test storage of non-existent tensor retrieval
        try:
            await storage.retrieve_tensor("non_existent_tensor")
            assert False, "Should have raised TensorConstraintError"
        except TensorConstraintError:
            logger.info("✅ Correctly rejected retrieval of non-existent tensor")
        
        # Test duplicate tensor storage
        test_tensor = test_tensors[0]
        await storage.store_tensor(
            test_tensor["tensor_id"],
            test_tensor["calendar_data"],
            test_tensor["embedding"]
        )
        
        try:
            await storage.store_tensor(
                test_tensor["tensor_id"],  # Same ID
                {"different": "data"},
                np.random.rand(384).tolist()
            )
            assert False, "Should have raised TensorConstraintError"
        except TensorConstraintError:
            logger.info("✅ Correctly rejected duplicate tensor storage")
        
        # Clean up
        await storage.delete_tensor(test_tensor["tensor_id"])
        
        logger.info("\n🎉 All tests passed! TLA+ verified Tensor Calendar Vector Storage is working correctly.")
        
    except Exception as e:
        logger.error(f"❌ Test failed: {e}")
        raise
    
    finally:
        # Cleanup
        await storage.cleanup()
        logger.info("🧹 Cleanup completed")


async def main():
    """Run the integration test"""
    logger.info("🚀 Starting TLA+ verified Tensor Calendar Vector Storage integration test...")
    logger.info("📋 This test verifies all operations from the validated TLA+ specification")
    
    await test_tensor_calendar_vector_storage()


if __name__ == "__main__":
    asyncio.run(main())
