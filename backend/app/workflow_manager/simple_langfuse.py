"""
Simple Langfuse Integration for ALIMS (v3.2.1 compatible)
"""

import os
import uuid
from datetime import datetime
from typing import Dict, Any, Optional
from langfuse import Langfuse
import logging

logger = logging.getLogger(__name__)

class SimpleLangfuseLIMSMonitor:
    """Simplified Langfuse monitoring for ALIMS workflows"""
    
    def __init__(self):
        # Get credentials
        self.public_key = os.getenv("LANGFUSE_PUBLIC_KEY")
        self.secret_key = os.getenv("LANGFUSE_SECRET_KEY")
        self.host = os.getenv("LANGFUSE_HOST", "https://cloud.langfuse.com")
        
        if not self.public_key or not self.secret_key:
            logger.warning("Langfuse credentials not found. Monitoring disabled.")
            self.enabled = False
            self.client = None
        else:
            self.enabled = True
            self.client = Langfuse()
            logger.info("Langfuse monitoring enabled")
        
        self.active_workflows = {}
    
    def start_workflow(self, priority: str, initiated_by: str) -> str:
        """Start monitoring a workflow"""
        if not self.enabled:
            return str(uuid.uuid4())
        
        workflow_id = str(uuid.uuid4())
        
        try:
            # Create workflow event
            self.client.create_event(
                name="workflow_started",
                metadata={
                    "workflow_id": workflow_id,
                    "priority": priority,
                    "initiated_by": initiated_by,
                    "system": "ALIMS",
                    "started_at": datetime.now().isoformat()
                }
            )
            
            self.active_workflows[workflow_id] = {
                "priority": priority,
                "initiated_by": initiated_by,
                "started_at": datetime.now()
            }
            
            logger.info(f"Started workflow monitoring: {workflow_id}")
            
        except Exception as e:
            logger.error(f"Failed to start workflow monitoring: {e}")
        
        return workflow_id
    
    def track_state_transition(self, workflow_id: str, from_state: str, 
                              to_state: str, context: Optional[Dict] = None):
        """Track workflow state transition"""
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        try:
            self.client.create_event(
                name="state_transition",
                metadata={
                    "workflow_id": workflow_id,
                    "from_state": from_state,
                    "to_state": to_state,
                    "context": context or {},
                    "timestamp": datetime.now().isoformat(),
                    "system": "ALIMS"
                }
            )
            
            logger.info(f"Tracked transition {from_state} -> {to_state} for {workflow_id}")
            
        except Exception as e:
            logger.error(f"Failed to track state transition: {e}")
    
    def complete_workflow(self, workflow_id: str, success: bool, 
                         result: Optional[Dict] = None):
        """Complete workflow monitoring"""
        if not self.enabled or workflow_id not in self.active_workflows:
            return
        
        try:
            workflow_info = self.active_workflows[workflow_id]
            duration = (datetime.now() - workflow_info["started_at"]).total_seconds()
            
            self.client.create_event(
                name="workflow_completed",
                metadata={
                    "workflow_id": workflow_id,
                    "success": success,
                    "duration_seconds": duration,
                    "result": result or {},
                    "completed_at": datetime.now().isoformat(),
                    "system": "ALIMS"
                }
            )
            
            # Remove from active workflows
            del self.active_workflows[workflow_id]
            
            logger.info(f"Completed workflow monitoring: {workflow_id} (success: {success})")
            
        except Exception as e:
            logger.error(f"Failed to complete workflow monitoring: {e}")
    
    def flush(self):
        """Flush pending data to Langfuse"""
        if self.enabled and self.client:
            try:
                self.client.flush()
            except Exception as e:
                logger.error(f"Failed to flush Langfuse data: {e}")

# Create global instance
monitor = SimpleLangfuseLIMSMonitor()

# Export for easy use
LangfuseLIMSMonitor = SimpleLangfuseLIMSMonitor
