"""
Enhanced Main Interface Agent Service - TLA+ Based Implementation with Ollama
Integrates the formally verified Main Interface Agent system with ALIMS backend and Ollama LLM.

This service replaces the previous implementation with the production-ready
TLA+ model-based agent system that provides:
- Formal verification guarantees
- Prolog-style logical reasoning
- Robust error handling and recovery
- Comprehensive audit trails
- Resource monitoring and optimization
- Intelligent Ollama-powered responses
"""

import asyncio
import logging
import time
from typing import Dict, List, Optional, Any
from datetime import datetime

from main_interface_agent import (
    MainInterfaceAgent,
    SystemConfiguration,
    ConversationState,
    AgentState,
    QueryState
)
from ollama_integration import OllamaIntegratedMainInterfaceAgent

logger = logging.getLogger(__name__)


class EnhancedLIMSMainInterfaceService:
    """
    Enhanced Main Interface Service using the TLA+ validated agent system with Ollama integration.
    Provides comprehensive integration with ALIMS backend components and intelligent LLM responses.
    """
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        self.config = config or {}
        self.base_agent_system: Optional[MainInterfaceAgent] = None
        self.agent_system: Optional[OllamaIntegratedMainInterfaceAgent] = None
        self._initialized = False
        self._background_tasks: List[asyncio.Task] = []
        
    async def initialize(self) -> bool:
        """Initialize the enhanced agent system with LIMS-specific configuration and Ollama."""
        try:
            logger.info("Initializing Enhanced Main Interface Agent System with Ollama...")
            
            # Create system configuration
            system_config = SystemConfiguration(
                MAX_CONVERSATIONS=self.config.get('max_conversations', 100),
                MAX_AGENTS=self.config.get('max_agents', 20),
                MAX_PROLOG_DEPTH=self.config.get('max_queries', 200),
                TIMEOUT_THRESHOLD=self.config.get('query_timeout', 30),
                MAX_RETRIES=self.config.get('agent_timeout', 60)
            )
            
            # Initialize the base main interface agent
            self.base_agent_system = MainInterfaceAgent(system_config)
            
            # Configure Ollama integration
            ollama_config = {
                'base_url': self.config.get('ollama_base_url', 'http://localhost:11434'),
                'model_name': self.config.get('ollama_model', 'llama3.2:latest'),
                'timeout': self.config.get('ollama_timeout', 30)
            }
            
            # Create Ollama-integrated agent system
            self.agent_system = OllamaIntegratedMainInterfaceAgent(
                base_agent=self.base_agent_system,
                ollama_config=ollama_config
            )
            
            await self.agent_system.initialize()
            
            # Register LIMS-specific agents
            await self._register_lims_agents()
            
            # Initialize LIMS-specific knowledge base
            await self._initialize_lims_knowledge_base()
            
            # Start background monitoring tasks
            await self._start_background_tasks()
            
            self._initialized = True
            logger.info("Enhanced Main Interface Agent System with Ollama initialized successfully")
            return True
            
        except Exception as e:
            logger.error(f"Failed to initialize Enhanced Main Interface Agent: {e}")
            return False
    
    async def _register_lims_agents(self):
        """Register specialized LIMS agents with their capabilities."""
        
        # Sample Management Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="sample_manager",
            capabilities={
                "sample_analysis", "sample_tracking", "sample_lifecycle", "sample_search",
                "quality_control", "chain_of_custody"
            }
        )
        
        # Laboratory Workflow Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="workflow_manager",
            capabilities={
                "protocol_management", "workflow_automation", "task_scheduling",
                "resource_allocation", "workflow_optimization"
            }
        )
        
        # Instrument Integration Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="instrument_manager",
            capabilities={
                "instrument_control", "data_acquisition", "calibration",
                "maintenance_scheduling", "performance_monitoring"
            }
        )
        
        # Data Analysis Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="data_analyst",
            capabilities={
                "statistical_analysis", "trend_analysis", "anomaly_detection",
                "report_generation", "data_visualization"
            }
        )
        
        # Compliance Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="compliance_manager",
            capabilities={
                "regulatory_compliance", "audit_trails", "documentation",
                "validation_protocols", "change_control"
            }
        )
        
        # Laboratory Safety Agent
        await self.agent_system.dispatcher.register_agent(
            agent_id="safety_manager",
            capabilities={
                "safety_monitoring", "hazard_assessment", "emergency_response",
                "training_management", "incident_reporting"
            }
        )
        
        logger.info("LIMS agents registered successfully")
    
    async def _initialize_lims_knowledge_base(self):
        """Initialize the Prolog knowledge base with LIMS-specific rules and facts."""
        
        # Sample lifecycle rules
        await self.agent_system.prolog_engine.add_rule(
            "sample_ready_for_testing",
            ["Sample", "Test"],
            [
                {"predicate": "sample_status", "args": ["Sample", "received"]},
                {"predicate": "test_available", "args": ["Test"]},
                {"predicate": "sample_meets_requirements", "args": ["Sample", "Test"]}
            ]
        )
        
        # Workflow completion rules
        await self.agent_system.prolog_engine.add_rule(
            "workflow_complete",
            ["Workflow"],
            [
                {"predicate": "all_tasks_complete", "args": ["Workflow"]},
                {"predicate": "quality_check_passed", "args": ["Workflow"]},
                {"predicate": "documentation_complete", "args": ["Workflow"]}
            ]
        )
        
        # Quality control rules
        await self.agent_system.prolog_engine.add_rule(
            "quality_control_required",
            ["Sample", "Test"],
            [
                {"predicate": "high_risk_sample", "args": ["Sample"]},
                {"predicate": "critical_test", "args": ["Test"]}
            ]
        )
        
        # Compliance verification rules
        await self.agent_system.prolog_engine.add_rule(
            "compliance_verified",
            ["Process"],
            [
                {"predicate": "sop_followed", "args": ["Process"]},
                {"predicate": "documentation_complete", "args": ["Process"]},
                {"predicate": "approval_obtained", "args": ["Process"]}
            ]
        )
        
        # Add some initial facts
        await self.agent_system.prolog_engine.add_fact("test_available", ["HPLC"])
        await self.agent_system.prolog_engine.add_fact("test_available", ["GC_MS"])
        await self.agent_system.prolog_engine.add_fact("test_available", ["UV_VIS"])
        await self.agent_system.prolog_engine.add_fact("critical_test", ["HPLC"])
        await self.agent_system.prolog_engine.add_fact("critical_test", ["GC_MS"])
        
        logger.info("LIMS knowledge base initialized")
    
    async def _start_background_tasks(self):
        """Start background monitoring and maintenance tasks."""
        
        # Resource monitoring task
        self._background_tasks.append(
            asyncio.create_task(self._monitor_system_resources())
        )
        
        # Audit log maintenance task
        self._background_tasks.append(
            asyncio.create_task(self._maintain_audit_logs())
        )
        
        # Agent health monitoring task
        self._background_tasks.append(
            asyncio.create_task(self._monitor_agent_health())
        )
        
        logger.info("Background monitoring tasks started")
    
    async def _monitor_system_resources(self):
        """Monitor system resources and optimize performance."""
        while self._initialized:
            try:
                if self.agent_system:
                    await self.agent_system.resource_monitor.update_metrics()
                    
                    # Check for resource constraints
                    status = await self.agent_system.get_system_status()
                    if status.get("resource_usage", 0) > 0.8:
                        logger.warning("High resource usage detected")
                        await self._optimize_system_performance()
                
                await asyncio.sleep(30)  # Check every 30 seconds
                
            except Exception as e:
                logger.error(f"Error in resource monitoring: {e}")
                await asyncio.sleep(60)
    
    async def _maintain_audit_logs(self):
        """Maintain audit logs and handle log rotation."""
        while self._initialized:
            try:
                if self.agent_system:
                    # Cleanup old audit events (older than 30 days)
                    cutoff_time = time.time() - (30 * 24 * 60 * 60)
                    self.agent_system.audit_trails = [
                        event for event in self.agent_system.audit_trails
                        if event.timestamp > cutoff_time
                    ]
                
                await asyncio.sleep(3600)  # Check every hour
                
            except Exception as e:
                logger.error(f"Error in audit log maintenance: {e}")
                await asyncio.sleep(3600)
    
    async def _monitor_agent_health(self):
        """Monitor agent health and handle recovery."""
        while self._initialized:
            try:
                if self.agent_system:
                    for agent_id, agent in self.agent_system.dispatcher.agents.items():
                        if agent.error_count > 5:
                            logger.warning(f"Agent {agent_id} has high error count: {agent.error_count}")
                            # Reset agent if necessary
                            await self.agent_system.dispatcher._handle_agent_error(agent_id, "High error count")
                
                await asyncio.sleep(60)  # Check every minute
                
            except Exception as e:
                logger.error(f"Error in agent health monitoring: {e}")
                await asyncio.sleep(60)
    
    async def _optimize_system_performance(self):
        """Optimize system performance when resources are constrained."""
        try:
            # Cleanup completed conversations
            completed_conversations = [
                conv_id for conv_id, conv in self.agent_system.conversations.items()
                if conv.state == ConversationState.COMPLETED
            ]
            
            for conv_id in completed_conversations:
                if len(self.agent_system.conversations) > self.agent_system.config.max_conversations // 2:
                    del self.agent_system.conversations[conv_id]
            
            # Cleanup old queries
            current_time = time.time()
            old_queries = [
                query_id for query_id, query in self.agent_system.active_queries.items()
                if current_time - query.start_time > self.agent_system.config.query_timeout * 2
            ]
            
            for query_id in old_queries:
                del self.agent_system.active_queries[query_id]
            
            logger.info("System performance optimization completed")
            
        except Exception as e:
            logger.error(f"Error in performance optimization: {e}")
    
    async def start_conversation(self, context: Optional[Dict[str, Any]] = None, 
                                required_capability: str = "sample_analysis") -> str:
        """Start a new conversation with LIMS-specific context."""
        if not self._initialized or not self.agent_system:
            raise RuntimeError("Service not initialized")
        
        return await self.agent_system.start_conversation(context, required_capability)
    
    async def send_message(self, conversation_id: str, message: str, 
                          user_id: Optional[str] = None) -> Dict[str, Any]:
        """Send a message to an existing conversation."""
        if not self._initialized or not self.agent_system:
            raise RuntimeError("Service not initialized")
        
        # Add user context if provided
        context = {"user_id": user_id} if user_id else None
        
        return await self.agent_system.process_user_input(conversation_id, message, context)
    
    async def query_knowledge_base(self, predicate: str, args: List[str], 
                                  conversation_id: Optional[str] = None) -> List[Dict[str, Any]]:
        """Query the LIMS knowledge base using Prolog reasoning."""
        if not self._initialized or not self.agent_system:
            raise RuntimeError("Service not initialized")
        
        # Create a temporary conversation for system queries if none provided
        if conversation_id is None:
            conv_id = await self.agent_system.start_conversation(
                context={"system_query": True},
                required_capability="logical_reasoning"
            )
        else:
            conv_id = conversation_id
        
        query_id = await self.agent_system.submit_prolog_query(conv_id, predicate, args)
        
        # Wait for query completion
        max_wait = 10.0
        start_time = time.time()
        
        while time.time() - start_time < max_wait:
            query = self.agent_system.active_queries.get(query_id)
            if query and query.state == QueryState.COMPLETED:
                return query.result or []
            await asyncio.sleep(0.1)
        
        return []
    
    async def get_system_status(self) -> Dict[str, Any]:
        """Get comprehensive system status."""
        if not self._initialized or not self.agent_system:
            return {"status": "not_initialized"}
        
        status = await self.agent_system.get_system_status()
        
        # Add LIMS-specific status information
        status.update({
            "lims_agents": {
                agent_id: {
                    "state": agent.state.value,
                    "capabilities": list(agent.capabilities),
                    "load_factor": agent.load_factor,
                    "error_count": agent.error_count
                }
                for agent_id, agent in self.agent_system.dispatcher.agents.items()
            },
            "knowledge_base_size": len(self.agent_system.prolog_engine.knowledge_base),
            "background_tasks": len(self._background_tasks)
        })
        
        return status
    
    async def shutdown(self):
        """Shutdown the enhanced main interface service."""
        try:
            self._initialized = False
            
            # Cancel background tasks
            for task in self._background_tasks:
                task.cancel()
            
            # Wait for tasks to complete
            if self._background_tasks:
                await asyncio.gather(*self._background_tasks, return_exceptions=True)
            
            # Shutdown agent system
            if self.agent_system:
                await self.agent_system.shutdown()
            
            logger.info("Enhanced Main Interface Service shutdown completed")
            
        except Exception as e:
            logger.error(f"Error during shutdown: {e}")
    
    def is_initialized(self) -> bool:
        """Check if the service is properly initialized."""
        return self._initialized and self.agent_system is not None
