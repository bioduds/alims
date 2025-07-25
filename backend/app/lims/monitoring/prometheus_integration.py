"""
Prometheus Metrics Integration for ALIMS

Open source metrics collection for LIMS workflows
"""

import time
from typing import Dict, Any
from prometheus_client import Counter, Histogram, Gauge, start_http_server

class PrometheusLIMSMonitor:
    """Prometheus metrics for LIMS workflows"""
    
    def __init__(self):
        # Workflow metrics
        self.workflow_total = Counter(
            'alims_workflow_total',
            'Total number of LIMS workflows',
            ['priority', 'status']
        )
        
        self.workflow_duration = Histogram(
            'alims_workflow_duration_seconds',
            'LIMS workflow execution time',
            ['priority']
        )
        
        self.agent_duration = Histogram(
            'alims_agent_duration_seconds', 
            'Individual agent execution time',
            ['agent_name', 'status']
        )
        
        self.active_workflows = Gauge(
            'alims_active_workflows',
            'Number of currently active workflows'
        )
        
        self.tla_violations = Counter(
            'alims_tla_violations_total',
            'TLA+ property violations',
            ['violation_type']
        )
        
        # Start Prometheus metrics server
        start_http_server(8000)
    
    def record_workflow_start(self, priority: str):
        """Record workflow start"""
        self.active_workflows.inc()
        
    def record_workflow_complete(self, priority: str, success: bool, duration: float):
        """Record workflow completion"""
        status = "success" if success else "failure"
        self.workflow_total.labels(priority=priority, status=status).inc()
        self.workflow_duration.labels(priority=priority).observe(duration)
        self.active_workflows.dec()
    
    def record_agent_execution(self, agent_name: str, success: bool, duration: float):
        """Record agent execution"""
        status = "success" if success else "failure"
        self.agent_duration.labels(agent_name=agent_name, status=status).observe(duration)
    
    def record_tla_violation(self, violation_type: str):
        """Record TLA+ property violation"""
        self.tla_violations.labels(violation_type=violation_type).inc()

# Usage:
monitor = PrometheusLIMSMonitor()

# In workflow:
monitor.record_workflow_start("URGENT")
start_time = time.time()

# ... workflow execution ...

duration = time.time() - start_time
monitor.record_workflow_complete("URGENT", True, duration)
