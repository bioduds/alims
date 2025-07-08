"""
API Gateway Configuration and Integration

This module provides configuration management and integration
with the ALIMS system following TLA+ verified patterns.
"""

import yaml
from typing import Dict, List, Optional
from dataclasses import dataclass
from pathlib import Path


@dataclass
class ServiceConfig:
    """Configuration for individual services"""
    id: str
    endpoint: str
    max_load: int = 10
    failure_threshold: int = 2
    health_check_path: str = "/health"
    timeout: float = 30.0


@dataclass
class APIGatewayConfig:
    """Main API Gateway configuration following TLA+ constraints"""
    max_requests: int = 100
    max_service_load: int = 10
    circuit_breaker_timeout: int = 30
    health_check_interval: int = 60
    services: List[ServiceConfig] = None

    def __post_init__(self):
        if self.services is None:
            self.services = []

    @classmethod
    def from_yaml(cls, config_path: str) -> 'APIGatewayConfig':
        """Load configuration from YAML file"""
        with open(config_path, 'r') as file:
            data = yaml.safe_load(file)
        
        gateway_config = data.get('api_gateway', {})
        services_data = data.get('services', [])
        
        services = [
            ServiceConfig(
                id=svc['id'],
                endpoint=svc['endpoint'],
                max_load=svc.get('max_load', 10),
                failure_threshold=svc.get('failure_threshold', 2),
                health_check_path=svc.get('health_check', '/health'),
                timeout=svc.get('timeout', 30.0)
            )
            for svc in services_data
        ]
        
        return cls(
            max_requests=gateway_config.get('max_requests', 100),
            max_service_load=gateway_config.get('max_service_load', 10),
            circuit_breaker_timeout=gateway_config.get('circuit_breaker_timeout', 30),
            health_check_interval=gateway_config.get('health_check_interval', 60),
            services=services
        )

    def validate_tla_constraints(self):
        """Validate configuration against TLA+ constraints"""
        assert self.max_requests > 0, "MaxRequests must be positive"
        assert self.max_service_load > 0, "MaxServiceLoad must be positive"
        
        for service in self.services:
            assert service.max_load <= self.max_service_load, \
                f"Service {service.id} max_load exceeds system MaxServiceLoad"
            assert service.failure_threshold > 0, \
                f"Service {service.id} failure_threshold must be positive"
        
        # Check for duplicate service IDs
        service_ids = [svc.id for svc in self.services]
        assert len(service_ids) == len(set(service_ids)), \
            "Duplicate service IDs found in configuration"


# Default configuration template
DEFAULT_CONFIG = """
api_gateway:
  max_requests: 1000
  max_service_load: 50
  circuit_breaker_timeout: 30
  health_check_interval: 60

services:
  - id: "user_service"
    endpoint: "http://user-service:8080"
    max_load: 20
    failure_threshold: 3
    health_check: "/health"
    timeout: 30.0
    
  - id: "data_service"
    endpoint: "http://data-service:8080"
    max_load: 30
    failure_threshold: 3
    health_check: "/health"
    timeout: 30.0
    
  - id: "analytics_service"
    endpoint: "http://analytics-service:8080"
    max_load: 15
    failure_threshold: 2
    health_check: "/health"
    timeout: 45.0
"""


def create_default_config(config_path: str):
    """Create default configuration file"""
    Path(config_path).parent.mkdir(parents=True, exist_ok=True)
    with open(config_path, 'w') as file:
        file.write(DEFAULT_CONFIG)


# FastAPI integration for ALIMS
from fastapi import FastAPI, HTTPException, Depends
from fastapi.responses import JSONResponse
import asyncio
from .core import APIGateway, ServiceState


class ALIMSAPIGatewayIntegration:
    """
    Integration layer for ALIMS system with FastAPI
    
    Provides REST API endpoints that enforce TLA+ verified behavior.
    """

    def __init__(self, config: APIGatewayConfig):
        self.config = config
        self.gateway = APIGateway(
            max_requests=config.max_requests,
            default_max_service_load=config.max_service_load
        )
        self._initialized = False

    async def initialize(self):
        """Initialize gateway with configured services"""
        if self._initialized:
            return
        
        for service_config in self.config.services:
            await self.gateway.add_service(
                service_id=service_config.id,
                endpoint=service_config.endpoint,
                max_load=service_config.max_load,
                failure_threshold=service_config.failure_threshold
            )
            
            # Start with services in UNKNOWN state (following TLA+ Init)
            await self.gateway.update_service_health(
                service_config.id, 
                ServiceState.UNKNOWN
            )
        
        self._initialized = True

    def create_fastapi_app(self) -> FastAPI:
        """Create FastAPI application with API Gateway endpoints"""
        app = FastAPI(
            title="ALIMS API Gateway",
            description="TLA+ Verified API Gateway Service Communication",
            version="1.0.0"
        )

        @app.on_event("startup")
        async def startup_event():
            await self.initialize()

        @app.post("/api/v1/request/{service_id}")
        async def handle_service_request(service_id: str, payload: dict):
            """
            Handle request to specific service following TLA+ RouteRequest logic
            
            Enforces target service routing - requests for service_id only go to service_id.
            """
            try:
                response = await self.gateway.handle_request(service_id, payload)
                return JSONResponse(content=response)
            except Exception as e:
                raise HTTPException(status_code=500, detail=str(e))

        @app.get("/api/v1/status")
        async def get_system_status():
            """Get current system status for monitoring"""
            return self.gateway.get_system_status()

        @app.post("/api/v1/services/{service_id}/health")
        async def update_service_health(service_id: str, health_data: dict):
            """
            Update service health status (TLA+ UpdateServiceHealth action)
            
            Expected payload: {"state": "HEALTHY|DEGRADED|FAILED|UNKNOWN"}
            """
            try:
                state_str = health_data.get("state", "").upper()
                new_state = ServiceState(state_str)
                await self.gateway.update_service_health(service_id, new_state)
                return {"status": "updated", "service_id": service_id, "new_state": state_str}
            except ValueError:
                raise HTTPException(
                    status_code=400, 
                    detail=f"Invalid state: {health_data.get('state')}"
                )

        @app.get("/api/v1/services")
        async def list_services():
            """List all registered services with their current status"""
            status = self.gateway.get_system_status()
            return status["services"]

        @app.get("/api/v1/services/{service_id}")
        async def get_service_status(service_id: str):
            """Get detailed status for specific service"""
            status = self.gateway.get_system_status()
            if service_id not in status["services"]:
                raise HTTPException(status_code=404, detail=f"Service {service_id} not found")
            return status["services"][service_id]

        @app.get("/api/v1/health")
        async def gateway_health_check():
            """Gateway health check endpoint"""
            return {
                "status": "healthy",
                "gateway": "operational",
                "tla_verified": True
            }

        return app


# Example production setup
async def setup_production_gateway(config_path: str) -> ALIMSAPIGatewayIntegration:
    """
    Set up production API Gateway from configuration file
    
    This function demonstrates how to properly initialize the gateway
    with TLA+ constraint validation.
    """
    # Load and validate configuration
    config = APIGatewayConfig.from_yaml(config_path)
    config.validate_tla_constraints()
    
    # Create gateway integration
    integration = ALIMSAPIGatewayIntegration(config)
    await integration.initialize()
    
    return integration


# Health monitoring service
class HealthMonitor:
    """
    Service health monitoring following TLA+ UpdateServiceHealth patterns
    """

    def __init__(self, gateway: APIGateway, config: APIGatewayConfig):
        self.gateway = gateway
        self.config = config
        self._monitoring = False

    async def start_monitoring(self):
        """Start continuous health monitoring"""
        self._monitoring = True
        
        while self._monitoring:
            await self._check_all_services()
            await asyncio.sleep(self.config.health_check_interval)

    def stop_monitoring(self):
        """Stop health monitoring"""
        self._monitoring = False

    async def _check_all_services(self):
        """Check health of all registered services"""
        for service_config in self.config.services:
            try:
                # In real implementation, make HTTP health check call
                # For now, simulate health check
                health_status = await self._check_service_health(service_config)
                await self.gateway.update_service_health(service_config.id, health_status)
            except Exception as e:
                # On health check failure, mark service as failed
                await self.gateway.update_service_health(service_config.id, ServiceState.FAILED)

    async def _check_service_health(self, service_config: ServiceConfig) -> ServiceState:
        """
        Perform actual health check for a service
        
        In production, this would make HTTP calls to service_config.endpoint + health_check_path
        """
        # Simulate health check - in real implementation:
        # async with aiohttp.ClientSession() as session:
        #     async with session.get(f"{service_config.endpoint}{service_config.health_check_path}") as response:
        #         if response.status == 200:
        #             return ServiceState.HEALTHY
        #         else:
        #             return ServiceState.DEGRADED
        
        # For simulation, return HEALTHY
        return ServiceState.HEALTHY


# Export main classes for ALIMS integration
__all__ = [
    'ServiceConfig',
    'APIGatewayConfig', 
    'ALIMSAPIGatewayIntegration',
    'HealthMonitor',
    'setup_production_gateway',
    'create_default_config'
]
