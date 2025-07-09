#!/bin/bash

# ALIMS Docker Development Environment Startup Script
# This script initializes and starts the complete ALIMS development environment

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}🚀 ALIMS Development Environment Startup${NC}"
echo -e "${BLUE}=======================================${NC}"

# Check if Docker is running
if ! docker info > /dev/null 2>&1; then
    echo -e "${RED}❌ Docker is not running. Please start Docker first.${NC}"
    exit 1
fi

# Check if Docker Compose is available
if ! command -v docker-compose &> /dev/null && ! docker compose version &> /dev/null; then
    echo -e "${RED}❌ Docker Compose is not available. Please install Docker Compose.${NC}"
    exit 1
fi

# Set up environment file
if [ ! -f .env ]; then
    echo -e "${YELLOW}📝 Creating .env file from template...${NC}"
    cp .env.example .env
    echo -e "${GREEN}✅ .env file created. Please customize it if needed.${NC}"
fi

# Create necessary directories
echo -e "${YELLOW}📁 Creating necessary directories...${NC}"
mkdir -p logs
mkdir -p monitoring/grafana/dashboards
mkdir -p nginx/ssl
mkdir -p data/postgres
mkdir -p data/redis
mkdir -p data/elasticsearch

# Build and start services
echo -e "${YELLOW}🔨 Building Docker images...${NC}"
docker-compose build

echo -e "${YELLOW}🚀 Starting ALIMS services...${NC}"
docker-compose up -d

# Wait for services to be ready
echo -e "${YELLOW}⏳ Waiting for services to be ready...${NC}"
sleep 10

# Check service health
echo -e "${YELLOW}🏥 Checking service health...${NC}"

services=(
    "alims-postgres:5432"
    "alims-redis:6379"
    "alims-predicate-logic-engine:8001"
    "alims-workflow-manager:8002"
    "alims-api-gateway:8000"
    "alims-elasticsearch:9200"
    "alims-vector-db:6333"
)

for service in "${services[@]}"; do
    IFS=':' read -r name port <<< "$service"
    if docker exec "$name" nc -z localhost "$port" 2>/dev/null; then
        echo -e "${GREEN}✅ $name is running on port $port${NC}"
    else
        echo -e "${RED}❌ $name is not responding on port $port${NC}"
    fi
done

# Show service URLs
echo -e "${BLUE}🌐 Service URLs:${NC}"
echo -e "${GREEN}API Gateway:${NC} http://localhost:8000"
echo -e "${GREEN}API Documentation:${NC} http://localhost:8000/docs"
echo -e "${GREEN}Workflow Manager:${NC} http://localhost:8002"
echo -e "${GREEN}PredicateLogic Engine:${NC} http://localhost:8001"
echo -e "${GREEN}Grafana:${NC} http://localhost:3001 (admin/admin)"
echo -e "${GREEN}Kibana:${NC} http://localhost:5601"
echo -e "${GREEN}Prometheus:${NC} http://localhost:9090"
echo -e "${GREEN}Vector Database:${NC} http://localhost:6333"

# Show useful commands
echo -e "${BLUE}📋 Useful Commands:${NC}"
echo -e "${YELLOW}View logs:${NC} docker-compose logs -f [service_name]"
echo -e "${YELLOW}Stop services:${NC} docker-compose down"
echo -e "${YELLOW}Restart service:${NC} docker-compose restart [service_name]"
echo -e "${YELLOW}View all services:${NC} docker-compose ps"
echo -e "${YELLOW}Access service shell:${NC} docker-compose exec [service_name] bash"

# Run initial tests
echo -e "${YELLOW}🧪 Running initial health checks...${NC}"
sleep 5

# Test API Gateway
if curl -s -f "http://localhost:8000/health" > /dev/null; then
    echo -e "${GREEN}✅ API Gateway health check passed${NC}"
else
    echo -e "${RED}❌ API Gateway health check failed${NC}"
fi

# Test Workflow Manager
if curl -s -f "http://localhost:8002/health" > /dev/null; then
    echo -e "${GREEN}✅ Workflow Manager health check passed${NC}"
else
    echo -e "${RED}❌ Workflow Manager health check failed${NC}"
fi

# Test PredicateLogic Engine
if curl -s -f "http://localhost:8001/health" > /dev/null; then
    echo -e "${GREEN}✅ PredicateLogic Engine health check passed${NC}"
else
    echo -e "${RED}❌ PredicateLogic Engine health check failed${NC}"
fi

echo -e "${BLUE}🎉 ALIMS Development Environment is ready!${NC}"
echo -e "${GREEN}You can now start developing and testing the ALIMS system.${NC}"
echo -e "${YELLOW}For detailed service information, run: docker-compose ps${NC}"
