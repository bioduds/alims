# 🐳 ALIMS Docker Development Environment

This directory contains the complete Docker-based development environment for ALIMS (Autonomous Laboratory Information Management System) with full microservices architecture.

## 🏗️ **Architecture Overview**

### **Core Services (TLA+ Verified)**
- **API Gateway** (`:8000`) - Central request routing and load balancing
- **Workflow Manager** (`:8002`) - LIMS workflow orchestration with mathematical guarantees
- **PredicateLogic Engine** (`:8001`) - Business rules validation and reasoning

### **Infrastructure Services**
- **PostgreSQL** (`:5432`) - Primary data persistence
- **Redis** (`:6379`) - Caching and session management
- **Qdrant Vector DB** (`:6333`) - Short-term memory and semantic search
- **Elasticsearch** (`:9200`) - Centralized logging and search
- **Nginx** (`:80`) - Load balancer and reverse proxy

### **Monitoring Stack**
- **Prometheus** (`:9090`) - Metrics collection and alerting
- **Grafana** (`:3001`) - Monitoring dashboards and visualization
- **Kibana** (`:5601`) - Log analysis and visualization

## 🚀 **Quick Start**

### **Prerequisites**
- Docker 20.0+ installed
- Docker Compose 2.0+ installed
- At least 8GB RAM available
- At least 10GB disk space

### **Start Development Environment**
```bash
# Start all services
./start-dev.sh

# Or manually with docker-compose
docker-compose up -d
```

### **Stop Environment**
```bash
docker-compose down

# Stop and remove volumes (WARNING: This deletes all data)
docker-compose down -v
```

## 🔧 **Service Configuration**

### **Environment Variables**
Copy `.env.example` to `.env` and customize:

```env
# Database
DB_PASSWORD=your-secure-password
DATABASE_URL=postgresql://alims:password@postgres:5432/alims

# Services
WORKFLOW_SERVICE_URL=http://workflow-manager:8002
PREDICATE_LOGIC_SERVICE_URL=http://predicate-logic-engine:8001

# Monitoring
GRAFANA_PASSWORD=your-grafana-password
```

### **Service Ports**
| Service | Port | Description |
|---------|------|-------------|
| Nginx | 80 | Main entry point |
| API Gateway | 8000 | REST API endpoints |
| PredicateLogic Engine | 8001 | Business rules validation |
| Workflow Manager | 8002 | Workflow orchestration |
| Grafana | 3001 | Monitoring dashboards |
| PostgreSQL | 5432 | Database |
| Redis | 6379 | Cache |
| Kibana | 5601 | Log analysis |
| Prometheus | 9090 | Metrics |
| Vector DB | 6333 | Semantic search |
| Elasticsearch | 9200 | Logging |

## 🧪 **Development Workflow**

### **Running Tests**
```bash
# Test individual service
docker-compose exec workflow-manager python -m pytest

# Test API Gateway
docker-compose exec api-gateway python -m pytest

# Test PredicateLogic Engine
docker-compose exec predicate-logic-engine python -m pytest
```

### **Viewing Logs**
```bash
# View all logs
docker-compose logs -f

# View specific service logs
docker-compose logs -f workflow-manager
docker-compose logs -f api-gateway
docker-compose logs -f predicate-logic-engine
```

### **Accessing Service Shells**
```bash
# Access workflow manager shell
docker-compose exec workflow-manager bash

# Access database shell
docker-compose exec postgres psql -U alims -d alims
```

## 📊 **Monitoring & Debugging**

### **Health Checks**
```bash
# Check all service health
curl http://localhost:8000/health
curl http://localhost:8001/health
curl http://localhost:8002/health
```

### **Grafana Dashboards**
Access Grafana at `http://localhost:3001` (admin/admin) for:
- System overview dashboard
- API performance metrics
- Workflow analytics
- Infrastructure monitoring

### **Prometheus Metrics**
Access Prometheus at `http://localhost:9090` for:
- Custom ALIMS metrics
- Service health metrics
- Infrastructure metrics

### **Log Analysis**
Access Kibana at `http://localhost:5601` for:
- Centralized log analysis
- Error tracking
- Performance analysis

## 🔍 **API Documentation**

### **Interactive API Docs**
- **Main API**: http://localhost:8000/docs
- **Workflow Manager**: http://localhost:8002/docs
- **PredicateLogic Engine**: http://localhost:8001/docs

### **API Endpoints**
```bash
# Workflow operations
GET    /api/v1/workflows/{workflow_id}
POST   /api/v1/workflows/
PUT    /api/v1/workflows/{workflow_id}/transition

# PredicateLogic operations
POST   /api/v1/rules/evaluate
GET    /api/v1/rules/
POST   /api/v1/rules/

# System operations
GET    /health
GET    /metrics
```

## 🗄️ **Database Management**

### **Database Access**
```bash
# Connect to PostgreSQL
docker-compose exec postgres psql -U alims -d alims

# View database schemas
\\dt workflow_manager.*
\\dt predicate_logic.*
\\dt api_gateway.*
```

### **Migrations**
```bash
# Run database migrations
docker-compose exec workflow-manager alembic upgrade head
```

### **Backup & Restore**
```bash
# Backup database
docker-compose exec postgres pg_dump -U alims alims > backup.sql

# Restore database
docker-compose exec -T postgres psql -U alims alims < backup.sql
```

## 🔒 **Security Considerations**

### **Development Security**
- Default passwords are for development only
- Services are accessible on localhost only
- No SSL/TLS in development mode

### **Production Checklist**
- [ ] Change all default passwords
- [ ] Enable SSL/TLS certificates
- [ ] Configure proper firewall rules
- [ ] Enable authentication for all services
- [ ] Set up proper secret management

## 🏗️ **Architecture Patterns**

### **TLA+ Verified Services**
All core services implement TLA+ verified properties:
- **Workflow Manager**: 8 safety properties verified
- **API Gateway**: Circuit breaker and routing properties
- **PredicateLogic Engine**: Rule consistency and evaluation correctness

### **Microservices Communication**
- REST APIs for synchronous communication
- Event-driven architecture for async operations
- Circuit breakers for fault tolerance
- Load balancing for scalability

### **Data Flow**
```
Client Request → Nginx → API Gateway → Service Router → Microservice
                                   ↓
                               Monitoring & Logging
```

## 🚨 **Troubleshooting**

### **Common Issues**

**Services not starting:**
```bash
# Check Docker resources
docker system df
docker system prune

# Check service dependencies
docker-compose ps
docker-compose logs [service_name]
```

**Database connection issues:**
```bash
# Check PostgreSQL status
docker-compose exec postgres pg_isready -U alims

# Reset database
docker-compose down
docker volume rm alims_postgres_data
docker-compose up -d postgres
```

**Memory issues:**
```bash
# Check resource usage
docker stats

# Increase Docker memory limit in Docker Desktop settings
```

### **Performance Tuning**
- Adjust PostgreSQL shared_buffers in production
- Configure Redis memory limits
- Set appropriate JVM heap for Elasticsearch
- Tune Nginx worker processes

## 📈 **Scaling for Production**

### **Horizontal Scaling**
- Use Docker Swarm or Kubernetes
- Load balance multiple service instances
- Implement database read replicas
- Use external Redis cluster

### **Monitoring in Production**
- Set up alerting rules in Prometheus
- Configure log retention policies
- Implement distributed tracing
- Set up automated backups

## 🤝 **Contributing**

### **Development Setup**
1. Clone the repository
2. Copy `.env.example` to `.env`
3. Run `./start-dev.sh`
4. Make your changes
5. Run tests: `docker-compose exec [service] pytest`
6. Submit pull request

### **Adding New Services**
1. Create service directory in `backend/app/`
2. Add Dockerfile
3. Update docker-compose.yml
4. Add health checks
5. Update monitoring configuration

---

## 🎯 **Next Steps**

This Docker environment provides the foundation for:
- **Phase 2**: Vector database integration
- **Phase 3**: Enhanced monitoring and logging
- **Phase 4**: Kubernetes deployment
- **Phase 5**: Cloud-native features

The system is now ready for full development and testing of the ALIMS platform with mathematical guarantees provided by TLA+ verification!
