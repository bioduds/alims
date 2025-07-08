# ALIMS System Improvement Plan
*A Strategic Roadmap for Cloud-Ready, Scalable Laboratory Information Management*

## 🎯 Vision & Architecture Principles

### Core Separation of Concerns
1. **Backend**: Pure business logic, data management, PredicateLogic reasoning engine
2. **Frontend/Client**: All AI models, user interface, local processing
3. **Infrastructure**: Containerized services, distributed systems, cloud-native design

### Key Architecture Decisions
- ✅ **AI Models**: Client-side only (Ollama, local LLMs)
- ✅ **PredicateLogic Logic**: Backend only (business rules, workflow validation)
- ✅ **Data Layer**: Centralized with Redis caching
- ✅ **Communication**: REST APIs + WebSocket for real-time
- ✅ **Deployment**: Docker containers with Kubernetes orchestration

---

## 📋 Phase 1: Foundation & Containerization (Weeks 1-4)

### 1.1 Docker Infrastructure Setup

#### Backend Services Container Architecture
```
alims-backend/
├── api-gateway/           # Main API gateway (FastAPI)
├── predicate-logic-engine/         # Pure PredicateLogic reasoning service
├── workflow-manager/      # LIMS workflow orchestration
├── data-service/          # Database operations & business logic
├── notification-service/  # Real-time notifications
└── file-service/          # Document & file management
```

#### Infrastructure Services
```
alims-infrastructure/
├── postgres/              # Primary database
├── redis/                 # Caching & session management
├── vector-db/             # Short-term memory (Qdrant/Weaviate)
├── elasticsearch/         # Centralized logging
├── prometheus/            # Metrics collection
├── grafana/              # Monitoring dashboards
└── nginx/                # Load balancer
```

### 1.2 Docker Compose Development Environment

```yaml
# docker-compose.yml
version: '3.8'
services:
  # Backend Services
  api-gateway:
    build: ./backend/api-gateway
    ports: ["8000:8000"]
    depends_on: [postgres, redis]
    
  predicate-logic-engine:
    build: ./backend/predicate-logic-engine
    ports: ["8001:8001"]
    
  workflow-manager:
    build: ./backend/workflow-manager
    ports: ["8002:8002"]
    
  data-service:
    build: ./backend/data-service
    ports: ["8003:8003"]
    
  # Infrastructure
  postgres:
    image: postgres:15
    environment:
      POSTGRES_DB: alims
      POSTGRES_USER: alims
      POSTGRES_PASSWORD: ${DB_PASSWORD}
    volumes:
      - postgres_data:/var/lib/postgresql/data
      
  redis:
    image: redis:7-alpine
    command: redis-server --appendonly yes
    volumes:
      - redis_data:/data
      
  vector-db:
    image: qdrant/qdrant:latest
    ports: ["6333:6333"]
    volumes:
      - vector_data:/qdrant/storage
      
  elasticsearch:
    image: elasticsearch:8.8.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    volumes:
      - elastic_data:/usr/share/elasticsearch/data
      
  grafana:
    image: grafana/grafana:latest
    ports: ["3001:3000"]
    volumes:
      - grafana_data:/var/lib/grafana
```

### 1.3 Service Separation Tasks

#### 1.3.1 Extract PredicateLogic Engine Service
```bash
# Create dedicated PredicateLogic service
backend/predicate-logic-engine/
├── Dockerfile
├── requirements.txt
├── src/
│   ├── main.py              # FastAPI app
│   ├── predicate_logic_engine.py     # Pure PredicateLogic logic
│   ├── knowledge_base.py    # LIMS rules & facts
│   └── api/
│       ├── rules.py         # Rule management endpoints
│       ├── queries.py       # Query execution endpoints
│       └── validation.py    # Workflow validation
├── tests/
└── config/
```

#### 1.3.2 Extract Data Service
```bash
# Create dedicated data service
backend/data-service/
├── Dockerfile
├── requirements.txt
├── src/
│   ├── main.py              # FastAPI app
│   ├── database.py          # Database connections
│   ├── models/              # Pydantic models
│   ├── repositories/        # Data access layer
│   └── api/
│       ├── samples.py       # Sample management
│       ├── workflows.py     # Workflow data
│       └── reports.py       # Reporting data
├── migrations/              # Database migrations
└── tests/
```

---

## 📋 Phase 2: Vector Database & Memory Management (Weeks 5-6)

### 2.1 Vector Database Implementation

#### Short-Term Memory Architecture
```python
# Vector DB Service for Short-Term Memory
class ShortTermMemoryService:
    """
    Manages conversational context and recent interactions
    - Stores embeddings of recent conversations
    - Provides semantic search for context retrieval
    - Manages session-based memory cleanup
    """
    
    def __init__(self):
        self.qdrant_client = QdrantClient("vector-db", port=6333)
        
    async def store_conversation_context(
        self, 
        conversation_id: str,
        message: str,
        response: str,
        metadata: dict
    ):
        """Store conversation context with embeddings"""
        pass
        
    async def retrieve_relevant_context(
        self, 
        query: str, 
        conversation_id: str,
        limit: int = 5
    ) -> List[ConversationContext]:
        """Retrieve semantically similar contexts"""
        pass
```

#### Vector Database Schema
```python
# Vector collections structure
COLLECTIONS = {
    "conversation_context": {
        "vectors": {
            "size": 384,  # sentence-transformers dimension
            "distance": "Cosine"
        },
        "payload": {
            "conversation_id": "keyword",
            "user_id": "keyword", 
            "timestamp": "datetime",
            "message_type": "keyword",
            "workflow_stage": "keyword"
        }
    },
    "workflow_patterns": {
        "vectors": {"size": 384, "distance": "Cosine"},
        "payload": {
            "pattern_type": "keyword",
            "frequency": "integer",
            "success_rate": "float"
        }
    }
}
```

### 2.2 Memory Management Service

```bash
# Memory management microservice
backend/memory-service/
├── Dockerfile
├── src/
│   ├── main.py              # FastAPI app
│   ├── vector_store.py      # Vector database operations
│   ├── memory_manager.py    # Memory lifecycle management
│   └── api/
│       ├── storage.py       # Store contexts/patterns
│       ├── retrieval.py     # Retrieve relevant contexts
│       └── cleanup.py       # Memory cleanup operations
└── tests/
```

---

## 📋 Phase 3: Centralized Logging & Monitoring (Weeks 7-8)

### 3.1 Centralized Logging Architecture

#### ELK Stack Implementation
```yaml
# Logging infrastructure
logging:
  elasticsearch:
    image: elasticsearch:8.8.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    volumes:
      - elastic_data:/usr/share/elasticsearch/data
      
  logstash:
    image: logstash:8.8.0
    volumes:
      - ./config/logstash:/usr/share/logstash/pipeline
    depends_on: [elasticsearch]
    
  kibana:
    image: kibana:8.8.0
    ports: ["5601:5601"]
    depends_on: [elasticsearch]
    
  filebeat:
    image: elastic/filebeat:8.8.0
    volumes:
      - ./config/filebeat.yml:/usr/share/filebeat/filebeat.yml
      - /var/lib/docker/containers:/var/lib/docker/containers:ro
      - /var/run/docker.sock:/var/run/docker.sock:ro
```

#### Structured Logging Format
```python
# Standardized logging across all services
LOGGING_CONFIG = {
    "version": 1,
    "formatters": {
        "structured": {
            "format": json.dumps({
                "timestamp": "%(asctime)s",
                "level": "%(levelname)s",
                "service": "%(name)s",
                "module": "%(module)s",
                "function": "%(funcName)s",
                "line": "%(lineno)d",
                "message": "%(message)s",
                "correlation_id": "%(correlation_id)s",
                "user_id": "%(user_id)s",
                "conversation_id": "%(conversation_id)s"
            })
        }
    }
}
```

### 3.2 Monitoring & Metrics

#### Prometheus Metrics Collection
```python
# Custom metrics for ALIMS
from prometheus_client import Counter, Histogram, Gauge

# Business metrics
conversation_counter = Counter(
    'alims_conversations_total',
    'Total conversations started',
    ['service', 'user_type']
)

predicate_logic_query_duration = Histogram(
    'alims_predicate_logic_query_duration_seconds',
    'Time spent executing PredicateLogic queries',
    ['query_type', 'result_status']
)

active_workflows = Gauge(
    'alims_active_workflows',
    'Number of active LIMS workflows',
    ['workflow_type', 'priority']
)
```

#### Grafana Dashboards
```bash
# Monitoring dashboards
monitoring/grafana/dashboards/
├── alims-overview.json      # System overview
├── predicate-logic-performance.json  # PredicateLogic engine metrics
├── workflow-analytics.json  # LIMS workflow insights
├── api-performance.json     # API response times
└── resource-usage.json      # Infrastructure metrics
```

---

## 📋 Phase 4: Backend Service Separation (Weeks 9-12)

### 4.1 Microservices Architecture

#### Service Boundary Definition
```bash
# Clean service separation
alims-backend/
├── api-gateway/             # Client communication hub
│   ├── src/
│   │   ├── main.py         # FastAPI gateway
│   │   ├── auth/           # Authentication middleware
│   │   ├── routing/        # Service routing logic
│   │   └── websocket/      # Real-time communication
│   └── Dockerfile
│   
├── predicate-logic-engine/          # Business rules engine
│   ├── src/
│   │   ├── engine.py       # Pure PredicateLogic implementation
│   │   ├── rules/          # LIMS business rules
│   │   ├── validation/     # Workflow validation
│   │   └── api/            # Rule management endpoints
│   └── Dockerfile
│   
├── workflow-service/       # LIMS workflow orchestration
│   ├── src/
│   │   ├── orchestrator.py # Workflow state management
│   │   ├── stages/         # Workflow stage handlers
│   │   ├── transitions/    # State transition logic
│   │   └── api/            # Workflow endpoints
│   └── Dockerfile
│   
├── data-service/          # Data persistence layer
│   ├── src/
│   │   ├── repositories/   # Data access objects
│   │   ├── models/         # Database models
│   │   ├── migrations/     # Schema migrations
│   │   └── api/            # Data endpoints
│   └── Dockerfile
│   
├── notification-service/   # Real-time notifications
│   ├── src/
│   │   ├── publisher.py    # Event publishing
│   │   ├── subscribers/    # Event handlers
│   │   └── websocket/      # Real-time delivery
│   └── Dockerfile
│   
└── file-service/          # Document management
    ├── src/
    │   ├── storage/        # File storage abstraction
    │   ├── processing/     # Document processing
    │   └── api/            # File endpoints
    └── Dockerfile
```

### 4.2 API Gateway Pattern

#### Service Communication
```python
# API Gateway routing configuration
class ServiceRouter:
    """
    Routes client requests to appropriate backend services
    - Handles authentication and authorization
    - Manages service discovery
    - Provides circuit breaker functionality
    - Aggregates responses when needed
    """
    
    ROUTES = {
        "/api/v1/predicate-logic/**": "predicate-logic-engine:8001",
        "/api/v1/workflows/**": "workflow-service:8002", 
        "/api/v1/data/**": "data-service:8003",
        "/api/v1/files/**": "file-service:8004",
        "/api/v1/notifications/**": "notification-service:8005"
    }
```

### 4.3 Data Layer Abstraction

#### Repository Pattern Implementation
```python
# Clean data access layer
class SampleRepository:
    """Pure data operations - no AI logic"""
    
    def __init__(self, db_session, redis_client):
        self.db = db_session
        self.cache = redis_client
        
    async def create_sample(self, sample_data: SampleCreate) -> Sample:
        """Create new sample record"""
        pass
        
    async def get_samples_by_status(self, status: str) -> List[Sample]:
        """Retrieve samples by workflow status"""
        pass
        
    async def update_sample_stage(self, sample_id: str, stage: str) -> Sample:
        """Update sample workflow stage"""
        pass
```

---

## 📋 Phase 5: Cloud Preparation & Kubernetes (Weeks 13-16)

### 5.1 Kubernetes Manifests

#### Deployment Configuration
```yaml
# kubernetes/deployments/predicate-logic-engine.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: predicate-logic-engine
  labels:
    app: predicate-logic-engine
    component: backend
spec:
  replicas: 3
  selector:
    matchLabels:
      app: predicate-logic-engine
  template:
    metadata:
      labels:
        app: predicate-logic-engine
    spec:
      containers:
      - name: predicate-logic-engine
        image: alims/predicate-logic-engine:latest
        ports:
        - containerPort: 8001
        env:
        - name: REDIS_URL
          value: "redis://redis-service:6379"
        - name: LOG_LEVEL
          value: "INFO"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi" 
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8001
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8001
          initialDelaySeconds: 5
          periodSeconds: 5
```

#### Service Discovery
```yaml
# kubernetes/services/
├── api-gateway-service.yaml
├── predicate-logic-engine-service.yaml
├── workflow-service.yaml
├── data-service.yaml
├── redis-service.yaml
└── postgres-service.yaml
```

### 5.2 Cloud-Native Features

#### Helm Charts
```bash
# helm/alims/
├── Chart.yaml
├── values.yaml
├── templates/
│   ├── deployments/
│   ├── services/
│   ├── configmaps/
│   ├── secrets/
│   └── ingress/
└── charts/
    ├── postgresql/
    ├── redis/
    └── elasticsearch/
```

#### Auto-scaling Configuration
```yaml
# kubernetes/hpa/predicate-logic-engine-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: predicate-logic-engine-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: predicate-logic-engine
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

---

## 📋 Phase 6: Redis Integration & Caching (Weeks 17-18)

### 6.1 Redis Architecture

#### Caching Strategy
```python
class CacheManager:
    """
    Multi-layer caching strategy
    - L1: In-memory application cache
    - L2: Redis distributed cache
    - L3: Database persistence
    """
    
    CACHE_CONFIGS = {
        "sessions": {"ttl": 3600, "prefix": "sess:"},
        "workflow_states": {"ttl": 1800, "prefix": "wf:"},
        "predicate_logic_results": {"ttl": 600, "prefix": "pl:"},
        "sample_data": {"ttl": 7200, "prefix": "sample:"}
    }
```

#### Session Management
```python
class SessionManager:
    """Redis-based session management"""
    
    async def create_session(self, user_id: str, metadata: dict) -> str:
        """Create new user session"""
        session_id = generate_session_id()
        session_data = {
            "user_id": user_id,
            "created_at": datetime.utcnow().isoformat(),
            "metadata": metadata
        }
        await self.redis.setex(
            f"session:{session_id}",
            3600,  # 1 hour TTL
            json.dumps(session_data)
        )
        return session_id
```

### 6.2 Distributed State Management

#### Workflow State Caching
```python
class WorkflowStateCache:
    """Cache workflow states for fast access"""
    
    async def cache_workflow_state(
        self, 
        workflow_id: str, 
        state: WorkflowState
    ):
        """Cache current workflow state"""
        cache_key = f"workflow:state:{workflow_id}"
        await self.redis.setex(
            cache_key,
            1800,  # 30 minutes
            state.json()
        )
        
    async def get_cached_state(self, workflow_id: str) -> Optional[WorkflowState]:
        """Retrieve cached workflow state"""
        cache_key = f"workflow:state:{workflow_id}"
        cached_data = await self.redis.get(cache_key)
        if cached_data:
            return WorkflowState.parse_raw(cached_data)
        return None
```

---

## 📋 Phase 7: Client-Side AI Integration (Weeks 19-20)

### 7.1 Client Architecture

#### AI Client Service
```bash
# frontend/ai-client/
├── src/
│   ├── ollama/
│   │   ├── client.ts        # Ollama client wrapper
│   │   ├── models.ts        # Model management
│   │   └── streaming.ts     # Streaming responses
│   ├── embeddings/
│   │   ├── encoder.ts       # Text embedding service
│   │   └── similarity.ts    # Semantic similarity
│   ├── memory/
│   │   ├── context.ts       # Context management
│   │   └── retrieval.ts     # Memory retrieval
│   └── api/
│       ├── chat.ts          # Chat API interface
│       └── inference.ts     # AI inference API
└── package.json
```

#### AI Processing Pipeline
```typescript
// Client-side AI processing
class ClientAIService {
    private ollamaClient: OllamaClient;
    private memoryService: MemoryService;
    
    async processUserMessage(
        message: string,
        conversationId: string
    ): Promise<AIResponse> {
        // 1. Retrieve relevant context from vector DB
        const context = await this.memoryService.getRelevantContext(
            message, 
            conversationId
        );
        
        // 2. Process with local AI model
        const response = await this.ollamaClient.generateResponse({
            message,
            context,
            model: 'llama3.2:latest'
        });
        
        // 3. Store conversation context
        await this.memoryService.storeContext({
            conversationId,
            userMessage: message,
            aiResponse: response,
            timestamp: new Date()
        });
        
        return response;
    }
}
```

### 7.2 Backend Communication Protocol

#### Clear API Boundaries
```typescript
// Backend API client (NO AI processing)
class BackendAPIClient {
    // Pure data operations
    async getSampleData(sampleId: string): Promise<Sample> {
        return this.http.get(`/api/v1/data/samples/${sampleId}`);
    }
    
    // PredicateLogic reasoning queries
    async validateWorkflow(
        workflowId: string, 
        stage: string
    ): Promise<ValidationResult> {
        return this.http.post('/api/v1/predicate-logic/validate', {
            workflow_id: workflowId,
            current_stage: stage
        });
    }
    
    // Workflow state updates
    async updateWorkflowStage(
        workflowId: string, 
        stage: string
    ): Promise<WorkflowState> {
        return this.http.put(`/api/v1/workflows/${workflowId}/stage`, {
            stage
        });
    }
}
```

---

## 🚀 Implementation Timeline

### Quarter 1: Foundation (Weeks 1-12)
- **Weeks 1-4**: Docker containerization
- **Weeks 5-6**: Vector database implementation
- **Weeks 7-8**: Centralized logging & monitoring
- **Weeks 9-12**: Backend service separation

### Quarter 2: Cloud Readiness (Weeks 13-20)
- **Weeks 13-16**: Kubernetes preparation
- **Weeks 17-18**: Redis integration
- **Weeks 19-20**: Client-side AI integration

### Quarter 3: Production Deployment (Weeks 21-24)
- **Weeks 21-22**: Cloud deployment testing
- **Weeks 23-24**: Performance optimization & security hardening

---

## 📊 Success Metrics

### Performance Targets
- **API Response Time**: < 200ms (95th percentile)
- **PredicateLogic Query Time**: < 100ms (average)
- **System Availability**: 99.9% uptime
- **Auto-scaling**: Respond to load within 30 seconds

### Monitoring KPIs
- Service health and availability
- Resource utilization per service
- Request/response patterns
- Error rates and recovery times
- Cache hit ratios
- Database query performance

---

## 🔒 Security Considerations

### Service-to-Service Communication
- mTLS between microservices
- JWT-based authentication
- API rate limiting and throttling
- Input validation and sanitization

### Data Protection
- Encryption at rest and in transit
- GDPR compliance for user data
- Audit logging for compliance
- Regular security scanning

### Network Security
- Service mesh (Istio) for traffic management
- Network policies for service isolation
- VPN access for development environments
- Regular penetration testing

---

## 📈 Scalability Planning

### Horizontal Scaling
- Stateless service design
- Load balancing strategies
- Database sharding considerations
- Cache distribution patterns

### Vertical Scaling
- Resource optimization per service
- Memory and CPU profiling
- Database query optimization
- Cache efficiency improvements

This plan provides a comprehensive roadmap for transforming ALIMS into a modern, scalable, cloud-native system while maintaining clear separation between AI processing (client-side) and business logic (backend).
