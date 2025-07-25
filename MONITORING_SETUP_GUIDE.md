# ALIMS Monitoring Setup Guide

This guide explains how to get API keys and configure monitoring for your ALIMS system.

## 1. Langfuse (Recommended for AI workflows)

### Option A: Langfuse Cloud (Managed)

1. **Get API Keys:**
   - Go to https://cloud.langfuse.com
   - Sign up for a free account
   - Create a new project
   - Go to Settings → API Keys
   - Copy your `Public Key` and `Secret Key`

2. **Set Environment Variables:**
   ```bash
   export LANGFUSE_PUBLIC_KEY="pk-lf-..."
   export LANGFUSE_SECRET_KEY="sk-lf-..."
   export LANGFUSE_HOST="https://cloud.langfuse.com"
   ```

3. **Or create `.env` file:**
   ```bash
   # Create .env file in project root
   echo "LANGFUSE_PUBLIC_KEY=pk-lf-your-public-key" >> .env
   echo "LANGFUSE_SECRET_KEY=sk-lf-your-secret-key" >> .env
   echo "LANGFUSE_HOST=https://cloud.langfuse.com" >> .env
   ```

### Option B: Self-hosted Langfuse (Open Source)

1. **Start Langfuse locally:**
   ```bash
   docker-compose -f docker-compose.langfuse.yml up -d
   ```

2. **Access Langfuse:**
   - Open http://localhost:3000
   - Create an account
   - Create a project
   - Get API keys from Settings

3. **Set environment variables:**
   ```bash
   export LANGFUSE_PUBLIC_KEY="pk-lf-..."
   export LANGFUSE_SECRET_KEY="sk-lf-..."
   export LANGFUSE_HOST="http://localhost:3000"
   ```

## 2. OpenTelemetry + Jaeger (Pure Open Source)

### Setup Jaeger

1. **Start Jaeger:**
   ```bash
   docker run -d --name jaeger \
     -p 16686:16686 \
     -p 14268:14268 \
     jaegertracing/all-in-one:latest
   ```

2. **No API keys needed** - OpenTelemetry is open source
3. **Access Jaeger UI:** http://localhost:16686

### Configuration
```bash
# Optional: Configure Jaeger endpoint
export JAEGER_ENDPOINT="http://localhost:14268/api/traces"
```

## 3. Prometheus + Grafana (Metrics)

### Setup

1. **Start Prometheus + Grafana:**
   ```bash
   docker-compose -f docker-compose.prometheus.yml up -d
   ```

2. **No API keys needed** - Prometheus is open source
3. **Access:**
   - Prometheus: http://localhost:9090
   - Grafana: http://localhost:3001 (admin/admin)

## 4. Configuration Methods

### Method 1: Environment Variables (Recommended)
```bash
# Add to your shell profile (.zshrc, .bashrc)
export LANGFUSE_PUBLIC_KEY="pk-lf-your-key"
export LANGFUSE_SECRET_KEY="sk-lf-your-secret"
export LANGFUSE_HOST="https://cloud.langfuse.com"
```

### Method 2: .env file
```bash
# Create .env in project root
cat > .env << EOF
LANGFUSE_PUBLIC_KEY=pk-lf-your-public-key
LANGFUSE_SECRET_KEY=sk-lf-your-secret-key
LANGFUSE_HOST=https://cloud.langfuse.com
EOF
```

### Method 3: Direct in code (not recommended for production)
```python
# In your Python code
monitor = LangfuseLIMSMonitor(
    public_key="pk-lf-your-key",
    secret_key="sk-lf-your-secret",
    host="https://cloud.langfuse.com"
)
```

## 5. Verification

### Test Langfuse Connection
```bash
cd /Users/capanema/Projects/alims
python demos/quick_langfuse_test.py
```

### Test OpenTelemetry
```bash
cd /Users/capanema/Projects/alims
python -c "
from backend.app.lims.monitoring.opentelemetry_integration import OpenTelemetryLIMSMonitor
monitor = OpenTelemetryLIMSMonitor()
print('OpenTelemetry configured successfully')
"
```

## 6. Quick Start Commands

### Start everything:
```bash
# Terminal 1: Start monitoring services
docker-compose -f docker-compose.langfuse.yml up -d

# Terminal 2: Set environment variables
export LANGFUSE_PUBLIC_KEY="your-key"
export LANGFUSE_SECRET_KEY="your-secret"

# Terminal 3: Run ALIMS
./start-dev.sh
```

### View monitoring:
- **Langfuse:** http://localhost:3000 (self-hosted) or https://cloud.langfuse.com
- **Jaeger:** http://localhost:16686
- **Grafana:** http://localhost:3001

## 7. Free Tier Limits

### Langfuse Cloud (Free)
- 50,000 observations/month
- 1 project
- 1 user
- Perfect for development and small production

### Self-hosted (Unlimited)
- No limits
- Your infrastructure
- Full control

Choose based on your needs:
- **Development:** Langfuse Cloud (free)
- **Production:** Self-hosted or Langfuse Cloud Pro
- **Open Source Only:** OpenTelemetry + Jaeger
