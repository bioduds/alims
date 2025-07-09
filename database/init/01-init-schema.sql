-- ALIMS Database Initialization Script
-- Creates initial database schema for all services

-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pg_trgm";

-- Create schemas for each service
CREATE SCHEMA IF NOT EXISTS workflow_manager;
CREATE SCHEMA IF NOT EXISTS predicate_logic;
CREATE SCHEMA IF NOT EXISTS api_gateway;
CREATE SCHEMA IF NOT EXISTS data_service;

-- Workflow Manager Tables
CREATE TABLE IF NOT EXISTS workflow_manager.workflows (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    workflow_id VARCHAR(255) UNIQUE NOT NULL,
    state VARCHAR(50) NOT NULL,
    version INTEGER NOT NULL DEFAULT 1,
    metadata JSONB,
    in_transition BOOLEAN DEFAULT FALSE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS workflow_manager.workflow_events (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    workflow_id VARCHAR(255) NOT NULL,
    event_type VARCHAR(50) NOT NULL,
    from_state VARCHAR(50),
    to_state VARCHAR(50),
    metadata JSONB,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    FOREIGN KEY (workflow_id) REFERENCES workflow_manager.workflows(workflow_id)
);

-- PredicateLogic Engine Tables
CREATE TABLE IF NOT EXISTS predicate_logic.rules (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    rule_id VARCHAR(255) UNIQUE NOT NULL,
    name VARCHAR(255) NOT NULL,
    conditions JSONB NOT NULL,
    actions JSONB NOT NULL,
    priority INTEGER DEFAULT 0,
    enabled BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS predicate_logic.facts (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    fact_id VARCHAR(255) UNIQUE NOT NULL,
    fact_type VARCHAR(50) NOT NULL,
    value JSONB NOT NULL,
    metadata JSONB,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS predicate_logic.evaluations (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    evaluation_id VARCHAR(255) UNIQUE NOT NULL,
    rule_id VARCHAR(255) NOT NULL,
    context JSONB,
    result BOOLEAN,
    execution_time_ms INTEGER,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    FOREIGN KEY (rule_id) REFERENCES predicate_logic.rules(rule_id)
);

-- API Gateway Tables
CREATE TABLE IF NOT EXISTS api_gateway.requests (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    request_id VARCHAR(255) UNIQUE NOT NULL,
    target_service VARCHAR(100) NOT NULL,
    method VARCHAR(10) NOT NULL,
    path VARCHAR(500) NOT NULL,
    status_code INTEGER,
    response_time_ms INTEGER,
    retry_count INTEGER DEFAULT 0,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    completed_at TIMESTAMP WITH TIME ZONE
);

CREATE TABLE IF NOT EXISTS api_gateway.circuit_breakers (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    service_name VARCHAR(100) UNIQUE NOT NULL,
    state VARCHAR(20) NOT NULL DEFAULT 'CLOSED',
    failure_count INTEGER DEFAULT 0,
    last_failure_at TIMESTAMP WITH TIME ZONE,
    next_attempt_at TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Create indexes for performance
CREATE INDEX IF NOT EXISTS idx_workflows_workflow_id ON workflow_manager.workflows(workflow_id);
CREATE INDEX IF NOT EXISTS idx_workflows_state ON workflow_manager.workflows(state);
CREATE INDEX IF NOT EXISTS idx_workflow_events_workflow_id ON workflow_manager.workflow_events(workflow_id);
CREATE INDEX IF NOT EXISTS idx_workflow_events_created_at ON workflow_manager.workflow_events(created_at);

CREATE INDEX IF NOT EXISTS idx_rules_rule_id ON predicate_logic.rules(rule_id);
CREATE INDEX IF NOT EXISTS idx_rules_enabled ON predicate_logic.rules(enabled);
CREATE INDEX IF NOT EXISTS idx_facts_fact_id ON predicate_logic.facts(fact_id);
CREATE INDEX IF NOT EXISTS idx_facts_fact_type ON predicate_logic.facts(fact_type);
CREATE INDEX IF NOT EXISTS idx_evaluations_rule_id ON predicate_logic.evaluations(rule_id);

CREATE INDEX IF NOT EXISTS idx_requests_request_id ON api_gateway.requests(request_id);
CREATE INDEX IF NOT EXISTS idx_requests_target_service ON api_gateway.requests(target_service);
CREATE INDEX IF NOT EXISTS idx_requests_created_at ON api_gateway.requests(created_at);
CREATE INDEX IF NOT EXISTS idx_circuit_breakers_service_name ON api_gateway.circuit_breakers(service_name);

-- Create updated_at triggers
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = NOW();
    RETURN NEW;
END;
$$ language 'plpgsql';

CREATE TRIGGER update_workflows_updated_at BEFORE UPDATE ON workflow_manager.workflows FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();
CREATE TRIGGER update_rules_updated_at BEFORE UPDATE ON predicate_logic.rules FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();
CREATE TRIGGER update_facts_updated_at BEFORE UPDATE ON predicate_logic.facts FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();
CREATE TRIGGER update_circuit_breakers_updated_at BEFORE UPDATE ON api_gateway.circuit_breakers FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

-- Insert sample data for testing
INSERT INTO workflow_manager.workflows (workflow_id, state, metadata) VALUES
    ('sample-workflow-1', 'CREATED', '{"type": "SAMPLE_PROCESSING", "priority": "HIGH"}'),
    ('sample-workflow-2', 'ACTIVE', '{"type": "QUALITY_CONTROL", "priority": "MEDIUM"}')
ON CONFLICT (workflow_id) DO NOTHING;

INSERT INTO predicate_logic.rules (rule_id, name, conditions, actions, priority) VALUES
    ('sample-validation-rule', 'Sample Validation Rule', 
     '[{"field": "sample_type", "operator": "EQUALS", "value": "BLOOD"}]',
     '[{"type": "VALIDATE", "message": "Blood sample validation passed"}]',
     10),
    ('workflow-transition-rule', 'Workflow Transition Rule',
     '[{"field": "current_state", "operator": "IN", "value": ["CREATED", "ACTIVE"]}]',
     '[{"type": "ALLOW_TRANSITION", "message": "Transition allowed"}]',
     5)
ON CONFLICT (rule_id) DO NOTHING;

INSERT INTO predicate_logic.facts (fact_id, fact_type, value) VALUES
    ('sample-types', 'CONFIGURATION', '{"allowed_types": ["BLOOD", "URINE", "TISSUE"]}'),
    ('workflow-states', 'CONFIGURATION', '{"valid_states": ["CREATED", "ACTIVE", "PAUSED", "COMPLETED", "FAILED", "CANCELLED"]}')
ON CONFLICT (fact_id) DO NOTHING;

INSERT INTO api_gateway.circuit_breakers (service_name, state) VALUES
    ('workflow-manager', 'CLOSED'),
    ('predicate-logic-engine', 'CLOSED')
ON CONFLICT (service_name) DO NOTHING;

-- Log initialization completion
INSERT INTO workflow_manager.workflow_events (workflow_id, event_type, from_state, to_state, metadata) VALUES
    ('sample-workflow-1', 'CREATED', null, 'CREATED', '{"initialized": true}'),
    ('sample-workflow-2', 'CREATED', null, 'CREATED', '{"initialized": true}'),
    ('sample-workflow-2', 'TRANSITION', 'CREATED', 'ACTIVE', '{"initialized": true}')
ON CONFLICT DO NOTHING;
