"""
FastAPI Integration for PredicateLogic Engine

Provides REST API endpoints for rule evaluation and fact management
with TLA+ verified safety properties enforced at runtime.
"""

from fastapi import FastAPI
from typing import Dict, List, Optional, Set, Any
from fastapi import APIRouter, HTTPException, Depends, BackgroundTasks
from pydantic import BaseModel, Field
import logging

from core import PredicateLogicEngine, EngineConfiguration
from models import (
    Rule, Fact, Evaluation, RuleState, EvaluationState, FactType,
    ConditionOperator, RuleCondition, RuleAction,
    TLAPropertyViolationError
)

logger = logging.getLogger(__name__)

# Global engine instance (in production, would use dependency injection)
_engine_instance: Optional[PredicateLogicEngine] = None


def get_engine() -> PredicateLogicEngine:
    """Dependency to get the engine instance."""
    global _engine_instance
    if _engine_instance is None:
        config = EngineConfiguration(
            max_facts=10000,
            max_evaluations=1000,
            enable_runtime_validation=True
        )
        _engine_instance = PredicateLogicEngine(config)
    return _engine_instance


# API Models
class CreateRuleRequest(BaseModel):
    id: str = Field(..., min_length=1, description="Unique rule identifier")
    name: str = Field(..., min_length=1, description="Human-readable rule name")
    conditions: List[Dict[str, str]] = Field(default_factory=list)
    actions: List[Dict[str, str]] = Field(default_factory=list)
    priority: int = Field(default=1, ge=1, le=100)


class CreateFactRequest(BaseModel):
    id: str = Field(..., min_length=1, description="Unique fact identifier")
    type: FactType = Field(default=FactType.USER_INPUT)
    attributes: Dict[str, Any] = Field(..., min_size=1)
    confidence: int = Field(default=100, ge=0, le=100)
    source: Optional[str] = None


class EvaluationRequest(BaseModel):
    rule_id: str = Field(..., min_length=1)
    input_facts: Optional[Set[str]] = None


class EvaluationResponse(BaseModel):
    evaluation_id: str
    rule_id: str
    result: Optional[bool] = None
    state: EvaluationState
    duration: Optional[float] = None
    inference_steps: int = 0


class EngineStatusResponse(BaseModel):
    status: str
    rules_count: int
    facts_count: int
    active_evaluations: int
    tla_properties_valid: bool
    uptime_seconds: float


# Create router
router = APIRouter(prefix="/api/v1/predicate-logic", tags=["Predicate Logic Engine"])


@router.post("/rules", response_model=Rule)
async def create_rule(
    request: CreateRuleRequest,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Create a new rule with TLA+ verified safety properties.
    
    The rule is created in DRAFT state and must be explicitly activated.
    """
    try:
        # Convert request to internal models
        conditions = [
            RuleCondition(
                field=cond["field"],
                operator=ConditionOperator(cond["operator"]),
                value=cond["value"]
            )
            for cond in request.conditions
        ]
        
        actions = [
            RuleAction(type=act["type"], parameters=act["parameters"])
            for act in request.actions
        ]
        
        rule = engine.create_rule(
            rule_id=request.id,
            name=request.name,
            conditions=conditions,
            actions=actions,
            priority=request.priority
        )
        
        logger.info(f"Created rule {request.id} via API")
        return rule
    
    except TLAPropertyViolationError as e:
        logger.error(f"TLA+ property violation creating rule {request.id}: {e}")
        raise HTTPException(status_code=400, detail=f"Safety property violation: {e}")
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))
    except Exception as e:
        logger.error(f"Unexpected error creating rule {request.id}: {e}")
        raise HTTPException(status_code=500, detail="Internal server error")


@router.post("/rules/{rule_id}/activate")
async def activate_rule(
    rule_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Activate a rule for evaluation.
    
    Enforces TLA+ verified dependency constraints and state transitions.
    """
    try:
        success = engine.activate_rule(rule_id)
        logger.info(f"Activated rule {rule_id} via API")
        return {"rule_id": rule_id, "activated": success}
    
    except TLAPropertyViolationError as e:
        raise HTTPException(status_code=400, detail=f"Safety property violation: {e}")
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.post("/rules/{rule_id}/deactivate")
async def deactivate_rule(
    rule_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """Deactivate a rule."""
    try:
        success = engine.deactivate_rule(rule_id)
        return {"rule_id": rule_id, "deactivated": success}
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.get("/rules/{rule_id}", response_model=Rule)
async def get_rule(
    rule_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """Get a rule by ID."""
    if rule_id not in engine.state.rules:
        raise HTTPException(status_code=404, detail=f"Rule {rule_id} not found")
    
    return engine.state.rules[rule_id]


@router.get("/rules", response_model=List[Rule])
async def list_rules(
    state: Optional[RuleState] = None,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """List all rules, optionally filtered by state."""
    rules = list(engine.state.rules.values())
    
    if state:
        rules = [r for r in rules if r.state == state]
    
    return rules


@router.post("/facts", response_model=Fact)
async def create_fact(
    request: CreateFactRequest,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Add a fact to working memory with TLA+ verified capacity limits.
    """
    try:
        fact = engine.add_fact(
            fact_id=request.id,
            attributes=request.attributes,
            fact_type=request.type,
            confidence=request.confidence,
            source=request.source
        )
        
        logger.info(f"Added fact {request.id} via API")
        return fact
    
    except TLAPropertyViolationError as e:
        raise HTTPException(status_code=400, detail=f"Safety property violation: {e}")
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.delete("/facts/{fact_id}")
async def remove_fact(
    fact_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """Remove a fact from working memory."""
    try:
        success = engine.remove_fact(fact_id)
        return {"fact_id": fact_id, "removed": success}
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.get("/facts/{fact_id}", response_model=Fact)
async def get_fact(
    fact_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """Get a fact by ID."""
    fact = engine.get_fact(fact_id)
    if not fact:
        raise HTTPException(status_code=404, detail=f"Fact {fact_id} not found")
    
    return fact


@router.get("/facts", response_model=List[Fact])
async def list_facts(
    type: Optional[FactType] = None,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """List all facts, optionally filtered by type."""
    if type:
        return engine.query_facts(type=type)
    
    return list(engine.state.facts.values())


@router.post("/evaluate", response_model=EvaluationResponse)
async def evaluate_rule(
    request: EvaluationRequest,
    background_tasks: BackgroundTasks,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Evaluate a rule with TLA+ verified deterministic behavior.
    
    This endpoint provides synchronous rule evaluation with guaranteed
    deterministic results for the same inputs.
    """
    try:
        start_time = time.time()
        
        # Perform synchronous evaluation
        result = engine.evaluate_rule(
            rule_id=request.rule_id,
            input_facts=request.input_facts
        )
        
        end_time = time.time()
        duration = end_time - start_time
        
        # Create response
        response = EvaluationResponse(
            evaluation_id=f"sync_{int(start_time * 1000000)}",  # Synthetic ID for sync evaluation
            rule_id=request.rule_id,
            result=result,
            state=EvaluationState.COMPLETED,
            duration=duration,
            inference_steps=0  # Would be populated by inference engine
        )
        
        logger.info(f"Evaluated rule {request.rule_id} via API: {result} in {duration:.3f}s")
        return response
    
    except TLAPropertyViolationError as e:
        raise HTTPException(status_code=400, detail=f"Safety property violation: {e}")
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.post("/evaluate/async")
async def request_evaluation(
    request: EvaluationRequest,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Request asynchronous rule evaluation.
    
    Returns evaluation ID for tracking progress.
    """
    try:
        evaluation_id = engine.request_evaluation(
            rule_id=request.rule_id,
            input_facts=request.input_facts
        )
        
        return {"evaluation_id": evaluation_id, "status": "queued"}
    
    except TLAPropertyViolationError as e:
        raise HTTPException(status_code=400, detail=f"Safety property violation: {e}")
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@router.get("/evaluations/{evaluation_id}", response_model=EvaluationResponse)
async def get_evaluation(
    evaluation_id: str,
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """Get evaluation status and results."""
    if evaluation_id in engine.state.active_evaluations:
        evaluation = engine.state.active_evaluations[evaluation_id]
        return EvaluationResponse(
            evaluation_id=evaluation.id,
            rule_id=evaluation.rule_id,
            result=evaluation.result,
            state=evaluation.state,
            duration=evaluation.duration(),
            inference_steps=len(evaluation.inference_chain)
        )
    
    elif evaluation_id in engine.state.evaluation_results:
        # Completed evaluation
        result = engine.state.evaluation_results[evaluation_id]
        return EvaluationResponse(
            evaluation_id=evaluation_id,
            rule_id="completed",  # Would need to store rule_id separately
            result=result,
            state=EvaluationState.COMPLETED,
            duration=None,
            inference_steps=0
        )
    
    else:
        raise HTTPException(status_code=404, detail=f"Evaluation {evaluation_id} not found")


@router.get("/status", response_model=EngineStatusResponse)
async def get_engine_status(
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Get engine status including TLA+ property validation.
    
    This endpoint provides health check and monitoring information.
    """
    import time
    
    try:
        # Validate TLA+ properties
        properties_valid = engine.validate_properties()
        
        summary = engine.get_state_summary()
        
        return EngineStatusResponse(
            status="healthy",
            rules_count=summary["rules"]["total"],
            facts_count=summary["facts"]["total"],
            active_evaluations=summary["evaluations"]["active"],
            tla_properties_valid=properties_valid,
            uptime_seconds=time.time() - engine.state.history[0]["timestamp"] if engine.state.history else 0
        )
    
    except Exception as e:
        logger.error(f"Engine status check failed: {e}")
        return EngineStatusResponse(
            status="unhealthy",
            rules_count=0,
            facts_count=0,
            active_evaluations=0,
            tla_properties_valid=False,
            uptime_seconds=0
        )


@router.post("/validate")
async def validate_properties(
    engine: PredicateLogicEngine = Depends(get_engine)
):
    """
    Explicitly validate all TLA+ properties.
    
    This endpoint allows external monitoring of formal correctness guarantees.
    """
    try:
        valid = engine.validate_properties()
        return {
            "tla_properties_valid": valid,
            "validation_timestamp": time.time(),
            "properties_checked": [
                "TypeInvariant",
                "MemoryBounds", 
                "FactIntegrity",
                "CapacityConstraints"
            ]
        }
    
    except TLAPropertyViolationError as e:
        logger.error(f"TLA+ property validation failed: {e}")
        raise HTTPException(
            status_code=500, 
            detail=f"TLA+ property violation detected: {e}"
        )


# Additional imports for time
import time

# Create FastAPI app

app = FastAPI(
    title="PredicateLogic Engine API",
    description="TLA+ verified predicate logic engine for ALIMS",
    version="1.0.0"
)

# Include the router
app.include_router(router)

# Health check endpoint


@app.get("/health")
async def health_check():
    return {"status": "healthy", "service": "predicate-logic-engine"}

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
