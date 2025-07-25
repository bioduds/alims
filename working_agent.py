#!/usr/bin/env python3
"""
WORKING AGENTIC LIMS - No Bullshit Version
===========================================

Actually functional agent that:
1. Uses real LLM reasoning via Ollama
2. Traces everything to Langfuse 
3. Makes real decisions using predicate logic
4. Manages LIMS workflows properly

NO MORE FAKE RESPONSES. NO MORE BROKEN IMPORTS. JUST WORKING CODE.
"""

import asyncio
import httpx
import os
import json
import time
from typing import Dict, Any, List, Optional
from datetime import datetime
from langfuse import Langfuse

# Load environment
from dotenv import load_dotenv
load_dotenv()

class WorkingAgent:
    """An agent that actually fucking works"""
    
    def __init__(self):
        # Initialize Langfuse properly
        self.langfuse = Langfuse(
            public_key=os.getenv('LANGFUSE_PUBLIC_KEY'),
            secret_key=os.getenv('LANGFUSE_SECRET_KEY'),
            host=os.getenv('LANGFUSE_HOST', 'https://us.cloud.langfuse.com')
        )
        
        self.ollama_url = "http://localhost:11434"
        self.client = httpx.AsyncClient(timeout=30.0)
        
        print("🤖 Working Agent initialized with real tracing")
    
    async def think(self, query: str) -> Dict[str, Any]:
        """Actually think using LLM, not fake responses"""
        
        # Start tracing
        trace = self.langfuse.trace(
            name="agent_reasoning",
            metadata={"query": query, "timestamp": datetime.now().isoformat()}
        )
        
        try:
            # Real LLM reasoning
            llm_response = await self._call_ollama(query, trace)
            
            # Real predicate logic evaluation
            logic_result = await self._evaluate_predicates(query, llm_response, trace)
            
            # Real decision making
            decision = await self._make_decision(query, llm_response, logic_result, trace)
            
            trace.update(
                output=decision,
                metadata={"success": True, "reasoning_steps": 3}
            )
            
            return {
                "success": True,
                "query": query,
                "llm_reasoning": llm_response,
                "logic_evaluation": logic_result,
                "decision": decision,
                "trace_id": trace.id
            }
            
        except Exception as e:
            trace.update(
                output={"error": str(e)},
                metadata={"success": False, "error": str(e)}
            )
            raise
    
    async def _call_ollama(self, query: str, trace) -> Dict[str, Any]:
        """Make real LLM call to Ollama"""
        
        span = trace.span(
            name="ollama_llm_call",
            input={"query": query}
        )
        
        try:
            prompt = f"""You are an intelligent LIMS (Laboratory Information Management System) agent.
            
Analyze this query and provide structured reasoning:
Query: {query}

Respond with JSON containing:
- analysis: Your understanding of the request
- sample_type: What type of samples are involved (if any)
- workflow_stage: What stage of lab workflow this relates to
- required_actions: List of actions needed
- priority: HIGH/MEDIUM/LOW
- reasoning: Your step-by-step thinking

Be specific and practical."""

            payload = {
                "model": "llama3.2",
                "messages": [{"role": "user", "content": prompt}],
                "stream": False,
                "options": {
                    "temperature": 0.3,
                    "top_p": 0.9
                }
            }
            
            response = await self.client.post(
                f"{self.ollama_url}/v1/chat/completions",
                json=payload,
                headers={"Content-Type": "application/json"}
            )
            
            if response.status_code != 200:
                raise Exception(f"Ollama API error: {response.status_code} - {response.text}")
            
            result = response.json()
            content = result["choices"][0]["message"]["content"]
            
            # Try to parse as JSON, fallback to text
            try:
                structured_response = json.loads(content)
            except:
                structured_response = {
                    "analysis": content,
                    "sample_type": "unknown",
                    "workflow_stage": "analysis_needed",
                    "required_actions": ["manual_review"],
                    "priority": "MEDIUM",
                    "reasoning": "Raw LLM response parsing failed"
                }
            
            span.update(
                output=structured_response,
                usage={
                    "input_tokens": result.get("usage", {}).get("prompt_tokens", 0),
                    "output_tokens": result.get("usage", {}).get("completion_tokens", 0)
                }
            )
            
            return structured_response
            
        except Exception as e:
            span.update(output={"error": str(e)})
            raise Exception(f"LLM call failed: {e}")
    
    async def _evaluate_predicates(self, query: str, llm_response: Dict[str, Any], trace) -> Dict[str, Any]:
        """Real predicate logic evaluation"""
        
        span = trace.span(
            name="predicate_logic_evaluation",
            input={"query": query, "llm_analysis": llm_response}
        )
        
        try:
            # Define real LIMS predicates
            predicates = {
                "is_sample_request": "sample" in query.lower() or "test" in query.lower(),
                "is_urgent": llm_response.get("priority") == "HIGH" or "urgent" in query.lower(),
                "requires_qc": "quality" in query.lower() or "qc" in query.lower(),
                "is_routine": llm_response.get("priority") == "LOW" and "routine" in query.lower(),
                "needs_approval": llm_response.get("workflow_stage") in ["approval", "review"],
                "has_sample_type": llm_response.get("sample_type") != "unknown"
            }
            
            # Apply logical rules
            rules_fired = []
            
            if predicates["is_sample_request"] and predicates["has_sample_type"]:
                rules_fired.append("sample_processing_workflow")
            
            if predicates["is_urgent"]:
                rules_fired.append("expedite_processing")
            
            if predicates["requires_qc"]:
                rules_fired.append("quality_control_required")
            
            if predicates["needs_approval"]:
                rules_fired.append("approval_workflow")
            
            result = {
                "predicates": predicates,
                "rules_fired": rules_fired,
                "confidence": sum(predicates.values()) / len(predicates),
                "recommendation": self._generate_recommendation(predicates, rules_fired)
            }
            
            span.update(output=result)
            return result
            
        except Exception as e:
            span.update(output={"error": str(e)})
            raise Exception(f"Predicate evaluation failed: {e}")
    
    def _generate_recommendation(self, predicates: Dict[str, bool], rules_fired: List[str]) -> str:
        """Generate actionable recommendations"""
        
        if "expedite_processing" in rules_fired:
            return "URGENT: Fast-track this request through all workflow stages"
        
        if "sample_processing_workflow" in rules_fired:
            return "Route to sample processing workflow with standard timeline"
        
        if "quality_control_required" in rules_fired:
            return "Include QC steps in processing workflow"
        
        if "approval_workflow" in rules_fired:
            return "Send to approval queue for supervisor review"
        
        return "Standard processing recommended"
    
    async def _make_decision(self, query: str, llm_response: Dict[str, Any], logic_result: Dict[str, Any], trace) -> Dict[str, Any]:
        """Make real decisions based on reasoning and logic"""
        
        span = trace.span(
            name="decision_making",
            input={
                "query": query,
                "llm_reasoning": llm_response,
                "logic_evaluation": logic_result
            }
        )
        
        try:
            # Combine LLM reasoning with predicate logic
            confidence = logic_result.get("confidence", 0.5)
            priority = llm_response.get("priority", "MEDIUM")
            recommendation = logic_result.get("recommendation", "Standard processing")
            
            # Make structured decision
            decision = {
                "action": self._determine_action(llm_response, logic_result),
                "priority": priority,
                "workflow": self._determine_workflow(logic_result["rules_fired"]),
                "timeline": self._determine_timeline(priority),
                "next_steps": llm_response.get("required_actions", []),
                "confidence": confidence,
                "reasoning": recommendation
            }
            
            span.update(output=decision)
            return decision
            
        except Exception as e:
            span.update(output={"error": str(e)})
            raise Exception(f"Decision making failed: {e}")
    
    def _determine_action(self, llm_response: Dict[str, Any], logic_result: Dict[str, Any]) -> str:
        """Determine the primary action to take"""
        
        rules = logic_result.get("rules_fired", [])
        
        if "expedite_processing" in rules:
            return "EXPEDITE"
        elif "sample_processing_workflow" in rules:
            return "PROCESS_SAMPLE"
        elif "approval_workflow" in rules:
            return "REQUEST_APPROVAL"
        elif "quality_control_required" in rules:
            return "APPLY_QC"
        else:
            return "STANDARD_PROCESSING"
    
    def _determine_workflow(self, rules_fired: List[str]) -> str:
        """Determine which workflow to use"""
        
        if "expedite_processing" in rules_fired:
            return "urgent_processing"
        elif "sample_processing_workflow" in rules_fired:
            return "standard_sample_workflow"
        elif "approval_workflow" in rules_fired:
            return "approval_workflow"
        else:
            return "general_inquiry_workflow"
    
    def _determine_timeline(self, priority: str) -> str:
        """Determine processing timeline"""
        
        if priority == "HIGH":
            return "2-4 hours"
        elif priority == "MEDIUM":
            return "1-2 days"
        else:
            return "3-5 days"
    
    async def close(self):
        """Clean shutdown"""
        await self.client.aclose()
        self.langfuse.flush()
        print("🔌 Working Agent shut down cleanly")


async def main():
    """Test the working agent"""
    print("🚀 Testing WORKING Agentic LIMS")
    print("=" * 50)
    
    agent = WorkingAgent()
    
    test_queries = [
        "I need to submit a blood sample for urgent toxicology testing",
        "Can you help me track the status of sample ID-12345?",
        "We need to run quality control on the new batch of reagents",
        "Please schedule routine maintenance for the mass spectrometer"
    ]
    
    try:
        for i, query in enumerate(test_queries, 1):
            print(f"\n🧪 Test {i}: {query}")
            print("-" * 30)
            
            result = await agent.think(query)
            
            if result["success"]:
                print(f"✅ SUCCESS - Trace ID: {result['trace_id']}")
                print(f"🧠 LLM Analysis: {result['llm_reasoning'].get('analysis', 'N/A')}")
                print(f"⚡ Logic Result: {result['logic_evaluation']['recommendation']}")
                print(f"🎯 Decision: {result['decision']['action']} via {result['decision']['workflow']}")
                print(f"⏱️  Timeline: {result['decision']['timeline']}")
            else:
                print(f"❌ FAILED: {result}")
        
        print(f"\n🎯 ALL TESTS COMPLETED - Check Langfuse dashboard: {os.getenv('LANGFUSE_HOST')}")
        
    except Exception as e:
        print(f"💥 ERROR: {e}")
    
    finally:
        await agent.close()


if __name__ == "__main__":
    asyncio.run(main())
