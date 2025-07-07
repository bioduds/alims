#!/usr/bin/env python3
"""
Simple test to debug PydanticAI agent with Llama 3.2
"""

import asyncio
from pydantic import BaseModel
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIModel
from pydantic_ai.providers.openai import OpenAIProvider

# Super simple response model
class SimpleResponse(BaseModel):
    success: bool
    sample_id: int
    barcode: str
    message: str

# Create Ollama model
ollama_model = OpenAIModel(
    model_name='llama3.2',
    provider=OpenAIProvider(base_url='http://localhost:11434/v1', api_key='ollama')
)

# Create a minimal agent
simple_agent = Agent(
    ollama_model,
    output_type=SimpleResponse,
    system_prompt="""
    You are a simple sample reception system.
    
    When given a request, respond with JSON containing:
    - success: true
    - sample_id: 1
    - barcode: "BLD20250703001R"
    - message: "Sample received successfully"
    
    Always use exactly this format.
    """
)

async def test_simple_agent():
    """Test the simplest possible agent"""
    print("Testing simple agent...")
    
    request = """
    Process this blood sample:
    - Patient: TEST001
    - Type: blood
    - Priority: ROUTINE
    """
    
    try:
        result = await simple_agent.run(request)
        print(f"Success: {result.output.success}")
        print(f"Sample ID: {result.output.sample_id}")
        print(f"Barcode: {result.output.barcode}")
        print(f"Message: {result.output.message}")
        return result.output.success
    except Exception as e:
        print(f"Error: {e}")
        return False

if __name__ == "__main__":
    success = asyncio.run(test_simple_agent())
    print(f"Agent test {'PASSED' if success else 'FAILED'}")
