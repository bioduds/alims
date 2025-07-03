"""
Sample Reception Agent - PydanticAI Implementatisample_reception_agent = Agent(
    'llama3.2',  # Using Llama 3.2 via Ollama for local tool-calling support

This agent handles the initial reception of samples into the LIMS system,
following the TLA+ verified workflow specification.

Responsibilities:
- Validate incoming sample data
- Assign unique sample IDs
- Create initial sample records
- Transition samples to RECEIVED state
- Generate barcodes if needed
- Validate against business rules
"""

from datetime import datetime
from typing import Optional, Dict, Any, List
from pydantic import BaseModel, Field
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIModel
from pydantic_ai.providers.openai import OpenAIProvider
from pydantic_ai.tools import RunContext

from ..models import Sample, SampleWorkflow, SampleState, LIMSSystemState


class SampleReceptionRequest(BaseModel):
    """Request model for sample reception"""
    barcode: Optional[str] = None  # Auto-generate if not provided
    sample_type: str = Field(..., description="Type of sample (blood, urine, etc.)")
    patient_id: str = Field(..., description="Patient identifier")
    collection_site: str = Field(..., description="Where sample was collected")
    priority: str = Field(default="ROUTINE", description="STAT, URGENT, ROUTINE")
    collection_time: Optional[datetime] = None
    collector_id: Optional[str] = None
    notes: Optional[str] = None


class SampleReceptionResponse(BaseModel):
    """Response model for sample reception"""
    success: bool
    sample_id: int
    barcode: str
    message: str
    # Simplified workflow status fields
    current_state: str = "RECEIVED"
    audit_trail_count: int = 1
    can_proceed: bool = True


class SampleReceptionDeps(BaseModel):
    """Dependencies for sample reception agent"""
    lims_system: LIMSSystemState
    barcode_generator: Optional[Any] = None  # Will implement barcode generation service
    validation_rules: Dict[str, Any] = Field(default_factory=dict)


# Create the Ollama model for Llama 3.2
ollama_model = OpenAIModel(
    model_name='llama3.2',
    provider=OpenAIProvider(base_url='http://localhost:11434/v1', api_key='ollama')
)

# Create the sample reception agent (without tools for now)
sample_reception_agent = Agent(
    ollama_model,  # Using Llama 3.2 via Ollama for local tool-calling support
    output_type=SampleReceptionResponse,
    system_prompt="""
    You are the Sample Reception Agent for the ALIMS Laboratory Information Management System.
    
    Your role is to process incoming sample reception requests following these guidelines:
    
    CORE RESPONSIBILITIES:
    1. Validate all required sample information is present and correct
    2. Create sample records in RECEIVED state
    3. Ensure compliance with laboratory standards
    
    VALIDATION RULES:
    - Patient ID must be valid format (at least 3 characters)
    - Sample type must be from approved list: blood, urine, serum, plasma, tissue, swab
    - Collection site must be specified
    - Priority levels: STAT, URGENT, ROUTINE
    
    TLA+ COMPLIANCE:
    - All samples start in RECEIVED state
    - Sample IDs must be unique (provided in system status)
    - Complete audit trail must be maintained
    
    OUTPUT FORMAT - IMPORTANT:
    You must respond with exactly this JSON structure:
    {
        "success": true,
        "sample_id": [use the provided next_sample_id],
        "barcode": "[generate: TYPE_YYYYMMDD_NNN_PRIORITY like BLD_20250703_001_R]",
        "message": "Sample successfully validated and ready for reception",
        "current_state": "RECEIVED",
        "audit_trail_count": 1,
        "can_proceed": true
    }
    
    For failed validation, set success to false and provide clear error message.
    Always generate a barcode in format: [TYPE]_[YYYYMMDD]_[NNN]_[PRIORITY_CODE]
    Type codes: blood=BLD, urine=URN, serum=SER, plasma=PLS, tissue=TSU, swab=SWB
    Priority codes: STAT=S, URGENT=U, ROUTINE=R
    """,
)

# Hardcoded barcode generation function (simpler than agent tools)
def generate_simple_barcode(sample_type: str, priority: str, sample_count: int) -> str:
    """Generate barcode without agent tool complexity"""
    today = datetime.now().strftime("%Y%m%d")
    
    type_codes = {
        "blood": "BLD", "urine": "URN", "serum": "SER", 
        "plasma": "PLS", "tissue": "TSU", "swab": "SWB"
    }
    priority_codes = {"STAT": "S", "URGENT": "U", "ROUTINE": "R"}
    
    type_code = type_codes.get(sample_type.lower(), "UNK")
    priority_code = priority_codes.get(priority, "R")
    
    return f"{type_code}_{today}_{sample_count:03d}_{priority_code}"


async def receive_sample(request: SampleReceptionRequest, 
                        lims_system: LIMSSystemState) -> SampleReceptionResponse:
    """
    Main entry point for sample reception using PydanticAI agent.
    
    This function orchestrates the sample reception process
    following the TLA+ verified workflow specification.
    """
    
    # Prepare the request context for the agent (simplified)
    agent_request = f"""
    Process this sample reception request:
    
    Sample Type: {request.sample_type}
    Patient ID: {request.patient_id}
    Collection Site: {request.collection_site}
    Priority: {request.priority}
    Provided Barcode: {request.barcode or 'None - needs generation'}
    
    Current system status:
    - Next Sample ID: {lims_system.next_sample_id}
    - Total Samples: {len(lims_system.workflows)}
    - System Capacity: {lims_system.max_samples}
    
    Please validate this request and provide the response format as specified.
    Generate a barcode following the format: TYPE_YYYYMMDD_NNN_PRIORITY
    Use sample_id: {lims_system.next_sample_id}
    """
    
    try:
        # Run the agent (no dependencies needed now)
        print(f"DEBUG: Calling agent with request for {request.sample_type} sample...")
        result = await sample_reception_agent.run(agent_request)
        
        print(f"DEBUG: Agent result success: {result.output.success}")
        print(f"DEBUG: Agent result barcode: '{result.output.barcode}'")
        print(f"DEBUG: Agent result sample_id: {result.output.sample_id}")
        
        # If agent processing was successful, create the actual sample
        if result.output.success:
            # Use the validated data to create the sample
            collection_time = request.collection_time or datetime.now()
            
            # Ensure we have a barcode (fallback if agent didn't generate one)
            barcode = result.output.barcode
            if not barcode or not barcode.strip():
                print("DEBUG: Agent didn't generate barcode, creating fallback...")
                barcode = generate_simple_barcode(request.sample_type, request.priority, lims_system.next_sample_id)
            
            sample_id = lims_system.create_sample(
                barcode=barcode,
                sample_type=request.sample_type,
                patient_id=request.patient_id,
                collection_site=request.collection_site,
                priority=request.priority,
                received_at=collection_time
            )
            
            # Get the created workflow for status
            workflow = lims_system.get_sample(sample_id)
            
            return SampleReceptionResponse(
                success=True,
                sample_id=sample_id,
                barcode=barcode,
                message=f"Sample successfully received with ID {sample_id}",
                current_state="RECEIVED",
                audit_trail_count=len(workflow.audit_trail),
                can_proceed=True
            )
        
        else:
            return result.output
            
    except Exception as e:
        return SampleReceptionResponse(
            success=False,
            sample_id=-1,
            barcode="",
            message=f"Sample reception failed: {str(e)}",
            current_state="ERROR",
            audit_trail_count=0,
            can_proceed=False
        )


# Example usage and testing
if __name__ == "__main__":
    import asyncio
    
    async def test_sample_reception():
        """Test the sample reception agent"""
        lims = LIMSSystemState()
        
        # Test request
        request = SampleReceptionRequest(
            sample_type="blood",
            patient_id="PAT12345",
            collection_site="Main Lab",
            priority="ROUTINE",
            notes="Morning draw for routine labs"
        )
        
        # Process the request
        response = await receive_sample(request, lims)
        
        print(f"Reception Result: {response}")
        print(f"System State: {lims.validate_system_invariants()}")
    
    # Run test
    asyncio.run(test_sample_reception())
