"""
Sample Accessioning Agent - PydanticAI Implementation

This agent handles the accessioning of received samples in the LIMS system,
following the TLA+ verified workflow specification.

Responsibilities:
- Transition samples from RECEIVED to ACCESSIONED state
- Verify sample integrity and quality
- Assign laboratory accession numbers
- Update sample metadata
- Validate completeness of requisition information
- Flag samples for special handling
"""

from datetime import datetime
from typing import Optional, List
from pydantic import BaseModel, Field
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIModel
from pydantic_ai.providers.openai import OpenAIProvider

from ..models import SampleWorkflow, SampleState, LIMSSystemState


class SampleAccessionRequest(BaseModel):
    """Request model for sample accessioning"""
    sample_id: int = Field(..., description="Sample ID to accession")
    accession_number: Optional[str] = None  # Auto-generate if not provided
    technician_id: str = Field(..., description="ID of technician performing accessioning")
    quality_check_passed: bool = Field(default=True, description="Sample quality assessment")
    volume_received: Optional[float] = None  # mL
    temperature_ok: bool = Field(default=True, description="Temperature within acceptable range")
    container_intact: bool = Field(default=True, description="Container not damaged")
    label_legible: bool = Field(default=True, description="Sample label readable")
    requisition_complete: bool = Field(default=True, description="All required information present")
    special_handling_notes: Optional[str] = None
    notes: Optional[str] = None


class SampleAccessionResponse(BaseModel):
    """Response model for sample accessioning"""
    success: bool
    sample_id: int
    accession_number: str
    message: str
    # Simplified quality assessment fields
    quality_score: int = 5
    quality_passed: bool = True
    # Simplified workflow status fields
    current_state: str = "ACCESSIONED"
    recommended_actions: List[str] = Field(default_factory=list)


# Create the Ollama model for Llama 3.2
ollama_model = OpenAIModel(
    model_name='llama3.2',
    provider=OpenAIProvider(base_url='http://localhost:11434/v1', api_key='ollama')
)

# Create the sample accessioning agent (simplified, no tools)
sample_accessioning_agent = Agent(
    ollama_model,  # Using Llama 3.2 via Ollama for local processing
    output_type=SampleAccessionResponse,
    system_prompt="""
    You are the Sample Accessioning Agent for the ALIMS Laboratory Information Management System.
    
    Your role is to process sample accessioning requests following these guidelines:
    
    CORE RESPONSIBILITIES:
    1. Verify sample quality and integrity
    2. Generate unique accession numbers for laboratory tracking
    3. Validate requisition information
    4. Ensure compliance with laboratory quality standards
    
    TLA+ COMPLIANCE:
    - Only RECEIVED samples can be accessioned
    - Transition to ACCESSIONED state only after processing
    - Maintain complete audit trail
    - Sample IDs remain unique and immutable
    
    OUTPUT FORMAT - IMPORTANT:
    You must respond with exactly this JSON structure:
    {
        "success": true,
        "sample_id": [use the provided sample_id],
        "accession_number": "[generate: LAB-YYYYMMDD-NNNNNN like LAB-20250703-000001]",
        "message": "Sample successfully accessioned",
        "quality_score": 5,
        "quality_passed": true,
        "current_state": "ACCESSIONED",
        "recommended_actions": []
    }
    
    For failed processing, set success to false and provide clear error message.
    Always generate accession_number in format: LAB-[YYYYMMDD]-[NNNNNN]
    Quality score should be 1-5 (5 = excellent, 1 = poor)
    """,
)


def generate_accession_number() -> str:
    """
    Generate unique accession number for sample.
    Simple fallback implementation.
    """
    from datetime import datetime
    import random
    
    date_str = datetime.now().strftime("%Y%m%d")
    # Generate a random 6-digit number for simplicity
    sequence = random.randint(1, 999999)
    return f"LAB-{date_str}-{sequence:06d}"


async def accession_sample(request: SampleAccessionRequest, 
                          lims_system: LIMSSystemState) -> SampleAccessionResponse:
    """
    Main entry point for sample accessioning using PydanticAI agent.
    
    This function orchestrates the intelligent sample accessioning process
    following the TLA+ verified workflow specification.
    """
    
    # Get the sample workflow
    workflow = lims_system.get_sample(request.sample_id)
    if not workflow:
        return SampleAccessionResponse(
            success=False,
            sample_id=request.sample_id,
            accession_number="",
            message=f"Sample {request.sample_id} not found",
            quality_score=0,
            quality_passed=False,
            current_state="ERROR",
            recommended_actions=[]
        )
    
    # Check current state - must be RECEIVED
    if workflow.current_state != SampleState.RECEIVED:
        return SampleAccessionResponse(
            success=False,
            sample_id=request.sample_id,
            accession_number="",
            message=f"Sample must be in RECEIVED state for accessioning. Current state: {workflow.current_state}",
            quality_score=0,
            quality_passed=False,
            current_state=str(workflow.current_state),
            recommended_actions=[]
        )

    # Prepare the request context for the agent
    agent_request = f"""
    Process this sample accessioning request:
    
    Sample ID: {request.sample_id}
    Sample Type: {workflow.sample.sample_type}
    Patient ID: {workflow.sample.patient_id}
    Barcode: {workflow.sample.barcode}
    Priority: {workflow.sample.priority}
    Collection Site: {workflow.sample.collection_site}
    Received At: {workflow.sample.received_at}
    
    Quality Assessment:
    - General Quality Check: {'PASSED' if request.quality_check_passed else 'FAILED'}
    - Volume Received: {request.volume_received or 'Not specified'} mL
    - Temperature OK: {'YES' if request.temperature_ok else 'NO'}
    - Container Intact: {'YES' if request.container_intact else 'NO'}
    - Label Legible: {'YES' if request.label_legible else 'NO'}
    - Requisition Complete: {'YES' if request.requisition_complete else 'NO'}
    
    Technician: {request.technician_id}
    Special Handling Notes: {request.special_handling_notes or 'None'}
    Additional Notes: {request.notes or 'None'}
    Requested Accession Number: {request.accession_number or 'Auto-generate'}
    
    Please perform intelligent accessioning following TLA+ specification compliance,
    including quality assessment, accession number generation, and recommendations.
    """
    
    try:
        # Run the agent (simplified, no deps)
        result = await sample_accessioning_agent.run(agent_request)
        
        if result.output.success:
            # Generate accession number if the agent didn't provide one or provided invalid one
            if not result.output.accession_number or not result.output.accession_number.startswith("LAB-"):
                result.output.accession_number = generate_accession_number()
            
            # Perform the actual state transition
            try:
                lims_system.transition_sample(
                    request.sample_id,
                    SampleState.ACCESSIONED,
                    request.technician_id,
                    f"Accessioned with number {result.output.accession_number}. {request.notes or ''}"
                )
                
                return SampleAccessionResponse(
                    success=True,
                    sample_id=request.sample_id,
                    accession_number=result.output.accession_number,
                    message=f"Sample successfully accessioned with number {result.output.accession_number}",
                    quality_score=result.output.quality_score,
                    quality_passed=result.output.quality_passed,
                    current_state="ACCESSIONED",
                    recommended_actions=result.output.recommended_actions
                )
                
            except ValueError as e:
                return SampleAccessionResponse(
                    success=False,
                    sample_id=request.sample_id,
                    accession_number="",
                    message=f"Failed to transition sample state: {str(e)}",
                    quality_score=0,
                    quality_passed=False,
                    current_state="ERROR",
                    recommended_actions=[]
                )
        else:
            return result.output
            
    except Exception as e:
        return SampleAccessionResponse(
            success=False,
            sample_id=request.sample_id,
            accession_number="",
            message=f"Sample accessioning failed: {str(e)}",
            quality_score=0,
            quality_passed=False,
            current_state="ERROR",
            recommended_actions=[]
        )


# Example usage and testing
if __name__ == "__main__":
    import asyncio
    from .sample_reception import receive_sample, SampleReceptionRequest
    from ..models import LIMSSystemState
    
    async def test_sample_accessioning():
        """Test the complete reception -> accessioning workflow"""
        lims = LIMSSystemState()
        
        # First, receive a sample
        reception_request = SampleReceptionRequest(
            sample_type="blood",
            patient_id="PAT12345",
            collection_site="Main Lab",
            priority="ROUTINE",
            notes="Morning draw for routine labs"
        )
        
        reception_response = await receive_sample(reception_request, lims)
        print(f"Reception Result: {reception_response}")
        
        if reception_response.success:
            # Now accession the sample
            accession_request = SampleAccessionRequest(
                sample_id=reception_response.sample_id,
                technician_id="TECH001",
                quality_check_passed=True,
                volume_received=5.0,
                temperature_ok=True,
                container_intact=True,
                label_legible=True,
                requisition_complete=True,
                notes="Quality check passed, ready for testing"
            )
            
            accession_response = await accession_sample(accession_request, lims)
            print(f"Accessioning Result: {accession_response}")
            print(f"System Invariants: {lims.validate_system_invariants()}")
    
    # Run test
    asyncio.run(test_sample_accessioning())
