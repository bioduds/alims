#!/usr/bin/env python3
"""
Simple ALIMS Agent Chat Demo

Shows the concept of human-agent interaction for LIMS workflows
using the Agent Creator to generate specialized agents.
"""

import asyncio
import logging
from datetime import datetime
from typing import Dict, Any

from backend.app.core.agent_creator import AgentCreator, AgentBlueprint

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("SimpleAgentChatDemo")

class SimpleAgentChatDemo:
    """Simple demo of agent creation and conversation concepts"""
    
    def __init__(self):
        self.agent_creator = AgentCreator({
            "model_name": "llama3.2",
            "temperature": 0.7
        })
        
    def simulate_sample_arrival(self, sample_data: Dict[str, Any]):
        """Simulate a sample arriving at the lab"""
        print(f"\n🚨 NEW SAMPLE ALERT! 🚨")
        print(f"Sample: {sample_data['sample_id']}")
        print(f"Patient: {sample_data['patient_id']}")
        print(f"Type: {sample_data['sample_type']}")
        print(f"Priority: {sample_data['priority']}")
        print(f"Tests: {', '.join(sample_data['tests_requested'])}")
        
    async def create_agent_for_sample(self, sample_data: Dict[str, Any]) -> AgentBlueprint:
        """Create a specialized agent for the sample"""
        print(f"\n🤖 AGENT CREATOR ANALYZING SAMPLE...")
        
        # Create embryo data based on sample characteristics
        embryo_data = {
            "embryo_id": f"embryo_{sample_data['sample_id']}",
            "specialization_scores": {
                "sample_reception": 0.9,
                "sample_accessioning": 0.8,
                "urgent_processing": 0.9 if sample_data['priority'] == "STAT" else 0.3,
                "routine_processing": 0.7 if sample_data['priority'] == "ROUTINE" else 0.2,
                "quality_control": 0.6,
                "communication": 0.8
            },
            "patterns_detected": 85,
            "dominant_specialization": "sample_reception",
            "fitness_score": 0.85,
            "sample_context": {
                "priority": sample_data['priority'],
                "tests_count": len(sample_data['tests_requested']),
                "complexity": "high" if len(sample_data['tests_requested']) > 3 else "standard"
            }
        }
        
        # Create agent using Agent Creator
        agent_blueprint = await self.agent_creator.create_agent(embryo_data)
        
        if agent_blueprint:
            print(f"✨ AGENT CREATED: {agent_blueprint.name}")
            print(f"   Specialization: {agent_blueprint.specialization}")
            print(f"   Autonomy Level: {agent_blueprint.autonomy_level}")
            print(f"   Confidence Threshold: {agent_blueprint.confidence_threshold:.2f}")
            print(f"   Key Personality Traits:")
            
            # Show top 3 personality traits
            sorted_traits = sorted(agent_blueprint.personality_traits.items(), 
                                 key=lambda x: x[1], reverse=True)[:3]
            for trait, value in sorted_traits:
                print(f"     - {trait}: {value:.2f}")
                
        return agent_blueprint
        
    def simulate_conversation(self, agent_blueprint: AgentBlueprint, sample_data: Dict[str, Any]):
        """Simulate a conversation with the created agent"""
        print(f"\n💬 STARTING CONVERSATION WITH {agent_blueprint.name}")
        print("=" * 60)
        
        # Agent introduces itself
        print(f"\n🤖 {agent_blueprint.name}:")
        print(agent_blueprint.introduction_message)
        
        # Simulate human-agent interaction scenarios
        scenarios = [
            {
                "human": "Hi! I see this sample just arrived. Can you help me understand what needs to be done?",
                "agent": f"Absolutely! I can see we have sample {sample_data['sample_id']} from patient {sample_data['patient_id']}. Since this is a {sample_data['priority'].lower()} priority {sample_data['sample_type'].lower()} sample, I recommend we first verify the patient information, then generate a barcode, and finally assign an accession number. Would you like me to walk you through each step?"
            },
            {
                "human": "The patient information looks correct. Can you generate a barcode for this sample?",
                "agent": f"Perfect! I've generated barcode LIM{datetime.now().strftime('%Y%m%d')}001 for sample {sample_data['sample_id']}. The barcode has been linked to the patient record and test orders. Next, we should assign an accession number and move this sample to the accessioning queue. Shall I proceed?"
            },
            {
                "human": "What's the next step after accessioning?",
                "agent": f"Great question! After accessioning, this sample will move to the 'SCHEDULED' state where it will be assigned to specific instruments and technologists based on the requested tests: {', '.join(sample_data['tests_requested'])}. The scheduling system will optimize the workflow based on instrument availability and turnaround time requirements. Would you like me to schedule the tests now?"
            },
            {
                "human": "Everything looks good. Let's move this sample forward in the workflow.",
                "agent": "Excellent! I've successfully processed sample {sample_id} through reception and accessioning. The sample is now in the SCHEDULED state with all tests properly queued. The expected completion time is within our standard turnaround time for {priority} priority samples. I'll continue monitoring this sample and will alert you if any issues arise during testing."
            }
        ]
        
        for i, scenario in enumerate(scenarios, 1):
            print(f"\n👨‍🔬 Lab Technician: {scenario['human']}")
            
            # Personalize agent response based on agent traits
            response = scenario['agent']
            if agent_blueprint.personality_traits.get('friendliness', 0.5) > 0.7:
                response = response.replace("Perfect!", "That's fantastic!")
                response = response.replace("Great question!", "What an excellent question!")
            
            if agent_blueprint.personality_traits.get('precision', 0.5) > 0.8:
                response += " I've documented all steps in the audit trail for compliance."
                
            print(f"\n🤖 {agent_blueprint.name}: {response.format(**sample_data)}")
            
            # Show suggested actions based on agent capabilities
            if i == 1:  # After first exchange
                print(f"\n💡 Suggested Actions:")
                print(f"   1. Verify patient demographics")
                print(f"   2. Generate barcode")
                print(f"   3. Check insurance authorization") 
                print(f"   4. Flag for urgent processing" if sample_data['priority'] == 'STAT' else "   4. Add to routine queue")
                
    async def run_demo(self):
        """Run the complete demo"""
        print("🔬 ALIMS AGENT CREATOR & HUMAN INTERACTION DEMO")
        print("=" * 60)
        print("This demonstrates how the Agent Creator generates specialized")
        print("LIMS agents that lab technicians can chat with to process samples.")
        
        # Sample scenarios
        samples = [
            {
                "sample_id": "STAT2024001",
                "patient_id": "PAT78901",
                "sample_type": "Blood",
                "tests_requested": ["Troponin", "CBC", "BNP"],
                "priority": "STAT"
            },
            {
                "sample_id": "RTN2024002", 
                "patient_id": "PAT78902",
                "sample_type": "Urine",
                "tests_requested": ["Urinalysis", "Culture"],
                "priority": "ROUTINE"
            }
        ]
        
        for i, sample_data in enumerate(samples, 1):
            print(f"\n\n🧪 SCENARIO {i}: {sample_data['priority']} SAMPLE")
            print("=" * 40)
            
            # Step 1: Sample arrives
            self.simulate_sample_arrival(sample_data)
            
            # Step 2: Agent Creator creates specialized agent
            agent_blueprint = await self.create_agent_for_sample(sample_data)
            
            if agent_blueprint:
                # Step 3: Human-agent conversation
                self.simulate_conversation(agent_blueprint, sample_data)
                
            print(f"\n⏳ Processing complete for {sample_data['sample_id']}")
            
        # Final summary
        print(f"\n\n🎉 DEMO COMPLETE!")
        print(f"This showcases how:")
        print(f"• Agent Creator analyzes sample characteristics")
        print(f"• Specialized agents are generated with unique personalities") 
        print(f"• Lab technicians can chat naturally with agents")
        print(f"• Agents guide users through LIMS workflows")
        print(f"• Each agent has domain expertise and personality traits")
        
        stats = self.agent_creator.get_creation_stats()
        print(f"\n📊 AGENT CREATION STATS:")
        print(f"   Total Agents Created: {stats['total_agents']}")
        if stats['total_agents'] > 0:
            print(f"   Specializations: {stats.get('specializations', {})}")
            print(f"   Autonomy Levels: {stats.get('autonomy_levels', {})}")
            
            print(f"\n🤖 CREATED AGENTS:")
            for agent in self.agent_creator.get_all_agents():
                traits = sorted(agent.personality_traits.items(), key=lambda x: x[1], reverse=True)[:2]
                trait_str = ", ".join([f"{t}={v:.2f}" for t, v in traits])
                print(f"   • {agent.name} ({agent.specialization}, {trait_str})")

async def main():
    """Run the demo"""
    demo = SimpleAgentChatDemo()
    await demo.run_demo()

if __name__ == "__main__":
    asyncio.run(main())
