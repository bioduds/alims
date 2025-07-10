#!/usr/bin/env python3
"""
ALIMS Agent Chat Demo

Demonstrates the integration between the Agent Creator and the LIMS workflow
in a conversational interface that lab technicians would use.
"""

import asyncio
import logging
import json
from datetime import datetime
from typing import Dict, List, Any

from backend.app.core.agent_creator import AgentCreator, AgentBlueprint
from backend.app.lims.agents.sample_reception import sample_reception_agent, receive_sample
from backend.app.lims.agents.sample_accessioning import sample_accessioning_agent, accession_sample
from backend.app.lims.models import Sample, SampleState, Priority
from backend.app.lims.workflows.core_workflow import LIMSWorkflow

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("AgentChatDemo")

class LIMSAgentChatDemo:
    """Demo of human-agent interaction in LIMS workflows"""
    
    def __init__(self):
        self.agent_creator = AgentCreator({
            "model_name": "llama3.2",
            "temperature": 0.7
        })
        self.workflow = LIMSWorkflow()
        self.active_agents = {}
        self.conversations = {}
        
    async def simulate_sample_arrival(self, sample_data: Dict[str, Any]) -> Sample:
        """Simulate a new sample arriving at the lab"""
        print(f"\n🚨 NEW SAMPLE ALERT! 🚨")
        print(f"Sample {sample_data['sample_id']} has arrived at the laboratory")
        print(f"Patient: {sample_data['patient_id']}")
        print(f"Type: {sample_data['sample_type']}")
        print(f"Priority: {sample_data['priority']}")
        print(f"Tests: {', '.join(sample_data['tests_requested'])}")
        
        # Create sample
        sample = Sample(
            sample_id=sample_data['sample_id'],
            patient_id=sample_data['patient_id'],
            state=SampleState.RECEIVED,
            received_at=datetime.now(),
            sample_type=sample_data['sample_type'],
            tests_requested=sample_data['tests_requested'],
            priority=Priority[sample_data['priority']]
        )
        
        print(f"\n📋 Sample officially registered in LIMS")
        print(f"Status: {sample.state.value}")
        
        return sample
        
    async def create_specialized_agent_for_sample(self, sample: Sample) -> AgentBlueprint:
        """Use Agent Creator to generate a specialized agent for this sample"""
        print(f"\n🤖 AGENT CREATOR ANALYZING SAMPLE...")
        
        # Create embryo data based on sample characteristics
        embryo_data = {
            "embryo_id": f"embryo_{sample.sample_id}",
            "specialization_scores": {
                "sample_reception": 0.9 if sample.state == SampleState.RECEIVED else 0.1,
                "sample_accessioning": 0.8,
                "urgent_processing": 0.9 if sample.priority == Priority.STAT else 0.3,
                "routine_processing": 0.7 if sample.priority == Priority.ROUTINE else 0.2,
                "quality_control": 0.6,
                "communication": 0.7
            },
            "patterns_detected": 85,
            "dominant_specialization": "sample_reception",
            "fitness_score": 0.85,
            "sample_context": {
                "priority": sample.priority.value,
                "tests_count": len(sample.tests_requested),
                "complexity": "high" if len(sample.tests_requested) > 3 else "standard"
            }
        }
        
        # Create agent using Agent Creator
        agent_blueprint = await self.agent_creator.create_agent(embryo_data)
        
        if agent_blueprint:
            print(f"✨ AGENT CREATED: {agent_blueprint.name}")
            print(f"   Specialization: {agent_blueprint.specialization}")
            print(f"   Autonomy Level: {agent_blueprint.autonomy_level}")
            print(f"   Confidence Threshold: {agent_blueprint.confidence_threshold:.2f}")
            print(f"   Personality Traits:")
            for trait, value in agent_blueprint.personality_traits.items():
                print(f"     - {trait}: {value:.2f}")
                
        return agent_blueprint
        
    async def start_conversation_with_agent(self, agent_blueprint: AgentBlueprint, sample: Sample):
        """Start a conversation with the created agent"""
        print(f"\n💬 STARTING CONVERSATION WITH {agent_blueprint.name}")
        print("=" * 60)
        
        # Agent introduces itself
        print(f"\n🤖 {agent_blueprint.name}:")
        print(agent_blueprint.introduction_message)
        
        # Create conversation context
        conversation_id = f"conv_{sample.sample_id}_{datetime.now().timestamp()}"
        self.conversations[conversation_id] = {
            "agent": agent_blueprint,
            "sample": sample,
            "messages": []
        }
        
        # Simulate human-agent interaction
        await self.simulate_human_interaction(conversation_id)
        
    async def simulate_human_interaction(self, conversation_id: str):
        """Simulate realistic human-agent interaction scenarios"""
        conversation = self.conversations[conversation_id]
        agent_blueprint = conversation["agent"]
        sample = conversation["sample"]
        
        # Get appropriate LIMS agent
        if "reception" in agent_blueprint.specialization.lower():
            lims_agent_func = receive_sample
        else:
            lims_agent_func = accession_sample
            
        # Scenario 1: Human asks about sample status
        await self.exchange_message(
            conversation_id,
            "👨‍🔬 Lab Technician",
            "Hi! I see this sample just arrived. Can you help me understand what needs to be done?",
            lims_agent,
            sample
        )
        
        # Scenario 2: Human asks for specific action
        await self.exchange_message(
            conversation_id,
            "👨‍🔬 Lab Technician", 
            "The patient information looks correct. Can you generate a barcode for this sample?",
            lims_agent,
            sample
        )
        
        # Scenario 3: Human asks about workflow
        await self.exchange_message(
            conversation_id,
            "👨‍🔬 Lab Technician",
            "What's the next step after we generate the barcode?",
            lims_agent,
            sample
        )
        
        # Scenario 4: Human wants to move sample forward
        await self.exchange_message(
            conversation_id,
            "👨‍🔬 Lab Technician",
            "Everything looks good. Let's move this sample to accessioning.",
            lims_agent,
            sample
        )
        
    async def exchange_message(self, conversation_id: str, sender: str, message: str, lims_agent, sample: Sample):
        """Exchange a message between human and agent"""
        print(f"\n{sender}: {message}")
        
        # Get agent response
        try:
            # Use the function-based approach for LIMS agents
            response = await lims_agent_func(sample, {"user_input": message})
                
            agent_name = self.conversations[conversation_id]["agent"].name
            agent_response = response.get("message", "I understand and I'm here to help!")
            
            print(f"\n🤖 {agent_name}: {agent_response}")
            
            # Show suggested actions if any
            if "suggested_actions" in response and response["suggested_actions"]:
                print(f"\n💡 Suggested actions:")
                for i, action in enumerate(response["suggested_actions"], 1):
                    print(f"   {i}. {action}")
                    
            # Show workflow context
            if "sample" in response:
                updated_sample = response["sample"]
                print(f"\n📊 Workflow Status:")
                print(f"   Current State: {updated_sample.state.value}")
                print(f"   Sample ID: {updated_sample.sample_id}")
                if updated_sample.barcode:
                    print(f"   Barcode: {updated_sample.barcode}")
                    
            # Update sample if changed
            if "sample" in response:
                updated_sample = response["sample"]
                sample.state = updated_sample.state
                if updated_sample.barcode:
                    sample.barcode = updated_sample.barcode
                print(f"\n✅ Sample updated: {sample.state.value}")
                
        except Exception as e:
            print(f"\n⚠️  Agent error: {str(e)}")
            print(f"🤖 {self.conversations[conversation_id]['agent'].name}: I apologize, but I encountered an issue. Let me help you manually process this sample.")
            
        # Store message in conversation
        self.conversations[conversation_id]["messages"].append({
            "sender": sender,
            "message": message,
            "timestamp": datetime.now()
        })
        
    async def demonstrate_agent_creator_workflow(self):
        """Full demonstration of the agent creator workflow"""
        print("🔬 ALIMS AGENT CREATOR & LIMS CHAT DEMONSTRATION")
        print("=" * 60)
        print("This demo shows how lab technicians interact with AI agents")
        print("that are dynamically created by the Agent Creator system.")
        print("\nScenario: New samples arrive and agents help process them")
        
        # Simulate different types of samples
        sample_scenarios = [
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
        
        for i, sample_data in enumerate(sample_scenarios, 1):
            print(f"\n\n🧪 SAMPLE SCENARIO {i}/2")
            print("=" * 40)
            
            # Step 1: Sample arrives
            sample = await self.simulate_sample_arrival(sample_data)
            
            # Step 2: Agent Creator creates specialized agent
            agent_blueprint = await self.create_specialized_agent_for_sample(sample)
            
            if agent_blueprint:
                # Step 3: Human-agent conversation
                await self.start_conversation_with_agent(agent_blueprint, sample)
                
                # Step 4: Show agent creation stats
                print(f"\n📈 AGENT CREATION STATS:")
                stats = self.agent_creator.get_creation_stats()
                print(f"   Total Agents Created: {stats['total_agents']}")
                print(f"   Specializations: {stats.get('specializations', {})}")
                print(f"   Autonomy Levels: {stats.get('autonomy_levels', {})}")
            
            if i < len(sample_scenarios):
                print(f"\n⏳ Next sample arriving in 3 seconds...")
                await asyncio.sleep(3)
                
        print(f"\n\n🎉 DEMONSTRATION COMPLETE!")
        print("This shows how the Agent Creator dynamically generates")
        print("specialized LIMS agents that lab technicians can chat with")
        print("to efficiently process samples through the laboratory workflow.")
        
        # Show final summary
        print(f"\n📊 FINAL SUMMARY:")
        all_agents = self.agent_creator.get_all_agents()
        print(f"   Agents Created: {len(all_agents)}")
        print(f"   Conversations: {len(self.conversations)}")
        print(f"   Total Messages: {sum(len(conv['messages']) for conv in self.conversations.values())}")
        
        for agent in all_agents:
            print(f"\n   🤖 {agent.name}")
            print(f"      Specialization: {agent.specialization}")
            print(f"      Autonomy: {agent.autonomy_level}")
            dominant_traits = sorted(agent.personality_traits.items(), key=lambda x: x[1], reverse=True)[:2]
            print(f"      Key Traits: {', '.join([f'{trait}={value:.2f}' for trait, value in dominant_traits])}")

async def main():
    """Run the demo"""
    demo = LIMSAgentChatDemo()
    await demo.demonstrate_agent_creator_workflow()

if __name__ == "__main__":
    asyncio.run(main())
