#!/usr/bin/env python3
"""
Interactive demo of Enhanced Main Interface Agent with Prolog reasoning.
This script demonstrates the integration of logical programming into our TLA+ model.
"""

import sys
import os

# Add implementation to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'implementation'))

from main_interface_agent_with_prolog import (
    EnhancedMainInterfaceAgent, RequestType
)

def print_header(title):
    print(f"\n{'='*60}")
    print(f" {title}")
    print(f"{'='*60}")

def print_section(title):
    print(f"\n--- {title} ---")

def main():
    print_header("ALIMS Enhanced Agent with Prolog Integration Demo")
    
    # Initialize the enhanced agent
    print("🔧 Initializing Enhanced Main Interface Agent...")
    agent = EnhancedMainInterfaceAgent()
    agent.initialize()
    
    kb_summary = agent.get_knowledge_base_summary()
    print(f"✅ Agent initialized successfully!")
    print(f"   📚 Knowledge Base: {kb_summary['total_facts']} facts, {kb_summary['total_rules']} rules")
    
    # Start conversation
    conv_id = agent.start_conversation()
    print(f"💬 Started conversation: {conv_id[:8]}...")
    
    print_section("1. Traditional Agent Interactions")
    
    # Traditional sample management
    print("👤 User: I need to register a new sample for protein analysis")
    response = agent.send_message(conv_id, "I need to register a new sample for protein analysis", RequestType.SAMPLE_INQUIRY)
    print(f"🤖 Agent: {response['messages'][-1]['content'][:120]}...")
    print(f"   Source: {response['messages'][-1]['agent_source']}")
    
    # Traditional workflow management
    print("\n👤 User: Start the laboratory workflow process")
    response = agent.send_message(conv_id, "Start the laboratory workflow process", RequestType.WORKFLOW_COMMAND)
    print(f"🤖 Agent: {response['messages'][-1]['content'][:120]}...")
    print(f"   Source: {response['messages'][-1]['agent_source']}")
    
    print_section("2. Logical Reasoning Interactions")
    
    # Logical agent selection
    print("👤 User: Which agent is suitable for sample_inquiry tasks?")
    response = agent.send_message(conv_id, "Which agent is suitable for sample_inquiry?", RequestType.LOGICAL_QUERY)
    print(f"🤖 Agent: {response['messages'][-1]['content'][:200]}...")
    print(f"   🧠 Reasoning Used: {response['reasoning_used']}")
    print(f"   📊 Inference Result: {response['inference_result']}")
    if response['messages'][-1].get('reasoning_chain'):
        print(f"   🔗 Reasoning Steps: {len(response['messages'][-1]['reasoning_chain'])} steps")
    
    # Workflow dependency reasoning
    print("\n👤 User: Explain workflow dependencies in the system")
    response = agent.send_message(conv_id, "What are the workflow dependencies?", RequestType.LOGICAL_QUERY)
    print(f"🤖 Agent: {response['messages'][-1]['content'][:200]}...")
    print(f"   🧠 Reasoning Used: {response['reasoning_used']}")
    
    print_section("3. Dynamic Knowledge Addition")
    
    # Add new knowledge to the system
    print("🔧 Adding new knowledge: priority samples and fast-track processing...")
    
    # Add facts about priority samples
    agent.add_prolog_rule("priority_sample", ["urgent_blood"])
    agent.add_prolog_rule("priority_sample", ["stat_glucose"])
    
    # Add rule for fast-track processing
    agent.add_prolog_rule("needs_fast_track", ["?Sample"], [("priority_sample", ["?Sample"])])
    
    # Add capabilities for priority handling
    agent.add_prolog_rule("has_capability", ["priority_handler", "urgent_processing"])
    agent.add_prolog_rule("suitable_agent", ["?Agent", "urgent_processing"], [("has_capability", ["?Agent", "urgent_processing"])])
    
    print("✅ Knowledge added successfully!")
    
    # Query the new knowledge
    print("\n👤 User: Which samples need fast-track processing?")
    result = agent.query_knowledge_base(conv_id, "needs_fast_track", ["?Sample"])
    if result and result.result == "SUCCESS":
        print(f"🤖 Logical Query Result: {result.result}")
        print(f"   🔍 Solution: {result.solution_bindings.bindings}")
        print(f"   📋 Proof Steps:")
        for i, step in enumerate(result.proof_steps, 1):
            print(f"      {i}. {step}")
    else:
        print(f"🤖 Query failed: {result.result if result else 'No result'}")
    
    print_section("4. Complex Multi-Step Reasoning")
    
    # Add complex domain knowledge
    print("🔧 Adding complex laboratory domain knowledge...")
    
    # Sample types and their requirements
    agent.add_prolog_rule("sample_type", ["BLOOD001", "hematology"])
    agent.add_prolog_rule("sample_type", ["URINE002", "chemistry"])
    agent.add_prolog_rule("sample_type", ["TISSUE003", "pathology"])
    
    # Capability requirements for sample types
    agent.add_prolog_rule("requires_capability", ["hematology", "blood_analysis"])
    agent.add_prolog_rule("requires_capability", ["chemistry", "chemical_analysis"])
    agent.add_prolog_rule("requires_capability", ["pathology", "tissue_analysis"])
    
    # Agent capabilities
    agent.add_prolog_rule("has_capability", ["hematology_analyzer", "blood_analysis"])
    agent.add_prolog_rule("has_capability", ["chemistry_analyzer", "chemical_analysis"])
    agent.add_prolog_rule("has_capability", ["pathology_scanner", "tissue_analysis"])
    
    # Complex rule: which agent can process which sample
    agent.add_prolog_rule(
        "can_process", ["?Sample", "?Agent"],
        [
            ("sample_type", ["?Sample", "?Type"]),
            ("requires_capability", ["?Type", "?Capability"]),
            ("has_capability", ["?Agent", "?Capability"])
        ]
    )
    
    print("✅ Complex domain knowledge added!")
    
    # Query complex reasoning
    print("\n👤 User: Which agent can process sample BLOOD001?")
    result = agent.query_knowledge_base(conv_id, "can_process", ["BLOOD001", "?Agent"])
    if result and result.result == "SUCCESS":
        print(f"🤖 Complex Reasoning Result: {result.result}")
        print(f"   🎯 Found Solution: Sample BLOOD001 can be processed!")
        print(f"   📋 Complete Reasoning Chain:")
        for i, step in enumerate(result.proof_steps, 1):
            print(f"      {i}. {step}")
    else:
        print(f"🤖 Complex reasoning failed: {result.result if result else 'No result'}")
    
    print_section("5. System Knowledge Summary")
    
    final_kb = agent.get_knowledge_base_summary()
    print(f"📚 Final Knowledge Base Statistics:")
    print(f"   Total Facts: {final_kb['total_facts']}")
    print(f"   Total Rules: {final_kb['total_rules']}")
    print(f"   Example Facts: {final_kb['facts'][:3]}")
    print(f"   Example Rules: {final_kb['rules'][:2]}")
    
    messages = agent.get_conversation_messages(conv_id)
    print(f"\n💬 Conversation Summary:")
    print(f"   Total Messages: {len(messages)}")
    reasoning_messages = [m for m in messages if m.get('agent_source') == 'logical_reasoner']
    print(f"   Logical Reasoning Messages: {len(reasoning_messages)}")
    
    print_header("Demo Completed Successfully!")
    print("🎉 The Enhanced Main Interface Agent demonstrates:")
    print("   ✅ Traditional agent orchestration")
    print("   ✅ Prolog-style logical reasoning")
    print("   ✅ Dynamic knowledge base updates")
    print("   ✅ Complex multi-step inference")
    print("   ✅ Explainable reasoning chains")
    print("   ✅ Seamless integration between paradigms")
    
    print(f"\n🔬 Laboratory LIMS System Benefits:")
    print("   • Intelligent agent selection based on logical rules")
    print("   • Automated workflow dependency analysis")
    print("   • Dynamic adaptation to new requirements")
    print("   • Formal verification through TLA+ modeling")
    print("   • Explainable AI for regulatory compliance")

if __name__ == "__main__":
    main()
