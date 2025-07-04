#!/usr/bin/env python3
"""
ALims Central AI Brain Demo

This script demonstrates the complete Central AI Brain functionality including:
- Natural language interaction
- Command translation and execution
- Multi-agent coordination
- Safety validation
"""

import asyncio
import logging
import sys
import os
from datetime import datetime

# Add the app directory to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "app"))

from ai.central_brain import CentralAIBrain

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


class CentralBrainDemo:
    """Interactive demo of ALims Central AI Brain"""

    def __init__(self):
        self.central_brain = None

    async def setup(self):
        """Initialize the Central AI Brain"""
        try:
            logger.info("🧠 Initializing ALims Central AI Brain...")

            # Configuration
            config = {
                "ai_brain": {
                    "model_name": "gemma3:4b",
                    "base_url": "http://localhost:11434",
                    "context_window": 8192,
                    "max_tokens": 2048,
                    "temperature": 0.7,
                    "timeout": 30,
                },
                "context_management": {
                    "max_conversation_history": 50,
                    "context_refresh_interval": 3600,
                    "memory_persistence": True,
                },
            }

            # Create and start Central AI Brain
            self.central_brain = CentralAIBrain(config)
            await self.central_brain.start()

            logger.info("✅ Central AI Brain is ready!")
            return True

        except Exception as e:
            logger.error(f"❌ Failed to initialize Central AI Brain: {e}")
            return False

    async def demo_chat_interface(self):
        """Demonstrate the chat interface"""
        print("\n" + "=" * 60)
        print("🗣️  CHAT INTERFACE DEMO")
        print("=" * 60)

        test_messages = [
            "Hello! What can you help me with?",
            "What is ALims and how does it work?",
            "Show me the current system status",
            "Can you help me understand the agent system?",
        ]

        for i, message in enumerate(test_messages, 1):
            print(f"\n💬 User: {message}")

            try:
                response = await self.central_brain.chat_with_user_interface_agent(
                    message
                )

                if response.get("success"):
                    print(f"🤖 ALims: {response.get('message', 'No response')}")
                else:
                    print(f"❌ Error: {response.get('error', 'Unknown error')}")

            except Exception as e:
                print(f"❌ Chat error: {e}")

            # Small delay between messages
            await asyncio.sleep(1)

    async def demo_command_processing(self):
        """Demonstrate command translation and processing"""
        print("\n" + "=" * 60)
        print("🧭 COMMAND PROCESSING DEMO")
        print("=" * 60)

        test_commands = [
            "show me system information",
            "help me understand ALims features",
            "create a productivity agent",
            "configure system settings",
        ]

        for i, command in enumerate(test_commands, 1):
            print(f"\n🎯 Command {i}: {command}")

            try:
                # Translate command
                translation = await self.central_brain.translate_user_command(command)

                if translation.get("success"):
                    action = translation["action"]
                    print(f"   📋 Type: {action.intent_analysis.command_type.value}")
                    print(f"   🛡️  Risk: {action.safety_validation.risk_level.value}")
                    print(f"   ⚡ Action: {action.recommended_action.value}")

                    # Process command if safe
                    if action.recommended_action.value == "execute":
                        result = await self.central_brain.process_user_command(command)
                        if result.get("success"):
                            print(f"   ✅ Executed successfully")
                        else:
                            print(
                                f"   ⚠️  Execution result: {result.get('message', 'Unknown')}"
                            )
                    else:
                        print(f"   ⏸️  Requires: {action.recommended_action.value}")

                else:
                    print(f"   ❌ Translation failed: {translation.get('error')}")

            except Exception as e:
                print(f"   ❌ Command error: {e}")

            await asyncio.sleep(0.5)

    async def demo_agent_orchestration(self):
        """Demonstrate multi-agent coordination"""
        print("\n" + "=" * 60)
        print("🎭 AGENT ORCHESTRATION DEMO")
        print("=" * 60)

        complex_tasks = [
            "Analyze system performance and suggest improvements",
            "Coordinate multiple agents to optimize user workflow",
            "Create a comprehensive system health report",
        ]

        for i, task in enumerate(complex_tasks, 1):
            print(f"\n🎯 Complex Task {i}: {task}")

            try:
                result = await self.central_brain.orchestrate_complex_task(task)

                if result.get("success"):
                    print(f"   ✅ Orchestration successful")
                    print(f"   📊 Task ID: {result.get('task_id', 'N/A')}")
                    print(f"   🎭 Agents involved: {result.get('agents_used', 'N/A')}")
                else:
                    print(
                        f"   ❌ Orchestration failed: {result.get('error', 'Unknown')}"
                    )

            except Exception as e:
                print(f"   ❌ Orchestration error: {e}")

            await asyncio.sleep(0.5)

    async def demo_system_status(self):
        """Show current system status and metrics"""
        print("\n" + "=" * 60)
        print("📊 SYSTEM STATUS & METRICS")
        print("=" * 60)

        try:
            # Get health status
            health = await self.central_brain.get_health_status()
            print(f"\n🏥 Health Status:")
            print(
                f"   Central Brain: {'✅ Running' if health.get('central_brain_running') else '❌ Stopped'}"
            )
            print(
                f"   Ollama: {'✅ Healthy' if health.get('ollama_healthy') else '❌ Unhealthy'}"
            )
            print(f"   Model: {health.get('ollama_model', 'Unknown')}")
            print(f"   Interactions: {health.get('interaction_count', 0)}")

            # Get system insights
            insights = await self.central_brain.get_system_insights()
            print(f"\n📈 System Insights:")
            stats = insights.get("interaction_statistics", {})
            print(f"   Total Interactions: {stats.get('total_interactions', 0)}")
            print(f"   Uptime: {stats.get('uptime_hours', 0):.1f} hours")

            # Get agent metrics
            if (
                hasattr(self.central_brain, "system_controller")
                and self.central_brain.system_controller
            ):
                metrics = self.central_brain.system_controller.get_metrics()
                print(f"\n🧭 SystemController Metrics:")
                print(f"   Total Actions: {metrics.get('total_actions', 0)}")
                print(f"   Success Rate: {metrics.get('success_rate', 0):.1%}")
                print(f"   Active Actions: {metrics.get('active_actions', 0)}")
                print(f"   Security Level: {metrics.get('security_level', 'unknown')}")

            # Status summary
            summary = self.central_brain.get_status_summary()
            print(f"\n📋 Status Summary:")
            print(f"   {summary}")

        except Exception as e:
            print(f"❌ Status error: {e}")

    async def run_demo(self):
        """Run the complete demonstration"""
        print("🎉 Welcome to ALims Central AI Brain Demo!")
        print("This demonstration showcases our Phase 2 achievements:")
        print("- Natural Language Interface")
        print("- Intelligent Command Processing")
        print("- Multi-Agent Coordination")
        print("- Safety Validation")
        print("- System Monitoring")

        # Setup
        if not await self.setup():
            print("❌ Demo setup failed!")
            return False

        try:
            # Run all demonstrations
            await self.demo_system_status()
            await self.demo_chat_interface()
            await self.demo_command_processing()
            await self.demo_agent_orchestration()

            print("\n" + "=" * 60)
            print("🎉 DEMO COMPLETE!")
            print("=" * 60)
            print("✅ All Central AI Brain capabilities demonstrated successfully!")
            print("🚀 ALims is ready for intelligent operation!")

            return True

        except Exception as e:
            print(f"❌ Demo failed: {e}")
            return False

        finally:
            # Cleanup
            if self.central_brain:
                await self.central_brain.stop()
                print("🧹 Demo environment cleaned up")


async def main():
    """Main demo execution"""
    demo = CentralBrainDemo()

    try:
        success = await demo.run_demo()
        return 0 if success else 1

    except KeyboardInterrupt:
        print("\n⏹️ Demo interrupted by user")
        return 1
    except Exception as e:
        print(f"\n💥 Demo execution failed: {e}")
        return 1


if __name__ == "__main__":
    print("🧠 Starting ALims Central AI Brain Demo...")
    exit_code = asyncio.run(main())
    sys.exit(exit_code)
