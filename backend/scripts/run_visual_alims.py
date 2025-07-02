#!/usr/bin/env python3
"""
ALims Visual System Launcher
Launches the complete visual meta-learning system including:
- Enhanced tray interface
- Web dashboard with real-time updates
- Visual meta-learning backend
- WebSocket communication
"""

import asyncio
import logging
import multiprocessing
import os
import signal
import sys
import threading
import time
import webbrowser
from pathlib import Path

# Add app directory to path
sys.path.insert(0, str(Path(__file__).parent / "app"))

from app.ai.visual_meta_learning import VisualMetaLearningSystem
from app.web.dashboard_server import DashboardServer
from app.system.enhanced_tray import EnhancedAlimsTray

logger = logging.getLogger(__name__)


class VisualALimsLauncher:
    """
    Visual launcher for ALims with enhanced UI and monitoring capabilities.
    
    Features:
    - Real-time system visualization
    - Interactive agent monitoring
    - Pattern evolution display
    - System health dashboard
    """

    def __init__(self):
        self.processes = []
        self.threads = []
        self.running = False

        # Components
        self.meta_learning_system = None
        self.dashboard_server = None
        self.tray_app = None

        # Configuration
        self.dashboard_host = "localhost"
        self.dashboard_port = 8080

        # Set up signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

    def _signal_handler(self, signum, frame):
        """Handle shutdown signals"""
        logger.info(f"Received signal {signum}, shutting down...")
        self.shutdown()
        sys.exit(0)

    def start_meta_learning_system(self):
        """Start the visual meta-learning system"""
        try:
            self.meta_learning_system = VisualMetaLearningSystem()

            # Set up callbacks for real-time updates
            def on_embryo_created(embryo):
                logger.info(f"🥚 New embryo created: {embryo.name}")
                # Could send notification to tray here

            def on_embryo_progress(embryo):
                logger.info(
                    f"🐣 Embryo progress: {embryo.name} -> {embryo.stage.value}"
                )
                # Could update tray status here

            def on_agent_born(agent, embryo):
                logger.info(f"🎉 AGENT BORN! {agent.name}")
                # Could show celebration notification
                self._show_birth_notification(agent)

            def on_training_update(training):
                logger.debug(
                    f"🧠 Training update: {training.agent_name} Epoch {training.epoch}"
                )

            self.meta_learning_system.set_callbacks(
                on_embryo_created=on_embryo_created,
                on_embryo_progress=on_embryo_progress,
                on_agent_born=on_agent_born,
                on_training_update=on_training_update,
            )

            # Start processing
            self.meta_learning_system.start_processing()
            logger.info("✅ Meta-learning system started")

        except Exception as e:
            logger.error(f"Failed to start meta-learning system: {e}")
            raise

    def start_dashboard_server(self):
        """Start the web dashboard server"""
        try:
            self.dashboard_server = DashboardServer(
                host=self.dashboard_host, port=self.dashboard_port
            )

            # Start server in separate thread
            def run_server():
                try:
                    self.dashboard_server.run()
                except Exception as e:
                    logger.error(f"Dashboard server error: {e}")

            server_thread = threading.Thread(target=run_server, daemon=True)
            server_thread.start()
            self.threads.append(server_thread)

            # Wait a moment for server to start
            time.sleep(2)

            logger.info(
                f"✅ Dashboard server started at http://{self.dashboard_host}:{self.dashboard_port}"
            )

        except Exception as e:
            logger.error(f"Failed to start dashboard server: {e}")
            raise

    def start_tray_interface(self):
        """Start the enhanced tray interface"""
        try:
            # Import here to avoid issues on non-macOS systems
            import rumps

            self.tray_app = EnhancedAlimsTray()

            # Add dashboard link to tray menu
            @rumps.clicked("🌐 Open Dashboard")
            def open_dashboard(_):
                webbrowser.open(f"http://{self.dashboard_host}:{self.dashboard_port}")

            # Add the menu item
            self.tray_app.menu.insert(0, "🌐 Open Dashboard")

            logger.info("✅ Tray interface ready")

        except ImportError:
            logger.warning(
                "Tray interface not available (rumps not installed or not on macOS)"
            )
            self.tray_app = None
        except Exception as e:
            logger.error(f"Failed to start tray interface: {e}")
            self.tray_app = None

    def _show_birth_notification(self, agent):
        """Show system notification for agent birth"""
        try:
            if sys.platform == "darwin":  # macOS
                os.system(
                    f"""
                    osascript -e 'display notification "🎉 {agent.name} has been born with {agent.accuracy:.1f}% accuracy!" with title "ALims Agent Birth" sound name "Glass"'
                """
                )
            elif sys.platform == "linux":  # Linux
                os.system(
                    f'notify-send "ALims Agent Birth" "🎉 {agent.name} has been born!"'
                )
            elif sys.platform == "win32":  # Windows
                # Could use plyer or win10toast here
                pass
        except Exception as e:
            logger.error(f"Failed to show birth notification: {e}")

    def open_dashboard_in_browser(self):
        """Open the dashboard in the default browser"""
        try:
            dashboard_url = f"http://{self.dashboard_host}:{self.dashboard_port}"
            webbrowser.open(dashboard_url)
            logger.info(f"🌐 Opened dashboard in browser: {dashboard_url}")
        except Exception as e:
            logger.error(f"Failed to open dashboard in browser: {e}")

    def start_all(self):
        """Start all components of the visual ALims system"""
        self.running = True

        print("🧬 Starting ALims Visual Meta-Learning System...")
        print("=" * 60)

        try:
            # 1. Start meta-learning system
            print("🧠 Starting meta-learning system...")
            self.start_meta_learning_system()

            # 2. Start dashboard server
            print("🌐 Starting web dashboard...")
            self.start_dashboard_server()

            # 3. Start tray interface
            print("🖥️  Starting tray interface...")
            self.start_tray_interface()

            # 4. Open dashboard in browser
            print("🚀 Opening dashboard in browser...")
            time.sleep(1)  # Give server time to fully start
            self.open_dashboard_in_browser()

            print("=" * 60)
            print("✅ ALims Visual System Started Successfully!")
            print()
            print("🎯 What you can do now:")
            print(
                f"   • View dashboard: http://{self.dashboard_host}:{self.dashboard_port}"
            )
            print("   • Check tray menu for quick access")
            print("   • Watch embryos develop in real-time")
            print("   • See agents being born and trained")
            print("   • Monitor meta-learning progress")
            print()
            print("🔥 Cool features to watch:")
            print("   • Real-time embryo development progress")
            print("   • Neural network training visualization")
            print("   • Agent birth celebrations")
            print("   • Pattern discovery and analysis")
            print("   • System intelligence growth")
            print()
            print("Press Ctrl+C to stop the system")
            print("=" * 60)

            # Run tray app if available, otherwise just wait
            if self.tray_app:
                # Run tray app (this blocks)
                self.tray_app.run()
            else:
                # Just keep running
                try:
                    while self.running:
                        time.sleep(1)
                except KeyboardInterrupt:
                    pass

        except Exception as e:
            logger.error(f"Failed to start system: {e}")
            self.shutdown()
            raise

    def shutdown(self):
        """Shutdown all components"""
        if not self.running:
            return

        self.running = False

        print("\n🛑 Shutting down ALims Visual System...")

        try:
            # Stop meta-learning system
            if self.meta_learning_system:
                self.meta_learning_system.stop_processing()
                logger.info("✅ Meta-learning system stopped")

            # Stop dashboard server
            if self.dashboard_server:
                # Dashboard server stops automatically when main thread ends
                logger.info("✅ Dashboard server stopped")

            # Stop tray app
            if self.tray_app:
                try:
                    self.tray_app.quit()
                except:
                    pass
                logger.info("✅ Tray interface stopped")

            # Wait for threads to finish
            for thread in self.threads:
                if thread.is_alive():
                    thread.join(timeout=2)

            print("✅ ALims Visual System shutdown complete")

        except Exception as e:
            logger.error(f"Error during shutdown: {e}")


def check_dependencies():
    """Check if required dependencies are available"""
    missing_deps = []

    try:
        import torch
    except ImportError:
        missing_deps.append("torch")

    try:
        import numpy
    except ImportError:
        missing_deps.append("numpy")

    try:
        import aiohttp
    except ImportError:
        missing_deps.append("aiohttp")

    try:
        import websockets
    except ImportError:
        missing_deps.append("websockets")

    if sys.platform == "darwin":
        try:
            import rumps
        except ImportError:
            print(
                "⚠️  Warning: rumps not installed. Tray interface will not be available."
            )
            print("   Install with: pip install rumps")

    if missing_deps:
        print("❌ Missing required dependencies:")
        for dep in missing_deps:
            print(f"   • {dep}")
        print("\nInstall missing dependencies with:")
        print(f"   pip install {' '.join(missing_deps)}")
        return False

    return True


def main():
    """Main entry point"""

    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        handlers=[logging.StreamHandler(), logging.FileHandler("alims_visual.log")],
    )

    # Check dependencies
    if not check_dependencies():
        sys.exit(1)

    # Create and start launcher
    launcher = VisualALimsLauncher()

    try:
        launcher.start_all()
    except KeyboardInterrupt:
        print("\n🛑 Interrupted by user")
        launcher.shutdown()
    except Exception as e:
        logger.error(f"Fatal error: {e}")
        launcher.shutdown()
        sys.exit(1)


if __name__ == "__main__":
    main()
