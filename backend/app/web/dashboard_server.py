#!/usr/bin/env python3
"""
ALims Dashboard Web Server
Serves the meta-learning dashboard with real-time updates via WebSocket.
"""

import asyncio
import json
import logging
import sqlite3
import threading
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Set

import websockets
from aiohttp import web, WSMsgType
from aiohttp.web import Application, Request, Response, WebSocketResponse
import aiohttp_cors

logger = logging.getLogger(__name__)


class DashboardDataManager:
    """Manages real-time data for the dashboard"""

    def __init__(self):
        self.stats = {
            "events_today": 0,
            "patterns_found": 0,
            "active_embryos": 0,
            "trained_agents": 0,
            "system_iq": 0,
        }

        self.embryos = {
            "DevWorkflow-001": {
                "id": "DevWorkflow-001",
                "name": "DevelopmentWorkflowAgent",
                "status": "training",
                "progress": 0.80,
                "data_collected": 847,
                "data_needed": 1000,
                "confidence": 0.84,
                "eta_minutes": 135,
                "emoji": "🐣",
            },
            "AppState-002": {
                "id": "AppState-002",
                "name": "ApplicationStateAgent",
                "status": "birth_ready",
                "progress": 1.0,
                "data_collected": 1203,
                "data_needed": 1000,
                "confidence": 0.91,
                "eta_minutes": 0,
                "emoji": "🎉",
            },
            "SysMaint-003": {
                "id": "SysMaint-003",
                "name": "SystemMaintenanceAgent",
                "status": "gestation",
                "progress": 0.30,
                "data_collected": 156,
                "data_needed": 500,
                "confidence": 0.67,
                "eta_minutes": 342,
                "emoji": "🥚",
            },
        }

        self.agents = {
            "DevelopmentWorkflowAgent": {
                "name": "DevelopmentWorkflowAgent",
                "status": "active",
                "deployed_days": 2,
                "inferences": 1847,
                "accuracy": 94.2,
                "specialization": "Code Analysis",
            },
            "ApplicationStateAgent": {
                "name": "ApplicationStateAgent",
                "status": "active",
                "deployed_days": 1,
                "inferences": 923,
                "accuracy": 91.7,
                "specialization": "App Optimization",
            },
        }

        self.training_session = {
            "agent_name": "DevelopmentWorkflowAgent",
            "epoch": 47,
            "total_epochs": 100,
            "loss": 0.234,
            "accuracy": 87.3,
            "overfitting_risk": "Low",
            "eta_minutes": 83,
        }

        self.patterns = {
            "intensive_coding": {"confidence": 0.92, "frequency": "3-4/day"},
            "cache_optimization": {"confidence": 0.87, "frequency": "every 6h"},
            "multi_project_workflow": {"confidence": 0.81, "frequency": "continuous"},
        }

        # WebSocket connections
        self.websockets: Set[WebSocketResponse] = set()

        # Start background updates
        self.start_background_updates()

    def start_background_updates(self):
        """Start background thread for data updates"""

        def update_loop():
            while True:
                try:
                    self.update_data()
                    asyncio.run(self.broadcast_updates())
                    time.sleep(5)  # Update every 5 seconds
                except Exception as e:
                    logger.error(f"Update loop error: {e}")
                    time.sleep(10)

        thread = threading.Thread(target=update_loop, daemon=True)
        thread.start()

    def update_data(self):
        """Update dashboard data"""
        try:
            # Update stats from database
            self.update_stats_from_db()

            # Update embryo progress
            self.update_embryo_progress()

            # Update training session
            self.update_training_session()

            # Update agent metrics
            self.update_agent_metrics()

        except Exception as e:
            logger.error(f"Error updating data: {e}")

    def update_stats_from_db(self):
        """Update statistics from events database"""
        try:
            if Path("data/events.db").exists():
                conn = sqlite3.connect("data/events.db")
                cursor = conn.cursor()

                # Events today
                today = datetime.now().strftime("%Y-%m-%d")
                cursor.execute(
                    "SELECT COUNT(*) FROM events WHERE date(datetime(timestamp, 'unixepoch')) = ?",
                    (today,),
                )
                self.stats["events_today"] = cursor.fetchone()[0]

                # Total events for IQ calculation
                cursor.execute("SELECT COUNT(*) FROM events")
                total_events = cursor.fetchone()[0]

                conn.close()

                # Calculate system IQ
                self.stats["system_iq"] = min(
                    1000, int(total_events / 100) + len(self.patterns) * 50
                )
            else:
                # Demo data
                self.stats["events_today"] += 5

            self.stats["patterns_found"] = len(self.patterns)
            self.stats["active_embryos"] = len(
                [e for e in self.embryos.values() if e["status"] != "born"]
            )
            self.stats["trained_agents"] = len(self.agents)

        except Exception as e:
            logger.error(f"Error updating stats from DB: {e}")

    def update_embryo_progress(self):
        """Update embryo development progress"""
        for embryo_id, embryo in self.embryos.items():
            if embryo["status"] != "born":
                # Simulate progress
                progress_increment = 0.01 if embryo["status"] == "training" else 0.005
                embryo["progress"] = min(1.0, embryo["progress"] + progress_increment)

                # Update data collected
                embryo["data_collected"] = int(
                    embryo["progress"] * embryo["data_needed"]
                )

                # Update confidence
                embryo["confidence"] = min(0.95, embryo["progress"] * 0.9 + 0.1)

                # Update ETA
                embryo["eta_minutes"] = max(0, embryo["eta_minutes"] - 1)

                # Update status based on progress
                if embryo["progress"] >= 1.0:
                    embryo["status"] = "birth_ready"
                    embryo["emoji"] = "🎉"
                elif embryo["progress"] >= 0.8:
                    embryo["status"] = "training"
                    embryo["emoji"] = "🐣"
                elif embryo["progress"] >= 0.5:
                    embryo["status"] = "development"
                    embryo["emoji"] = "🐣"
                elif embryo["progress"] >= 0.2:
                    embryo["status"] = "gestation"
                    embryo["emoji"] = "🥚"

    def update_training_session(self):
        """Update training session progress"""
        if self.training_session["epoch"] < self.training_session["total_epochs"]:
            self.training_session["epoch"] += 1

            # Simulate improving metrics
            self.training_session["loss"] = max(
                0.1, self.training_session["loss"] - 0.001
            )
            self.training_session["accuracy"] = min(
                95.0, self.training_session["accuracy"] + 0.1
            )
            self.training_session["eta_minutes"] = max(
                0, self.training_session["eta_minutes"] - 1
            )

    def update_agent_metrics(self):
        """Update agent performance metrics"""
        for agent_name, agent in self.agents.items():
            # Simulate inference activity
            agent["inferences"] += 3

            # Slight accuracy improvements
            if agent["accuracy"] < 95.0:
                agent["accuracy"] = min(95.0, agent["accuracy"] + 0.01)

    async def broadcast_updates(self):
        """Broadcast updates to all connected WebSocket clients"""
        if not self.websockets:
            return

        data = {
            "type": "update",
            "stats": self.stats,
            "embryos": list(self.embryos.values()),
            "agents": list(self.agents.values()),
            "training_session": self.training_session,
            "patterns": self.patterns,
            "timestamp": datetime.now().isoformat(),
        }

        message = json.dumps(data)

        # Send to all connected clients
        disconnected = set()
        for ws in self.websockets:
            try:
                await ws.send_str(message)
            except Exception as e:
                logger.error(f"Error sending to WebSocket: {e}")
                disconnected.add(ws)

        # Remove disconnected clients
        self.websockets -= disconnected

    def add_websocket(self, ws: WebSocketResponse):
        """Add a WebSocket connection"""
        self.websockets.add(ws)

    def remove_websocket(self, ws: WebSocketResponse):
        """Remove a WebSocket connection"""
        self.websockets.discard(ws)

    def get_current_data(self) -> Dict[str, Any]:
        """Get current dashboard data"""
        return {
            "stats": self.stats,
            "embryos": list(self.embryos.values()),
            "agents": list(self.agents.values()),
            "training_session": self.training_session,
            "patterns": self.patterns,
            "timestamp": datetime.now().isoformat(),
        }


class DashboardServer:
    """Web server for the ALims dashboard"""

    def __init__(self, host="localhost", port=8080):
        self.host = host
        self.port = port
        self.data_manager = DashboardDataManager()
        self.app = self.create_app()

    def create_app(self) -> Application:
        """Create the web application"""
        app = web.Application()

        # Add CORS support
        cors = aiohttp_cors.setup(
            app,
            defaults={
                "*": aiohttp_cors.ResourceOptions(
                    allow_credentials=True,
                    expose_headers="*",
                    allow_headers="*",
                    allow_methods="*",
                )
            },
        )

        # Routes
        app.router.add_get("/", self.serve_dashboard)
        app.router.add_get("/api/data", self.get_data)
        app.router.add_get("/ws", self.websocket_handler)

        # Add CORS to all routes
        for route in list(app.router.routes()):
            cors.add(route)

        return app

    async def serve_dashboard(self, request: Request) -> Response:
        """Serve the main dashboard HTML"""
        try:
            dashboard_path = Path(__file__).parent / "dashboard.html"

            if dashboard_path.exists():
                with open(dashboard_path, "r", encoding="utf-8") as f:
                    content = f.read()

                # Inject WebSocket connection code
                ws_code = f"""
                <script>
                    // WebSocket connection for real-time updates
                    const ws = new WebSocket('ws://{self.host}:{self.port}/ws');
                    
                    ws.onmessage = function(event) {{
                        const data = JSON.parse(event.data);
                        if (data.type === 'update') {{
                            updateDashboardFromWebSocket(data);
                        }}
                    }};
                    
                    function updateDashboardFromWebSocket(data) {{
                        // Update stats
                        document.getElementById('events-today').textContent = data.stats.events_today.toLocaleString();
                        document.getElementById('patterns-found').textContent = data.stats.patterns_found;
                        document.getElementById('active-embryos').textContent = data.stats.active_embryos;
                        document.getElementById('trained-agents').textContent = data.stats.trained_agents;
                        document.getElementById('system-iq').textContent = data.stats.system_iq;
                        
                        // Update embryo progress bars
                        data.embryos.forEach((embryo, index) => {{
                            const progressBars = document.querySelectorAll('.progress-fill');
                            if (progressBars[index]) {{
                                progressBars[index].style.width = (embryo.progress * 100) + '%';
                            }}
                        }});
                    }}
                </script>
                """

                # Insert WebSocket code before closing body tag
                content = content.replace("</body>", ws_code + "</body>")

                return web.Response(text=content, content_type="text/html")
            else:
                return web.Response(text="Dashboard not found", status=404)

        except Exception as e:
            logger.error(f"Error serving dashboard: {e}")
            return web.Response(text="Internal server error", status=500)

    async def get_data(self, request: Request) -> Response:
        """API endpoint to get current data"""
        try:
            data = self.data_manager.get_current_data()
            return web.json_response(data)
        except Exception as e:
            logger.error(f"Error getting data: {e}")
            return web.json_response({"error": str(e)}, status=500)

    async def websocket_handler(self, request: Request) -> WebSocketResponse:
        """Handle WebSocket connections"""
        ws = web.WebSocketResponse()
        await ws.prepare(request)

        self.data_manager.add_websocket(ws)
        logger.info("WebSocket client connected")

        try:
            # Send initial data
            initial_data = {"type": "initial", **self.data_manager.get_current_data()}
            await ws.send_str(json.dumps(initial_data))

            # Handle messages
            async for msg in ws:
                if msg.type == WSMsgType.TEXT:
                    try:
                        data = json.loads(msg.data)
                        # Handle client messages if needed
                        logger.info(f"Received WebSocket message: {data}")
                    except json.JSONDecodeError:
                        logger.error(f"Invalid JSON from WebSocket: {msg.data}")
                elif msg.type == WSMsgType.ERROR:
                    logger.error(f"WebSocket error: {ws.exception()}")
                    break

        except Exception as e:
            logger.error(f"WebSocket handler error: {e}")

        finally:
            self.data_manager.remove_websocket(ws)
            logger.info("WebSocket client disconnected")

        return ws

    async def start(self):
        """Start the web server"""
        runner = web.AppRunner(self.app)
        await runner.setup()

        site = web.TCPSite(runner, self.host, self.port)
        await site.start()

        logger.info(f"Dashboard server started at http://{self.host}:{self.port}")
        print(f"🌐 ALims Dashboard: http://{self.host}:{self.port}")

    def run(self):
        """Run the server"""
        asyncio.run(self._run_forever())

    async def _run_forever(self):
        """Run the server forever"""
        await self.start()

        try:
            # Keep the server running
            while True:
                await asyncio.sleep(1)
        except KeyboardInterrupt:
            logger.info("Server stopped by user")


def main():
    """Main entry point"""

    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    # Create and run server
    server = DashboardServer()
    server.run()


if __name__ == "__main__":
    main()
