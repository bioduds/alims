#!/usr/bin/env python3
"""
ALIMS Real-Time Debug Dashboard
Web-based debugging interface for monitoring agent interactions in real-time
"""

import asyncio
import json
from datetime import datetime, timedelta
from typing import Any, Dict, List
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException
from fastapi.responses import HTMLResponse
from fastapi.staticfiles import StaticFiles

from .debug_system import get_debug_tracer, DebugLevel

class DebugDashboard:
    """Real-time debugging dashboard"""
    
    def __init__(self):
        self.app = FastAPI(title="ALIMS Debug Dashboard", version="1.0.0")
        self.connected_websockets: List[WebSocket] = []
        self.setup_routes()
        
    def setup_routes(self):
        """Setup FastAPI routes for dashboard"""
        
        @self.app.get("/")
        async def dashboard_home():
            return HTMLResponse(self.get_dashboard_html())
        
        @self.app.get("/api/debug/status")
        async def get_debug_status():
            """Get overall system debug status"""
            tracer = get_debug_tracer()
            
            # Calculate recent activity
            recent_events = [
                event for event in tracer.trace_events
                if datetime.fromisoformat(event.timestamp) > datetime.now() - timedelta(minutes=10)
            ]
            
            return {
                "timestamp": datetime.now().isoformat(),
                "total_events": len(tracer.trace_events),
                "recent_events": len(recent_events),
                "active_conversations": len(tracer.active_conversations),
                "tracked_agents": len(tracer.agent_states),
                "agent_states": tracer.agent_states,
                "performance_metrics": tracer.get_performance_summary()
            }
        
        @self.app.get("/api/debug/conversations")
        async def get_active_conversations():
            """Get list of active conversations"""
            tracer = get_debug_tracer()
            
            conversations = []
            for conv_id, events in tracer.active_conversations.items():
                if events:
                    last_event = events[-1]
                    conversations.append({
                        "conversation_id": conv_id,
                        "event_count": len(events),
                        "last_activity": last_event.timestamp,
                        "agents_involved": list(set(event.agent_id for event in events))
                    })
            
            return {"conversations": conversations}
        
        @self.app.get("/api/debug/conversation/{conversation_id}")
        async def get_conversation_debug(conversation_id: str):
            """Get debug trace for specific conversation"""
            tracer = get_debug_tracer()
            return tracer.export_trace_data(conversation_id=conversation_id)
        
        @self.app.get("/api/debug/agents")
        async def get_agent_status():
            """Get status of all tracked agents"""
            tracer = get_debug_tracer()
            
            agents = []
            for agent_id, state in tracer.agent_states.items():
                # Find recent events for this agent
                recent_events = [
                    event for event in tracer.trace_events
                    if event.agent_id == agent_id and 
                    datetime.fromisoformat(event.timestamp) > datetime.now() - timedelta(minutes=5)
                ]
                
                agents.append({
                    "agent_id": agent_id,
                    "current_state": state,
                    "recent_activity": len(recent_events),
                    "last_seen": recent_events[-1].timestamp if recent_events else None
                })
            
            return {"agents": agents}
        
        @self.app.get("/api/debug/events/recent")
        async def get_recent_events(limit: int = 50):
            """Get recent debug events"""
            tracer = get_debug_tracer()
            
            recent_events = sorted(
                tracer.trace_events,
                key=lambda x: x.timestamp,
                reverse=True
            )[:limit]
            
            return {
                "events": [event.to_dict() for event in recent_events]
            }
        
        @self.app.websocket("/ws/debug")
        async def websocket_debug_stream(websocket: WebSocket):
            """WebSocket for real-time debug events"""
            await websocket.accept()
            self.connected_websockets.append(websocket)
            
            try:
                while True:
                    # Keep connection alive and send periodic updates
                    await asyncio.sleep(1)
                    
                    # Send recent events every 2 seconds
                    if len(self.connected_websockets) > 0:
                        await self.broadcast_recent_events()
                        
            except WebSocketDisconnect:
                self.connected_websockets.remove(websocket)
    
    async def broadcast_recent_events(self):
        """Broadcast recent events to all connected WebSocket clients"""
        tracer = get_debug_tracer()
        
        # Get events from last 5 seconds
        recent_events = [
            event for event in tracer.trace_events
            if datetime.fromisoformat(event.timestamp) > datetime.now() - timedelta(seconds=5)
        ]
        
        if recent_events:
            message = {
                "type": "events_update",
                "events": [event.to_dict() for event in recent_events[-10:]],  # Last 10 events
                "timestamp": datetime.now().isoformat()
            }
            
            # Send to all connected clients
            disconnected = []
            for websocket in self.connected_websockets:
                try:
                    await websocket.send_text(json.dumps(message))
                except Exception:
                    disconnected.append(websocket)
            
            # Remove disconnected clients
            for ws in disconnected:
                self.connected_websockets.remove(ws)

    def get_dashboard_html(self) -> str:
        """Get HTML for the debug dashboard"""
        return """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>ALIMS Debug Dashboard</title>
    <style>
        body { 
            font-family: 'Consolas', 'Monaco', monospace; 
            margin: 0; 
            padding: 20px; 
            background-color: #1a1a1a; 
            color: #00ff00; 
        }
        .container { max-width: 1400px; margin: 0 auto; }
        .header { text-align: center; margin-bottom: 30px; }
        .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; }
        .panel { 
            background: #2d2d2d; 
            border: 1px solid #444; 
            border-radius: 8px; 
            padding: 20px; 
            height: 400px; 
            overflow-y: auto; 
        }
        .panel h3 { margin-top: 0; color: #ffff00; }
        .event { 
            margin: 10px 0; 
            padding: 8px; 
            background: #3d3d3d; 
            border-left: 4px solid #00ff00; 
            font-size: 12px; 
        }
        .event.error { border-left-color: #ff0000; }
        .event.warn { border-left-color: #ffff00; }
        .event-time { color: #888; }
        .event-agent { color: #00ffff; }
        .stats { 
            display: grid; 
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); 
            gap: 15px; 
            margin-bottom: 20px; 
        }
        .stat-card { 
            background: #2d2d2d; 
            padding: 15px; 
            border-radius: 8px; 
            text-align: center; 
        }
        .stat-number { font-size: 24px; font-weight: bold; color: #00ffff; }
        .stat-label { color: #888; }
        .live-indicator { 
            color: #00ff00; 
            animation: blink 1s infinite; 
        }
        @keyframes blink { 50% { opacity: 0.5; } }
        .conversation { 
            margin: 8px 0; 
            padding: 8px; 
            background: #3d3d3d; 
            border-radius: 4px; 
        }
        .agent-card {
            margin: 8px 0;
            padding: 10px;
            background: #3d3d3d;
            border-radius: 4px;
            border-left: 4px solid #00ff00;
        }
        .agent-card.idle { border-left-color: #888; }
        .agent-card.busy { border-left-color: #ffff00; }
        .agent-card.error { border-left-color: #ff0000; }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🔬 ALIMS Debug Dashboard</h1>
            <p>Real-time agent monitoring and debugging <span class="live-indicator">● LIVE</span></p>
        </div>
        
        <div class="stats" id="stats">
            <!-- Stats will be populated by JavaScript -->
        </div>
        
        <div class="grid">
            <div class="panel">
                <h3>🔄 Recent Events</h3>
                <div id="events"></div>
            </div>
            
            <div class="panel">
                <h3>💬 Active Conversations</h3>
                <div id="conversations"></div>
            </div>
            
            <div class="panel">
                <h3>🤖 Agent Status</h3>
                <div id="agents"></div>
            </div>
            
            <div class="panel">
                <h3>📊 Performance Metrics</h3>
                <div id="performance"></div>
            </div>
        </div>
    </div>

    <script>
        let ws;
        
        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            ws = new WebSocket(`${protocol}//${window.location.host}/ws/debug`);
            
            ws.onmessage = function(event) {
                const data = JSON.parse(event.data);
                if (data.type === 'events_update') {
                    updateEvents(data.events);
                }
            };
            
            ws.onclose = function() {
                setTimeout(connectWebSocket, 3000); // Reconnect after 3 seconds
            };
        }
        
        function updateStats(data) {
            const statsHtml = `
                <div class="stat-card">
                    <div class="stat-number">${data.total_events}</div>
                    <div class="stat-label">Total Events</div>
                </div>
                <div class="stat-card">
                    <div class="stat-number">${data.recent_events}</div>
                    <div class="stat-label">Recent (10m)</div>
                </div>
                <div class="stat-card">
                    <div class="stat-number">${data.active_conversations}</div>
                    <div class="stat-label">Conversations</div>
                </div>
                <div class="stat-card">
                    <div class="stat-number">${data.tracked_agents}</div>
                    <div class="stat-label">Agents</div>
                </div>
            `;
            document.getElementById('stats').innerHTML = statsHtml;
        }
        
        function updateEvents(events) {
            const eventsDiv = document.getElementById('events');
            const eventsHtml = events.map(event => {
                const levelClass = event.level.toLowerCase();
                return `
                    <div class="event ${levelClass}">
                        <div class="event-time">${event.formatted_time}</div>
                        <div class="event-agent">${event.agent_type}[${event.agent_id}]</div>
                        <div>${event.event_type}: ${event.message}</div>
                    </div>
                `;
            }).join('');
            eventsDiv.innerHTML = eventsHtml;
        }
        
        function updateConversations(conversations) {
            const conversationsDiv = document.getElementById('conversations');
            const conversationsHtml = conversations.map(conv => `
                <div class="conversation">
                    <strong>${conv.conversation_id}</strong><br>
                    Events: ${conv.event_count} | Agents: ${conv.agents_involved.join(', ')}<br>
                    <small>Last: ${new Date(conv.last_activity).toLocaleTimeString()}</small>
                </div>
            `).join('');
            conversationsDiv.innerHTML = conversationsHtml;
        }
        
        function updateAgents(agents) {
            const agentsDiv = document.getElementById('agents');
            const agentsHtml = agents.map(agent => {
                const status = agent.current_state.processing_message ? 'busy' : 'idle';
                return `
                    <div class="agent-card ${status}">
                        <strong>${agent.agent_id}</strong><br>
                        Recent Activity: ${agent.recent_activity}<br>
                        <small>State: ${JSON.stringify(agent.current_state).substring(0, 100)}...</small>
                    </div>
                `;
            }).join('');
            agentsDiv.innerHTML = agentsHtml;
        }
        
        async function fetchAndUpdate() {
            try {
                // Fetch overall status
                const statusResponse = await fetch('/api/debug/status');
                const statusData = await statusResponse.json();
                updateStats(statusData);
                
                // Fetch conversations
                const conversationsResponse = await fetch('/api/debug/conversations');
                const conversationsData = await conversationsResponse.json();
                updateConversations(conversationsData.conversations);
                
                // Fetch agents
                const agentsResponse = await fetch('/api/debug/agents');
                const agentsData = await agentsResponse.json();
                updateAgents(agentsData.agents);
                
                // Fetch recent events
                const eventsResponse = await fetch('/api/debug/events/recent?limit=20');
                const eventsData = await eventsResponse.json();
                updateEvents(eventsData.events);
                
            } catch (error) {
                console.error('Error fetching data:', error);
            }
        }
        
        // Initialize
        connectWebSocket();
        fetchAndUpdate();
        setInterval(fetchAndUpdate, 2000); // Update every 2 seconds
    </script>
</body>
</html>
        """

# Global dashboard instance
debug_dashboard = DebugDashboard()

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(debug_dashboard.app, host="0.0.0.0", port=8080)
