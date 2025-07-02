"""
ALims AI API Server
FastAPI server that exposes the Central AI Brain through REST endpoints
for the Tauri desktop application and other frontends.
"""

import logging
import yaml
import sys
import os
from datetime import datetime
from typing import Dict, Any, List, Optional
from contextlib import asynccontextmanager

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect, File, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
import uvicorn

# Add the backend path to sys.path for imports
sys.path.append(os.path.join(os.path.dirname(__file__), '..', '..'))

from app.ai.central_brain import CentralAIBrain, create_central_brain
from app.core.central_integration import CentralIntegration
from app.core.conversation_memory import conversation_memory
from app.core.multimodal_processor import multimodal_processor

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Global AI system instance
central_brain: Optional[CentralAIBrain] = None
central_integration: Optional[CentralIntegration] = None

# Request/Response Models
class ChatMessage(BaseModel):
    message: str
    context_type: str = "chat"
    session_id: Optional[str] = None
    request_visualization: Optional[bool] = False

class VisualizationData(BaseModel):
    type: str  # 'chart', 'plot', 'table', 'graph', 'text', 'code'
    title: Optional[str] = None
    data: Optional[Dict[str, Any]] = None
    config: Optional[Dict[str, Any]] = None
    content: Optional[str] = None

class ChatResponse(BaseModel):
    success: bool
    message: str
    response_time: float
    interaction_id: int
    agent_info: Dict[str, Any]
    visualization: Optional[VisualizationData] = None
    error: Optional[str] = None

class SystemStatus(BaseModel):
    status: str
    uptime: float
    model_name: str
    agents_active: int
    interaction_count: int
    health_status: Dict[str, Any]

class BlobCommand(BaseModel):
    command: str
    parameters: Optional[Dict[str, Any]] = None

# WebSocket connection manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: List[WebSocket] = []

    async def connect(self, websocket: WebSocket):
        await websocket.accept()
        self.active_connections.append(websocket)

    def disconnect(self, websocket: WebSocket):
        self.active_connections.remove(websocket)

    async def send_personal_message(self, message: str, websocket: WebSocket):
        await websocket.send_text(message)

    async def broadcast(self, message: str):
        for connection in self.active_connections:
            await connection.send_text(message)

manager = ConnectionManager()

@asynccontextmanager
async def lifespan(app: FastAPI):
    """Startup and shutdown events for the FastAPI app"""
    global central_brain, central_integration
    
    # Startup
    logger.info("🚀 Starting ALims AI API Server...")
    
    try:
        # Load configuration
        config = load_config()
        
        # Initialize Central AI Brain
        central_brain = await create_central_brain(config)
        if not central_brain:
            logger.error("Failed to create Central AI Brain")
            raise Exception("AI system initialization failed")
        
        # Initialize Central Integration
        central_integration = CentralIntegration(config)
        await central_integration.initialize()
        
        logger.info("✅ ALims AI API Server started successfully")
        
    except Exception as e:
        logger.error(f"❌ Failed to start AI API Server: {e}")
        raise
    
    yield
    
    # Shutdown
    logger.info("🛑 Shutting down ALims AI API Server...")
    if central_brain:
        await central_brain.stop()
    logger.info("✅ AI API Server shutdown complete")

# Create FastAPI app
app = FastAPI(
    title="ALims AI API",
    description="API server for ALims Central AI Brain",
    version="1.0.0",
    lifespan=lifespan
)

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "http://localhost:1420", 
        "http://127.0.0.1:1420", 
        "http://localhost:3000",
        "http://127.0.0.1:3000",
        "tauri://localhost"
    ],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

def load_config() -> Dict[str, Any]:
    """Load ALims configuration"""
    try:
        # Load AI config
        with open('config/ai_config.yaml', 'r') as f:
            ai_config = yaml.safe_load(f)
        
        # Load default config
        with open('config/default.yaml', 'r') as f:
            default_config = yaml.safe_load(f)
        
        # Merge configurations
        config = {**default_config, **ai_config}
        
        # Set up AI brain config
        config['ai_brain'] = {
            'model_name': ai_config['model']['model_name'],
            'base_url': 'http://localhost:11434',
            'temperature': ai_config['model']['temperature'],
            'max_tokens': ai_config['model']['max_tokens'],
            'context_window': ai_config['model']['context_window'],
            'timeout': 30
        }
        
        return config
        
    except Exception as e:
        logger.error(f"Failed to load config: {e}")
        # Fallback config
        return {
            'ai_brain': {
                'model_name': 'gemma3:4b',
                'base_url': 'http://localhost:11434',
                'temperature': 0.7,
                'max_tokens': 2048,
                'context_window': 8192,
                'timeout': 30
            }
        }

@app.get("/")
async def root():
    """API root endpoint"""
    return {"message": "ALims AI API Server", "status": "running"}

@app.get("/health", response_model=SystemStatus)
async def health_check():
    """Get system health status"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        health_status = await central_brain.get_health_status()
        uptime = (datetime.now() - central_brain.startup_time).total_seconds() if central_brain.startup_time else 0
        
        return SystemStatus(
            status="healthy" if health_status.get("central_brain_running", False) else "unhealthy",
            uptime=uptime,
            model_name=health_status.get("ollama_model", "unknown"),
            agents_active=5,  # Number of active agents
            interaction_count=central_brain.interaction_count,
            health_status=health_status
        )
        
    except Exception as e:
        logger.error(f"Health check failed: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/restart")
async def restart_ai_system():
    """Restart the AI system components"""
    global central_brain, central_integration
    
    try:
        logger.info("🔄 Restarting AI system...")
        
        # Stop existing components
        if central_brain:
            await central_brain.stop()
        if central_integration:
            await central_integration.stop()
        
        # Reinitialize components
        config = load_config()
        
        # Recreate Central AI Brain
        central_brain = await create_central_brain(config)
        if not central_brain:
            raise Exception("Failed to recreate Central AI Brain")
        
        # Recreate Central Integration
        central_integration = CentralIntegration(config)
        await central_integration.initialize()
        
        logger.info("✅ AI system restart completed successfully")
        
        return {"success": True, "message": "AI system restarted successfully"}
        
    except Exception as e:
        logger.error(f"❌ AI system restart failed: {e}")
        raise HTTPException(status_code=500, detail=f"Restart failed: {str(e)}")

@app.post("/chat", response_model=ChatResponse)
async def chat_with_ai(message: ChatMessage):
    """Chat with the AI system with conversation memory"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        start_time = datetime.now()
        
        # Get or create conversation session
        session_id = conversation_memory.get_or_create_session()
        
        # Store user message
        conversation_memory.add_message(
            content=message.message,
            sender="user",
            session_id=session_id,
            message_type="text"
        )
        
        # Get conversation context for AI
        context = conversation_memory.get_context_for_prompt(session_id, max_messages=8)
        
        # Enhanced prompt with conversation context
        enhanced_message = f"{context}\n\nCurrent message: {message.message}"
        
        # Process message through Central AI Brain
        result = await central_brain.chat_with_user_interface_agent(
            enhanced_message,
            context={"session_id": session_id, "has_history": len(context) > 50}
        )
        
        response_time = (datetime.now() - start_time).total_seconds()
        ai_message = result.get("message", "")
        
        # Check if code was executed
        execution_result = result.get("execution_result")
        code_executed = result.get("code_executed", False)
        
        # Generate visualization if requested or if message contains visualization keywords
        visualization = None
        if (message.request_visualization or 
            any(keyword in message.message.lower() for keyword in ['plot', 'chart', 'graph', 'table', 'analyze', 'show', 'visualize']) or
            (execution_result and execution_result.get("success"))):
            # Only pass execution_result if code was actually executed
            logger.info(f"Generating visualization - code_executed: {code_executed}, execution_result exists: {execution_result is not None}")
            if execution_result:
                logger.info(f"Execution result keys: {list(execution_result.keys())}")
                logger.info(f"Has visualization: {execution_result.get('visualization') is not None}")
            visualization = await generate_visualization(
                message.message, 
                ai_message, 
                execution_result if code_executed else None
            )
        
        # Store AI response with visualization data
        conversation_memory.add_message(
            content=ai_message,
            sender="ai",
            session_id=session_id,
            message_type="visualization" if visualization else "text",
            visualization_data=visualization.dict() if visualization else None,
            response_time=response_time
        )
        
        # Add context topics for better conversation tracking
        if any(keyword in message.message.lower() for keyword in ['system', 'stats', 'dashboard']):
            conversation_memory.add_context_topic(
                "system_monitoring", 
                "User interested in system statistics and performance monitoring",
                session_id, 
                importance=1.5
            )
        
        if result.get("success", False):
            return ChatResponse(
                success=True,
                message=ai_message,
                response_time=response_time,
                interaction_id=result.get("interaction_id", 0),
                agent_info={
                    "agent": result.get("agent", "central_brain"),
                    "context_used": True,
                    "session_id": session_id,
                    "conversation_length": len(conversation_memory.get_conversation_history(session_id))
                },
                visualization=visualization
            )
        else:
            return ChatResponse(
                success=False,
                message=result.get("message", "Sorry, I encountered an error."),
                response_time=response_time,
                interaction_id=0,
                agent_info={"agent": "error_handler", "session_id": session_id},
                visualization=visualization,
                error=result.get("error", "Unknown error")
            )
            
    except Exception as e:
        logger.error(f"Chat error: {e}")
        return ChatResponse(
            success=False,
            message="I apologize, but I'm experiencing technical difficulties. Please try again.",
            response_time=0.0,
            interaction_id=0,
            agent_info={"agent": "error_handler"},
            error=str(e)
        )

@app.post("/blob-command")
async def process_blob_command(command: BlobCommand):
    """Process blob creature commands"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        # Use the AI to interpret blob commands
        system_prompt = """You are controlling an animated blob creature in a desktop application.
        
        The user will give you commands to control the blob's appearance and behavior.
        Respond with a JSON object containing specific blob control parameters.
        
        Available blob properties:
        - mood: "happy", "sad", "excited", "sleeping", "thinking", "dancing"
        - color: any CSS color (hex, rgb, or named colors)
        - size: number between 0.5 and 2.0 (scale factor)
        - position: "center", "left", "right", "top", "bottom"
        - animation: "bounce", "pulse", "wiggle", "spin", "float"
        
        Examples:
        - "make it happy" -> {"mood": "happy"}
        - "turn it red" -> {"color": "#ff0000"}
        - "make it bigger" -> {"size": 1.5}
        - "move to the left" -> {"position": "left"}
        - "make it dance" -> {"mood": "dancing", "animation": "bounce"}
        
        Respond ONLY with valid JSON containing the blob control parameters."""
        
        result = await central_brain.ollama_client.generate_response(
            prompt=f"User command: {command.command}",
            system_prompt=system_prompt
        )
        
        # Try to parse the AI response as JSON
        try:
            import json
            blob_params = json.loads(result.strip())
            return {"success": True, "blob_params": blob_params, "ai_response": result}
        except json.JSONDecodeError:
            # Fallback parsing for non-JSON responses
            blob_params = parse_blob_command_fallback(command.command)
            return {"success": True, "blob_params": blob_params, "ai_response": result}
            
    except Exception as e:
        logger.error(f"Blob command error: {e}")
        return {"success": False, "error": str(e)}

async def generate_visualization(user_message: str, ai_response: str, execution_result: Optional[Dict[str, Any]] = None) -> Optional[VisualizationData]:
    """Generate visualization data based on user request and AI response
    
    Args:
        user_message: The user's original message
        ai_response: The AI's response text
        execution_result: Optional code execution results containing data to visualize
    """
    try:
        # If we have execution results with visualization data, use that first
        if execution_result and execution_result.get("visualization"):
            viz_data = execution_result["visualization"]
            if viz_data.get("type") == "image" and viz_data.get("data"):
                # This is a matplotlib figure captured as base64 PNG
                logger.info(f"Creating image visualization with base64 data length: {len(viz_data['data'])}")
                return VisualizationData(
                    type="image",
                    title="Generated Visualization",
                    content=f"data:image/png;base64,{viz_data['data']}"
                )
            else:
                return VisualizationData(
                    type=viz_data.get("type", "image"),
                    title="Code Execution Result",
                    data=viz_data.get("data"),
                    content=viz_data.get("content")
                )
        
        # Check if we have execution results with data to visualize
        if execution_result and execution_result.get("success"):
            stdout = execution_result.get("stdout", "")
            
            # Try to parse data from stdout for visualization
            if "prime" in user_message.lower() and any(chart_type in user_message.lower() for chart_type in ["chart", "plot", "graph"]):
                # Extract prime numbers from output
                import re
                numbers = re.findall(r'\d+', stdout)
                if numbers and len(numbers) > 1:
                    prime_numbers = [int(n) for n in numbers if int(n) > 1][:20]  # Limit to 20
                    
                    if "line" in user_message.lower():
                        return VisualizationData(
                            type="line",
                            title="Prime Numbers Visualization",
                            data={
                                "labels": [str(i+1) for i in range(len(prime_numbers))],
                                "datasets": [{
                                    "label": "Prime Numbers",
                                    "data": prime_numbers,
                                    "borderColor": "rgb(75, 192, 192)",
                                    "backgroundColor": "rgba(75, 192, 192, 0.2)",
                                    "tension": 0.1
                                }]
                            }
                        )
                    elif "bar" in user_message.lower():
                        return VisualizationData(
                            type="bar",
                            title="Prime Numbers Bar Chart",
                            data={
                                "labels": [f"P{i+1}" for i in range(len(prime_numbers))],
                                "datasets": [{
                                    "label": "Prime Value",
                                    "data": prime_numbers,
                                    "backgroundColor": "rgba(54, 162, 235, 0.8)",
                                    "borderColor": "rgba(54, 162, 235, 1)",
                                    "borderWidth": 1
                                }]
                            }
                        )
            
            # For hash function results
            if "hash" in user_message.lower() and "->" in stdout:
                # Parse hash results
                hash_results = []
                labels = []
                for line in stdout.split('\n'):
                    if '->' in line:
                        parts = line.split('->')
                        if len(parts) == 2:
                            label = parts[0].strip()
                            value = parts[1].strip()
                            try:
                                labels.append(label)
                                hash_results.append(int(value))
                            except:
                                pass
                
                if hash_results:
                    return VisualizationData(
                        type="bar",
                        title="Hash Function Results",
                        data={
                            "labels": labels,
                            "datasets": [{
                                "label": "Hash Values",
                                "data": hash_results,
                                "backgroundColor": [
                                    "rgba(255, 99, 132, 0.8)",
                                    "rgba(54, 162, 235, 0.8)",
                                    "rgba(255, 205, 86, 0.8)",
                                    "rgba(75, 192, 192, 0.8)",
                                    "rgba(153, 102, 255, 0.8)"
                                ][:len(hash_results)],
                                "borderWidth": 2
                            }]
                        }
                    )
        
        # Fall back to keyword-based visualization generation
        message_lower = user_message.lower()
        
        if any(keyword in message_lower for keyword in ['system', 'stats', 'statistics', 'dashboard', 'monitor', 'performance']):
            return VisualizationData(
                type="system_dashboard",
                title="System Statistics Dashboard",
                data={"dashboard_type": "system_stats"},
                config={"real_time": True, "update_interval": 5000}
            )
        
        elif any(keyword in message_lower for keyword in ['bar chart', 'bar']):
            return VisualizationData(
                type="bar",
                title="Sample Bar Chart",
                data={
                    "labels": ["Q1", "Q2", "Q3", "Q4"],
                    "datasets": [{
                        "label": "Sales",
                        "data": [65, 59, 80, 81],
                        "backgroundColor": ["rgba(255, 99, 132, 0.8)", "rgba(54, 162, 235, 0.8)", 
                                          "rgba(255, 205, 86, 0.8)", "rgba(75, 192, 192, 0.8)"],
                        "borderColor": ["rgba(255, 99, 132, 1)", "rgba(54, 162, 235, 1)", 
                                       "rgba(255, 205, 86, 1)", "rgba(75, 192, 192, 1)"],
                        "borderWidth": 2
                    }]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['pie chart', 'pie', 'doughnut']):
            chart_type = "doughnut" if "doughnut" in message_lower else "pie"
            return VisualizationData(
                type=chart_type,
                title=f"Sample {chart_type.title()} Chart",
                data={
                    "labels": ["Desktop", "Mobile", "Tablet", "Other"],
                    "datasets": [{
                        "data": [45, 30, 20, 5],
                        "backgroundColor": [
                            "rgba(255, 99, 132, 0.8)",
                            "rgba(54, 162, 235, 0.8)",
                            "rgba(255, 205, 86, 0.8)",
                            "rgba(75, 192, 192, 0.8)"
                        ],
                        "borderWidth": 2
                    }]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['line chart', 'line plot', 'sine', 'wave', 'trend']):
            import numpy as np
            if 'sine' in message_lower or 'wave' in message_lower:
                x = np.linspace(0, 4*np.pi, 50)
                y = np.sin(x)
                labels = [f"{i:.1f}" for i in x[:20]]
                data_points = y[:20].tolist()
            else:
                labels = ["Jan", "Feb", "Mar", "Apr", "May", "Jun"]
                data_points = [65, 59, 80, 81, 56, 55]
            
            return VisualizationData(
                type="line",
                title="Line Chart Visualization",
                data={
                    "labels": labels,
                    "datasets": [{
                        "label": "Data Series",
                        "data": data_points,
                        "borderColor": "rgb(75, 192, 192)",
                        "backgroundColor": "rgba(75, 192, 192, 0.2)",
                        "tension": 0.4
                    }]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['scatter', 'scatter plot']):
            import random
            return VisualizationData(
                type="scatter",
                title="Scatter Plot Visualization",
                data={
                    "datasets": [{
                        "label": "Dataset 1",
                        "data": [{"x": random.randint(0, 100), "y": random.randint(0, 100)} for _ in range(20)],
                        "backgroundColor": "rgba(255, 99, 132, 0.6)",
                        "borderColor": "rgba(255, 99, 132, 1)",
                        "pointRadius": 6
                    }]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['radar', 'radar chart']):
            return VisualizationData(
                type="radar",
                title="Radar Chart Visualization",
                data={
                    "labels": ["Speed", "Reliability", "Comfort", "Safety", "Efficiency"],
                    "datasets": [{
                        "label": "Performance",
                        "data": [80, 90, 70, 85, 75],
                        "backgroundColor": "rgba(54, 162, 235, 0.2)",
                        "borderColor": "rgba(54, 162, 235, 1)",
                        "pointBackgroundColor": "rgba(54, 162, 235, 1)",
                        "borderWidth": 2
                    }]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['network', 'graph', 'nodes', 'connections']):
            return VisualizationData(
                type="network",
                title="Network Graph Visualization",
                data={
                    "nodes": [
                        {"id": "Central", "group": 1},
                        {"id": "Node 1", "group": 2},
                        {"id": "Node 2", "group": 2},
                        {"id": "Node 3", "group": 3},
                        {"id": "Node 4", "group": 3},
                        {"id": "Node 5", "group": 3}
                    ],
                    "links": [
                        {"source": "Central", "target": "Node 1"},
                        {"source": "Central", "target": "Node 2"},
                        {"source": "Node 1", "target": "Node 3"},
                        {"source": "Node 2", "target": "Node 4"},
                        {"source": "Node 2", "target": "Node 5"}
                    ]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['heatmap', 'heat map']):
            return VisualizationData(
                type="plotly",
                title="Heatmap Visualization",
                data={
                    "data": [{
                        "z": [[1, 20, 30], [20, 1, 60], [30, 60, 1]],
                        "type": "heatmap",
                        "colorscale": "Viridis"
                    }],
                    "layout": {
                        "title": "Sample Heatmap",
                        "xaxis": {"title": "X Axis"},
                        "yaxis": {"title": "Y Axis"}
                    }
                }
            )
        
        elif any(keyword in message_lower for keyword in ['table', 'data table', 'dataset']):
            return VisualizationData(
                type="table",
                title="Sample Data Table",
                data={
                    "headers": ["Name", "Value", "Category", "Status"],
                    "rows": [
                        ["Item A", 100, "Type 1", "Active"],
                        ["Item B", 250, "Type 2", "Pending"],
                        ["Item C", 150, "Type 1", "Active"],
                        ["Item D", 300, "Type 3", "Completed"]
                    ]
                }
            )
        
        elif any(keyword in message_lower for keyword in ['code', 'algorithm', 'function']):
            code_content = """# Sample Python function
def fibonacci(n):
    if n <= 1:
        return n
    return fibonacci(n-1) + fibonacci(n-2)

# Generate first 10 Fibonacci numbers
fib_sequence = [fibonacci(i) for i in range(10)]
print(fib_sequence)
# Output: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]"""
            
            return VisualizationData(
                type="code",
                title="Python Code Example",
                content=code_content
            )
        
        elif any(keyword in message_lower for keyword in ['analyze', 'analysis', 'summary']):
            return VisualizationData(
                type="text",
                title="AI Analysis Result",
                content=f"Analysis of your request:\n\n{ai_response}\n\nKey insights:\n• Data processing completed\n• Patterns identified\n• Recommendations generated"
            )
        
        # Default visualization for general requests
        if any(keyword in message_lower for keyword in ['show', 'display', 'visualize', 'generate', 'chart']):
            return VisualizationData(
                type="bar",
                title="Generated Visualization",
                data={
                    "labels": ["Data Point 1", "Data Point 2", "Data Point 3"],
                    "datasets": [{
                        "label": "Sample Data",
                        "data": [45, 78, 32],
                        "backgroundColor": ["rgba(139, 69, 19, 0.8)", "rgba(75, 192, 192, 0.8)", "rgba(255, 206, 86, 0.8)"],
                        "borderColor": ["rgba(139, 69, 19, 1)", "rgba(75, 192, 192, 1)", "rgba(255, 206, 86, 1)"],
                        "borderWidth": 2
                    }]
                }
            )
        
        return None
        
    except Exception as e:
        logger.error(f"Visualization generation error: {e}")
        return VisualizationData(
            type="text",
            title="Visualization Error",
            content=f"Sorry, I encountered an error generating the visualization: {str(e)}"
        )

def parse_blob_command_fallback(command: str) -> Dict[str, Any]:
    """Fallback blob command parser if AI doesn't return valid JSON"""
    command_lower = command.lower()
    params = {}
    
    # Mood detection
    if "happy" in command_lower:
        params["mood"] = "happy"
    elif "sad" in command_lower:
        params["mood"] = "sad"
    elif "excited" in command_lower:
        params["mood"] = "excited"
    elif "sleep" in command_lower:
        params["mood"] = "sleeping"
    elif "think" in command_lower:
        params["mood"] = "thinking"
    elif "dance" in command_lower:
        params["mood"] = "dancing"
    
    # Color detection
    colors = {
        "red": "#ff0000", "blue": "#0000ff", "green": "#00ff00",
        "yellow": "#ffff00", "purple": "#800080", "orange": "#ffa500",
        "pink": "#ffc0cb", "white": "#ffffff", "black": "#000000"
    }
    for color_name, color_value in colors.items():
        if color_name in command_lower:
            params["color"] = color_value
            break
    
    # Size detection
    if "bigger" in command_lower or "larger" in command_lower:
        params["size"] = 1.5
    elif "smaller" in command_lower:
        params["size"] = 0.7
    
    # Position detection
    if "left" in command_lower:
        params["position"] = "left"
    elif "right" in command_lower:
        params["position"] = "right"
    elif "center" in command_lower:
        params["position"] = "center"
    
    return params

@app.websocket("/ws/chat")
async def websocket_chat(websocket: WebSocket):
    """WebSocket endpoint for real-time chat"""
    await manager.connect(websocket)
    try:
        while True:
            data = await websocket.receive_text()
            
            # Process message through AI
            if central_brain:
                result = await central_brain.chat_with_user_interface_agent(data)
                response = {
                    "type": "chat_response",
                    "message": result.get("message", ""),
                    "success": result.get("success", False),
                    "timestamp": datetime.now().isoformat()
                }
            else:
                response = {
                    "type": "error",
                    "message": "AI system not available",
                    "success": False,
                    "timestamp": datetime.now().isoformat()
                }
            
            await manager.send_personal_message(str(response), websocket)
            
    except WebSocketDisconnect:
        manager.disconnect(websocket)

@app.get("/system-stats")
async def get_system_statistics():
    """Get real-time system statistics for visualization"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        import psutil
        import time
        from datetime import datetime, timedelta
        
        # Get system metrics
        cpu_percent = psutil.cpu_percent(interval=1)
        memory = psutil.virtual_memory()
        disk = psutil.disk_usage('/')
        
        # Get AI system metrics
        uptime = (datetime.now() - central_brain.startup_time).total_seconds() if central_brain.startup_time else 0
        
        # Agent status
        agents_status = {
            "user_interface": "active" if central_brain.user_interface else "inactive",
            "agent_orchestrator": "active" if central_brain.agent_orchestrator else "inactive",
            "system_controller": "active" if central_brain.system_controller else "inactive",
            "embryo_trainer": "active" if central_brain.embryo_trainer else "inactive",
            "pattern_validator": "active" if central_brain.pattern_validator else "inactive"
        }
        
        active_agents = sum(1 for status in agents_status.values() if status == "active")
        
        # Response time metrics (simulated for now)
        response_times = [0.5, 1.2, 0.8, 2.1, 1.5, 0.9, 1.8, 1.1, 0.7, 1.4]
        avg_response_time = sum(response_times) / len(response_times)
        
        return {
            "timestamp": datetime.now().isoformat(),
            "system_metrics": {
                "cpu_usage": round(cpu_percent, 1),
                "memory_usage": round(memory.percent, 1),
                "memory_total": round(memory.total / (1024**3), 2),  # GB
                "memory_used": round(memory.used / (1024**3), 2),   # GB
                "disk_usage": round(disk.percent, 1),
                "disk_total": round(disk.total / (1024**3), 2),     # GB
                "disk_used": round(disk.used / (1024**3), 2)       # GB
            },
            "ai_metrics": {
                "uptime_seconds": round(uptime, 1),
                "uptime_formatted": str(timedelta(seconds=int(uptime))),
                "active_agents": active_agents,
                "total_agents": len(agents_status),
                "interaction_count": central_brain.interaction_count,
                "avg_response_time": round(avg_response_time, 2),
                "model_name": "gemma3:4b",
                "ollama_status": "healthy"
            },
            "agents_status": agents_status,
            "performance_history": {
                "response_times": response_times,
                "timestamps": [(datetime.now() - timedelta(minutes=i)).isoformat() for i in range(len(response_times)-1, -1, -1)]
            }
        }
        
    except Exception as e:
        logger.error(f"System stats error: {e}")
        return {
            "timestamp": datetime.now().isoformat(),
            "error": str(e),
            "system_metrics": {"cpu_usage": 0, "memory_usage": 0},
            "ai_metrics": {"active_agents": 0, "interaction_count": 0}
        }

@app.get("/agents")
async def get_agents():
    """Get information about active agents"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    agents = {
        "user_interface": {
            "name": "User Interface Agent",
            "status": "active" if central_brain.user_interface else "inactive",
            "description": "Natural language processing and user interaction"
        },
        "agent_orchestrator": {
            "name": "Agent Orchestrator", 
            "status": "active" if central_brain.agent_orchestrator else "inactive",
            "description": "Coordinates multiple agents for complex tasks"
        },
        "system_controller": {
            "name": "System Controller",
            "status": "active" if central_brain.system_controller else "inactive", 
            "description": "Translates user commands to system actions"
        },
        "embryo_trainer": {
            "name": "Embryo Trainer",
            "status": "active" if central_brain.embryo_trainer else "inactive",
            "description": "Intelligent training and validation of embryos"
        },
        "pattern_validator": {
            "name": "Pattern Validator",
            "status": "active" if central_brain.pattern_validator else "inactive",
            "description": "Ensures pattern classification coherence"
        }
    }
    
    return {"agents": agents, "total_agents": len(agents)}

@app.get("/conversation/history")
async def get_conversation_history(limit: int = 20):
    """Get conversation history with memory context"""
    try:
        session_id = conversation_memory.current_session_id
        if not session_id:
            return {"success": True, "history": [], "session_info": {"error": "No active session"}}
        
        history = conversation_memory.get_conversation_history(session_id, limit)
        session_info = conversation_memory.get_session_info(session_id)
        
        return {
            "success": True,
            "history": history,
            "session_info": session_info,
            "total_messages": len(history)
        }
        
    except Exception as e:
        logger.error(f"Error getting conversation history: {e}")
        return {"success": False, "error": str(e)}

@app.post("/conversation/new-session")
async def create_new_conversation_session():
    """Create a new conversation session"""
    try:
        session_id = conversation_memory.create_session()
        session_info = conversation_memory.get_session_info(session_id)
        
        return {
            "success": True,
            "session_id": session_id,
            "session_info": session_info
        }
        
    except Exception as e:
        logger.error(f"Error creating new session: {e}")
        return {"success": False, "error": str(e)}

@app.post("/multimodal/upload")
async def upload_multimodal_file(file: UploadFile = File(...)):
    """Upload and process multimodal content (images, data, code)"""
    try:
        # Read file content
        file_content = await file.read()
        
        # Process file through multimodal processor
        result = await multimodal_processor.process_file(
            file_path="", 
            file_content=file_content, 
            filename=file.filename
        )
        
        if result.get("success"):
            # Generate AI analysis using the processed content
            ai_prompt = result.get("ai_prompt", "")
            if ai_prompt and central_brain:
                ai_response = await central_brain.chat_with_user_interface_agent(
                    ai_prompt,
                    context={"multimodal": True, "file_type": result.get("type")}
                )
                result["ai_analysis"] = ai_response.get("message", "")
        
        return result
        
    except Exception as e:
        logger.error(f"Multimodal upload error: {e}")
        return {"success": False, "error": str(e)}

@app.post("/multimodal/screenshot")
async def capture_and_analyze_screenshot():
    """Capture desktop screenshot and analyze it"""
    try:
        # Capture screenshot
        result = await multimodal_processor.capture_screenshot()
        
        if result.get("success"):
            # Generate AI analysis
            ai_prompt = result.get("ai_prompt", "")
            if ai_prompt and central_brain:
                ai_response = await central_brain.chat_with_user_interface_agent(
                    ai_prompt,
                    context={"multimodal": True, "screenshot": True}
                )
                result["ai_analysis"] = ai_response.get("message", "")
        
        return result
        
    except Exception as e:
        logger.error(f"Screenshot capture error: {e}")
        return {"success": False, "error": str(e)}

@app.post("/multimodal/generate-diagram")
async def generate_mermaid_diagram(request: Dict[str, Any]):
    """Generate Mermaid diagrams"""
    try:
        diagram_type = request.get("type", "flowchart")
        content = request.get("content", "")
        
        # Generate Mermaid syntax
        mermaid_code = multimodal_processor.generate_mermaid_diagram(diagram_type, content)
        
        # Get AI to enhance the diagram
        if central_brain:
            ai_prompt = f"I've generated a {diagram_type} diagram. Please review and suggest improvements:\n\n{mermaid_code}"
            ai_response = await central_brain.chat_with_user_interface_agent(
                ai_prompt,
                context={"multimodal": True, "diagram_generation": True}
            )
            
            return {
                "success": True,
                "diagram_type": diagram_type,
                "mermaid_code": mermaid_code,
                "ai_suggestions": ai_response.get("message", ""),
                "visualization": {
                    "type": "mermaid",
                    "title": f"{diagram_type.title()} Diagram",
                    "content": mermaid_code
                }
            }
        
        return {
            "success": True,
            "diagram_type": diagram_type,
            "mermaid_code": mermaid_code
        }
        
    except Exception as e:
        logger.error(f"Diagram generation error: {e}")
        return {"success": False, "error": str(e)}

@app.get("/multimodal/supported-formats")
async def get_supported_formats():
    """Get list of supported multimodal formats"""
    return {
        "success": True,
        "supported_formats": {
            "images": [".jpg", ".jpeg", ".png", ".bmp", ".tiff", ".webp"],
            "data": [".csv", ".json", ".xlsx", ".tsv"],
            "code": [".py", ".js", ".ts", ".html", ".css", ".yaml", ".yml", ".md"],
            "documents": [".pdf", ".txt"]
        },
        "capabilities": {
            "image_analysis": "Visual content analysis, chart recognition, screenshot capture",
            "data_processing": "CSV/JSON analysis, visualization suggestions, statistical insights",
            "code_analysis": "Code structure analysis, documentation generation, quality metrics",
            "document_processing": "PDF text extraction, document analysis, content summarization",
            "diagram_generation": "Mermaid flowcharts, sequence diagrams, class diagrams"
        }
    }

@app.post("/ai/execute-code")
async def ai_execute_dynamic_code(request: Dict[str, Any]):
    """
    Execute dynamic code through the AI's Lambda-like capability.
    This endpoint allows the AI to run custom code when existing tools aren't sufficient.
    """
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        code = request.get("code", "")
        purpose = request.get("purpose", "general")
        context = request.get("context", {})
        use_lambda_style = request.get("use_lambda_style", False)
        
        if not code:
            raise HTTPException(status_code=400, detail="No code provided")
        
        # Execute the code through Central AI Brain
        result = await central_brain.execute_dynamic_code(
            code=code,
            purpose=purpose,
            context=context,
            use_lambda_style=use_lambda_style
        )
        
        return result
        
    except Exception as e:
        logger.error(f"Code execution error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/ai/lambda-templates")
async def get_lambda_templates():
    """Get available Lambda-style code templates"""
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        from ..ai.code_executor import LAMBDA_TEMPLATES
        
        templates = {}
        for name, code in LAMBDA_TEMPLATES.items():
            template_info = await central_brain.get_lambda_template(name)
            templates[name] = template_info
        
        return {
            "success": True,
            "templates": templates,
            "total_templates": len(templates)
        }
        
    except Exception as e:
        logger.error(f"Error getting lambda templates: {e}")
        raise HTTPException(status_code=500, detail=str(e))

@app.post("/ai/decide-code-execution")
async def decide_code_execution(request: Dict[str, Any]):
    """
    Let the AI decide whether to use existing tools or write custom code.
    """
    if not central_brain:
        raise HTTPException(status_code=503, detail="AI system not initialized")
    
    try:
        user_request = request.get("user_request", "")
        available_tools = request.get("available_tools", [
            "chat", "visualization", "file_analysis", "system_monitoring",
            "pattern_detection", "agent_orchestration"
        ])
        
        if not user_request:
            raise HTTPException(status_code=400, detail="No user request provided")
        
        decision = await central_brain.decide_code_execution(user_request, available_tools)
        
        return decision
        
    except Exception as e:
        logger.error(f"Decision error: {e}")
        raise HTTPException(status_code=500, detail=str(e))

if __name__ == "__main__":
    uvicorn.run(
        "app.web.ai_api_server:app",
        host="127.0.0.1",
        port=8000,
        reload=True,
        log_level="info"
    ) 