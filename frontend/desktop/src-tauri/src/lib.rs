use std::process::Command;
use serde::{Deserialize, Serialize};
use tauri::State;
use std::sync::Mutex;
use tauri::Manager;

#[derive(Debug, Serialize, Deserialize)]
struct AnalysisResults {
    timestamp: String,
    analysis_id: String,
    data_summary: serde_json::Value,
    clustering_results: serde_json::Value,
    consensus: serde_json::Value,
    recommendations: Vec<serde_json::Value>,
    analysis_duration_seconds: Option<f64>,
    error: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct SystemMetrics {
    events_today: u32,
    active_agents: u32,
    clustering_status: String,
    memory_usage: f64,
    cpu_usage: Option<f64>,
    last_analysis: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ChatResponse {
    session_id: String,
    response: ChatMessage,
    error: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ChatMessage {
    content: String,
    agent_name: String,
    specialization: String,
    confidence: f64,
    suggested_actions: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ChatSession {
    session_id: String,
    start_time: f64,
    duration: f64,
    message_count: u32,
    active_agents: Vec<String>,
    messages: Vec<ChatMessage>,
}

// LIMS-specific types
#[derive(Debug, Serialize, Deserialize)]
struct Sample {
    sample_id: String,
    patient_id: String,
    state: String,
    barcode: Option<String>,
    accession_number: Option<String>,
    received_at: String,
    sample_type: String,
    tests_requested: Vec<String>,
    priority: String,
    location: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct LIMSAgent {
    agent_id: String,
    name: String,
    specialization: String,
    state_handled: String,
    personality_traits: serde_json::Value,
    status: String,
    current_tasks: u32,
}

#[derive(Debug, Serialize, Deserialize)]
struct SampleNotification {
    id: String,
    notification_type: String,
    message: String,
    sample_id: Option<String>,
    timestamp: String,
    priority: String,
    requires_action: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct LIMSMessageResponse {
    content: String,
    action_suggestions: Vec<String>,
    workflow_context: WorkflowContext,
    sample_update: Option<Sample>,
}

#[derive(Debug, Serialize, Deserialize)]
struct WorkflowContext {
    current_state: String,
    next_states: Vec<String>,
    required_actions: Vec<String>,
}

struct AppState {
    python_path: Mutex<String>,
}

#[tauri::command]
async fn get_latest_analysis(state: State<'_, AppState>) -> Result<AnalysisResults, String> {
    let python_path = state.python_path.lock().unwrap();
    
    // Execute Python script to get latest analysis
    let output = Command::new(&*python_path)
        .arg("app/analytics/advanced_clustering_engine.py")
        .arg("--export-json")
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to execute Python script: {}", e))?;

    if !output.status.success() {
        return Err(format!("Python script failed: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse JSON: {}", e))
}

#[tauri::command]
async fn get_system_metrics() -> Result<SystemMetrics, String> {
    // Mock system metrics for now - in production this would query actual system stats
    Ok(SystemMetrics {
        events_today: 8542,
        active_agents: 2,
        clustering_status: "Active".to_string(),
        memory_usage: 245.6,
        cpu_usage: Some(12.3),
        last_analysis: Some("2 minutes ago".to_string()),
    })
}

#[tauri::command]
async fn trigger_analysis(state: State<'_, AppState>) -> Result<String, String> {
    let python_path = state.python_path.lock().unwrap();
    
    // Execute Python script to trigger new analysis
    let output = Command::new(&*python_path)
        .arg("app/analytics/advanced_clustering_engine.py")
        .arg("--force-analysis")
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to execute Python script: {}", e))?;

    if !output.status.success() {
        return Err(format!("Analysis failed: {}", String::from_utf8_lossy(&output.stderr)));
    }

    Ok("Analysis triggered successfully".to_string())
}

#[tauri::command]
async fn start_chat_session(state: State<'_, AppState>) -> Result<String, String> {
    let python_path = state.python_path.lock().unwrap();
    
    // Execute Python script to start a chat session
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(r#"
import asyncio
from backend.app.system.system_integration import ALimsSystemIntegration

async def start_session():
    system = ALimsSystemIntegration()
    await system.initialize()
    result = await system.chat_with_agents("", None)
    print(result.get("session_id", ""))

asyncio.run(start_session())
        "#)
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to start chat session: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to start chat session: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let session_id = String::from_utf8_lossy(&output.stdout).trim().to_string();
    Ok(session_id)
}

#[tauri::command]
async fn send_chat_message(state: State<'_, AppState>, message: String, session_id: String) -> Result<ChatResponse, String> {
    let python_path = state.python_path.lock().unwrap();
    
    // Execute Python script to send a chat message
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(format!(r#"
import asyncio
import json
from backend.app.system.system_integration import ALimsSystemIntegration

async def send_message():
    system = ALimsSystemIntegration()
    await system.initialize()
    result = await system.chat_with_agents("{}", "{}")
    print(json.dumps(result))

asyncio.run(send_message())
        "#, message.replace("\"", "\\\""), session_id))
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to send message: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to send message: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse response: {}", e))
}

#[tauri::command]
async fn get_chat_history(state: State<'_, AppState>, session_id: String) -> Result<ChatSession, String> {
    let python_path = state.python_path.lock().unwrap();
    
    // Execute Python script to get chat history
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(format!(r#"
import asyncio
import json
from backend.app.system.system_integration import ALimsSystemIntegration

async def get_history():
    system = ALimsSystemIntegration()
    await system.initialize()
    if system.agent_interface:
        history = system.agent_interface.get_session_history("{}")
        print(json.dumps(history))
    else:
        print(json.dumps({{}}))

asyncio.run(get_history())
        "#, session_id))
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to get chat history: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to get chat history: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse chat history: {}", e))
}

// LIMS-specific commands
#[tauri::command]
async fn get_lims_agents(state: State<'_, AppState>) -> Result<Vec<LIMSAgent>, String> {
    let python_path = state.python_path.lock().unwrap();
    
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(r#"
import asyncio
import json
from backend.app.lims.workflows.core_workflow import LIMSWorkflow

async def get_agents():
    workflow = LIMSWorkflow()
    agents = []
    
    # Mock agents for now - in production this would come from agent registry
    agents.append({
        "agent_id": "reception_001",
        "name": "Sam the Sample Reception Agent", 
        "specialization": "sample_reception",
        "state_handled": "RECEIVED",
        "personality_traits": {"friendliness": 0.8, "precision": 0.9},
        "status": "IDLE",
        "current_tasks": 0
    })
    
    agents.append({
        "agent_id": "accessioning_001",
        "name": "Alex the Accessioning Agent",
        "specialization": "sample_accessioning", 
        "state_handled": "ACCESSIONED",
        "personality_traits": {"thoroughness": 0.9, "patience": 0.7},
        "status": "IDLE",
        "current_tasks": 0
    })
    
    print(json.dumps(agents))

asyncio.run(get_agents())
        "#)
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to get LIMS agents: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to get LIMS agents: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse agents: {}", e))
}

#[tauri::command]
async fn get_pending_samples(state: State<'_, AppState>) -> Result<Vec<Sample>, String> {
    let python_path = state.python_path.lock().unwrap();
    
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(r#"
import asyncio
import json
from datetime import datetime

async def get_samples():
    # Mock pending samples - in production this would query the database
    samples = []
    print(json.dumps(samples))

asyncio.run(get_samples())
        "#)
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to get pending samples: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to get pending samples: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse samples: {}", e))
}

#[tauri::command]
async fn get_sample_notifications(state: State<'_, AppState>) -> Result<Vec<SampleNotification>, String> {
    let python_path = state.python_path.lock().unwrap();
    
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(r#"
import asyncio
import json
from datetime import datetime

async def get_notifications():
    # Mock notifications - in production this would come from the notification system
    notifications = []
    print(json.dumps(notifications))

asyncio.run(get_notifications())
        "#)
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to get notifications: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to get notifications: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse notifications: {}", e))
}

#[tauri::command]
async fn register_new_sample(state: State<'_, AppState>, sample_data: serde_json::Value) -> Result<Sample, String> {
    let python_path = state.python_path.lock().unwrap();
    
    let sample_json = serde_json::to_string(&sample_data)
        .map_err(|e| format!("Failed to serialize sample data: {}", e))?;
    
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(format!(r#"
import asyncio
import json
from datetime import datetime
from backend.app.lims.models import Sample, SampleState, Priority

async def register_sample():
    sample_data = json.loads('{}')
    
    # Create new sample
    sample = Sample(
        sample_id=sample_data.get("sample_id", "SAM123"),
        patient_id=sample_data.get("patient_id", "PAT123"),
        state=SampleState.RECEIVED,
        received_at=datetime.now(),
        sample_type=sample_data.get("sample_type", "Blood"),
        tests_requested=sample_data.get("tests_requested", ["CBC"]),
        priority=Priority[sample_data.get("priority", "ROUTINE")]
    )
    
    # Convert to dict for JSON serialization
    result = {{
        "sample_id": sample.sample_id,
        "patient_id": sample.patient_id,
        "state": sample.state.value,
        "barcode": sample.barcode,
        "accession_number": sample.accession_number,
        "received_at": sample.received_at.isoformat(),
        "sample_type": sample.sample_type,
        "tests_requested": sample.tests_requested,
        "priority": sample.priority.value,
        "location": sample.location
    }}
    
    print(json.dumps(result))

asyncio.run(register_sample())
        "#, sample_json.replace("\"", "\\\"")))
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to register sample: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to register sample: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse sample: {}", e))
}

#[tauri::command]
async fn send_lims_message(
    state: State<'_, AppState>,
    conversation_id: String,
    message: String,
    agent_id: String,
    sample_context: Option<serde_json::Value>
) -> Result<LIMSMessageResponse, String> {
    let python_path = state.python_path.lock().unwrap();
    
    let sample_json = match sample_context {
        Some(context) => serde_json::to_string(&context).unwrap_or("null".to_string()),
        None => "null".to_string()
    };
    
    let output = Command::new(&*python_path)
        .arg("-c")
        .arg(format!(r#"
import asyncio
import json
from backend.app.lims.agents.sample_reception import SampleReceptionAgent
from backend.app.lims.agents.sample_accessioning import SampleAccessioningAgent
from backend.app.lims.models import Sample, SampleState, Priority
from datetime import datetime

async def process_message():
    message = "{}"
    agent_id = "{}"
    conversation_id = "{}"
    sample_context = json.loads('{}')
    
    # Select appropriate agent
    if "reception" in agent_id:
        agent = SampleReceptionAgent()
    elif "accessioning" in agent_id:
        agent = SampleAccessioningAgent()
    else:
        agent = SampleReceptionAgent()  # Default
    
    # Process the message
    try:
        if sample_context:
            # Create sample object from context
            sample = Sample(
                sample_id=sample_context["sample_id"],
                patient_id=sample_context["patient_id"],
                state=SampleState(sample_context["state"]),
                received_at=datetime.fromisoformat(sample_context["received_at"].replace("Z", "+00:00")),
                sample_type=sample_context["sample_type"],
                tests_requested=sample_context["tests_requested"],
                priority=Priority(sample_context["priority"])
            )
            
            # Process with context
            response = await agent.process_sample(sample, message)
        else:
            # Process without context  
            response = await agent.process_message(message)
        
        # Generate response
        result = {{
            "content": response.get("message", "I understand. Let me help you with that."),
            "action_suggestions": response.get("suggested_actions", [
                "Verify sample information",
                "Generate barcode", 
                "Move to next step",
                "Need help"
            ]),
            "workflow_context": {{
                "current_state": response.get("current_state", "RECEIVED"),
                "next_states": response.get("next_states", ["ACCESSIONED"]),
                "required_actions": response.get("required_actions", ["Verify information"])
            }},
            "sample_update": response.get("updated_sample")
        }}
        
        print(json.dumps(result))
        
    except Exception as e:
        # Fallback response
        result = {{
            "content": f"I understand your request about: {{message}}. I'm here to help you process this sample through our LIMS workflow. What specific action would you like to take?",
            "action_suggestions": [
                "Verify sample information",
                "Generate barcode",
                "Move to accessioning", 
                "Flag for review"
            ],
            "workflow_context": {{
                "current_state": "RECEIVED",
                "next_states": ["ACCESSIONED"],
                "required_actions": ["Verify patient info", "Generate barcode"]
            }},
            "sample_update": None
        }}
        print(json.dumps(result))

asyncio.run(process_message())
        "#, 
        message.replace("\"", "\\\""),
        agent_id.replace("\"", "\\\""), 
        conversation_id.replace("\"", "\\\""),
        sample_json.replace("\"", "\\\"")))
        .current_dir("../")
        .output()
        .map_err(|e| format!("Failed to send LIMS message: {}", e))?;

    if !output.status.success() {
        return Err(format!("Failed to send LIMS message: {}", String::from_utf8_lossy(&output.stderr)));
    }

    let json_str = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str(&json_str)
        .map_err(|e| format!("Failed to parse LIMS response: {}", e))
}

#[cfg_attr(mobile, tauri::mobile_entry_point)]
pub fn run() {
    // Detect Python path
    let python_path = detect_python_path();
    
    tauri::Builder::default()
        .manage(AppState {
            python_path: Mutex::new(python_path),
        })
        .invoke_handler(tauri::generate_handler![
            get_latest_analysis,
            get_system_metrics,
            trigger_analysis,
            start_chat_session,
            send_chat_message,
            get_chat_history,
            get_lims_agents,
            get_pending_samples,
            get_sample_notifications,
            register_new_sample,
            send_lims_message
        ])
        .setup(|app| {
            if cfg!(debug_assertions) {
                app.handle().plugin(
                    tauri_plugin_log::Builder::default()
                        .level(log::LevelFilter::Info)
                        .build(),
                )?;
            }
            
            // Show the main window immediately on startup
            if let Some(window) = app.get_webview_window("main") {
                window.show().expect("Failed to show window");
                window.set_focus().expect("Failed to focus window");
                
                // Ensure window is brought to front
                #[cfg(target_os = "macos")]
                window.set_always_on_top(true).expect("Failed to set always on top");
                
                // Small delay then disable always on top (macOS only)
                #[cfg(target_os = "macos")]
                {
                    let window_handle = window.clone();
                    std::thread::spawn(move || {
                        std::thread::sleep(std::time::Duration::from_millis(1000));
                        window_handle.set_always_on_top(false).expect("Failed to unset always on top");
                    });
                }
            }
            
            Ok(())
        })
        .run(tauri::generate_context!())
        .expect("error while running tauri application");
}

fn detect_python_path() -> String {
    // Try different Python paths
    let candidates = vec![
        "python3",
        "python",
        "./alims_env/bin/python",
        "./alims_env/Scripts/python.exe",
    ];
    
    for candidate in candidates {
        if let Ok(output) = Command::new(candidate).arg("--version").output() {
            if output.status.success() {
                return candidate.to_string();
            }
        }
    }
    
    // Default fallback
    "python3".to_string()
}
