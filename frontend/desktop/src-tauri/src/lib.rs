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
            get_chat_history
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
