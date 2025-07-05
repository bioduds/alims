import React, { useState, useRef, useEffect } from 'react';
import { cn } from '../utils/cn';

// Types
interface VisualizationData {
  type: 'line' | 'bar' | 'pie' | 'doughnut' | 'radar' | 'scatter' | 'heatmap' | 'network' | 'd3_custom' | 'plotly' | 'system_dashboard' | 'chart' | 'plot' | 'table' | 'graph' | 'text' | 'code' | 'image';
  title?: string;
  data?: any;
  config?: any;
  content?: string;
  realTimeData?: boolean;
  updateInterval?: number;
}

interface MainInterfaceChatProps {
  onVisualizationUpdate?: (visualization: VisualizationData | null) => void;
}

interface Message {
  role: 'user' | 'agent';
  content: string;
  timestamp: string;
  agent_source?: string;
  ui_component?: string;
  workflow_action?: string;
  data?: any;
}

export default function MainInterfaceChat(props: MainInterfaceChatProps = {}) {
  const { onVisualizationUpdate } = props;
  const [messages, setMessages] = useState<Message[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [input, setInput] = useState('');
  const [conversationId, setConversationId] = useState<string | null>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    // Start a conversation when component mounts
    startNewConversation();
  }, []);

  useEffect(() => {
    scrollToBottom();
  }, [messages]);

  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  const startNewConversation = async () => {
    console.log('Starting conversation...');

    // Retry logic for backend connection
    let attempts = 0;
    const maxAttempts = 3;

    while (attempts < maxAttempts) {
      try {
        console.log(`Conversation start attempt ${attempts + 1}/${maxAttempts}`);

        // Direct fetch instead of using client to debug
        const response = await fetch('http://127.0.0.1:8001/api/v1/interface/conversations/start', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({}),
        });

        console.log('Raw response status:', response.status);
        console.log('Raw response ok:', response.ok);

        const data = await response.json();
        console.log('Raw response data:', data);

        if (data.success && data.conversation_id) {
          setConversationId(data.conversation_id);
          setMessages([
            {
              role: 'agent',
              content: `Hello! I am the ALIMS Main Interface Agent. How can I assist you today?`,
              timestamp: new Date().toISOString(),
              agent_source: 'system'
            }
          ]);
          console.log('Conversation started with ID:', data.conversation_id);

          // Set initial stage content
          const initialStageContent = generateStageContentFromResponse(
            'Hello! I am the ALIMS Main Interface Agent. How can I assist you today?',
            'initial greeting'
          );
          if (initialStageContent) {
            onVisualizationUpdate?.(initialStageContent);
          }

          return; // Success, exit the retry loop
        } else {
          console.error(`Attempt ${attempts + 1} failed:`, data.error || 'Unknown error');
          attempts++;
          if (attempts < maxAttempts) {
            console.log(`Waiting 2 seconds before retry...`);
            await new Promise(resolve => setTimeout(resolve, 2000));
          }
        }
      } catch (err) {
        console.error(`Attempt ${attempts + 1} error:`, err);
        attempts++;
        if (attempts < maxAttempts) {
          console.log(`Waiting 2 seconds before retry...`);
          await new Promise(resolve => setTimeout(resolve, 2000));
        }
      }
    }

    // All attempts failed
    console.error('All conversation start attempts failed');
    setMessages([
      {
        role: 'agent',
        content: 'Error: Failed to connect to Main Interface Agent. Please check if the backend is running at http://127.0.0.1:8001',
        timestamp: new Date().toISOString(),
        agent_source: 'error'
      }
    ]);
  };

  // Simplified sendMessage: send user text to main agent and handle responses
  const sendMessage = async (text?: string) => {
    const messageText = text || input.trim();
    console.log('Sending message:', messageText, 'ConversationID:', conversationId);

    if (!messageText || !conversationId || isLoading) {
      console.log('Cannot send message - missing data or loading');
      return;
    }

    const userMsg: Message = {
      role: 'user',
      content: messageText,
      timestamp: new Date().toISOString()
    };
    setMessages(prev => [...prev, userMsg]);
    setInput('');
    setIsLoading(true);

    try {
      console.log('Calling direct fetch to send message...');

      // Direct fetch instead of using client
      const response = await fetch('http://127.0.0.1:8001/api/v1/interface/conversations/message', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          conversation_id: conversationId,
          message: messageText,
          message_type: 'general',
          priority: 'normal'
        }),
      });

      console.log('Send message response status:', response.status);
      const data = await response.json();
      console.log('Send message response data:', data);

      if (data.success && data.messages) {
        // Backend returns only the agent response messages directly
        const agentMessages = data.messages;
        console.log('Agent messages from backend:', agentMessages.length);
        console.log('Raw agent messages:', agentMessages);

        const newMsgs: Message[] = agentMessages.map((m: any) => ({
          role: m.role as 'user' | 'agent',
          content: m.content,
          timestamp: m.timestamp,
          agent_source: m.agent_source
        }));

        console.log('New agent messages to add:', newMsgs);

        // Add the agent response messages
        if (newMsgs.length > 0) {
          setMessages(prev => [...prev, ...newMsgs]);

          // Trigger visualization if agent_source indicates visualization
          newMsgs.forEach(m => {
            if (m.role === 'agent' && m.agent_source === 'visualization') {
              try {
                const viz = JSON.parse(m.content) as VisualizationData;
                onVisualizationUpdate?.(viz);
              } catch (e) {
                console.error('Failed to parse visualization:', e);
              }
            }
          });

          // Generate intelligent stage content based on the conversation
          const lastAgentMessage = newMsgs[newMsgs.length - 1];
          if (lastAgentMessage && lastAgentMessage.role === 'agent') {
            const userMessage = messages[messages.length - 1]?.content || '';
            const stageContent = generateStageContentFromResponse(lastAgentMessage.content, userMessage);
            if (stageContent) {
              onVisualizationUpdate?.(stageContent);
            }
          }
        }
      } else {
        console.error('Send message failed:', data.error);
        const errorMsg: Message = {
          role: 'agent',
          content: `Error: ${data.error || 'Failed to send message'}`,
          timestamp: new Date().toISOString(),
          agent_source: 'error'
        };
        setMessages(prev => [...prev, errorMsg]);
      }
    } catch (err) {
      console.error(`Failed to send message: ${err}`);
      const errorMsg: Message = {
        role: 'agent',
        content: `Network error: ${err}`,
        timestamp: new Date().toISOString(),
        agent_source: 'error'
      };
      setMessages(prev => [...prev, errorMsg]);
    } finally {
      setIsLoading(false);
    }
  };

  const clearChat = () => {
    setMessages([]);
    setConversationId(null);
    startNewConversation();
  };

  const handleKeyPress = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      sendMessage();
    }
  };

  const renderMessageContent = (message: Message) => (
    <p className={cn(
      "text-sm whitespace-pre-wrap",
      message.role === 'agent' ? 'text-gray-200' : 'text-blue-300'
    )}>
      {message.content}
    </p>
  );

  // Function to generate intelligent stage content based on chat response
  const generateStageContentFromResponse = (agentMessage: string, userMessage: string): VisualizationData | null => {
    const msgLower = agentMessage.toLowerCase();
    const userMsgLower = userMessage.toLowerCase();

    // Sample tracking and registration
    if (msgLower.includes('sample') && (msgLower.includes('register') || msgLower.includes('batch') || msgLower.includes('accession'))) {
      return {
        type: 'text',
        title: '🧪 Sample Registration Guide',
        content: `Sample Registration Workflow:

📋 Required Information:
• Batch numbers or accession codes
• Sample description (type, source, parameters)
• Collection date and conditions
• Associated workflows/protocols

🔄 Next Steps:
1. Prepare sample labels with unique identifiers
2. Document chain of custody information
3. Select appropriate testing protocols
4. Schedule analysis based on priority

💡 Tip: Use the sample tracking system to monitor progress and ensure compliance with laboratory protocols.`
      };
    }

    // Test availability and analytical methods
    if (msgLower.includes('test') && (msgLower.includes('available') || msgLower.includes('hplc') || msgLower.includes('gc') || msgLower.includes('uv'))) {
      return {
        type: 'text',
        title: '🔬 Available Analytical Tests',
        content: `Current Laboratory Testing Capabilities:

🧬 Analytical Methods:
• HPLC (High-Performance Liquid Chromatography)
• GC-MS (Gas Chromatography-Mass Spectrometry) 
• UV-VIS Spectrophotometry
• Complete Blood Count (CBC)
• Blood Chemistry Profile
• Molecular Diagnostics (PCR, DNA sequencing)

⚗️ Sample Types Supported:
• Biological samples (blood, urine, tissue)
• Chemical compounds and mixtures
• Environmental samples
• Pharmaceutical formulations

📊 Turnaround Times:
• Routine: 24-48 hours
• Urgent: 4-8 hours
• Molecular: 2-5 days

📞 Contact lab scheduling to book tests`
      };
    }

    // Workflow and protocol management
    if (msgLower.includes('workflow') || msgLower.includes('protocol') || msgLower.includes('procedure')) {
      return {
        type: 'text',
        title: '📋 Laboratory Workflow Management',
        content: `Laboratory Workflow Options:

🔄 Standard Workflows:
• Sample Receipt & Accessioning
• Quality Control Testing
• Method Validation Protocol
• Instrument Calibration
• Data Review & Approval

⚡ Automated Processes:
• Sample tracking and chain of custody
• Result reporting and notifications
• Compliance documentation
• Equipment maintenance scheduling

🎯 Optimization Tips:
• Batch similar samples for efficiency
• Schedule preventive maintenance
• Use barcode scanning for accuracy
• Implement electronic signatures

📈 Monitor workflow metrics in real-time`
      };
    }

    // Quality control and compliance
    if (msgLower.includes('quality') || msgLower.includes('qc') || msgLower.includes('compliance') || msgLower.includes('validation')) {
      return {
        type: 'text',
        title: '✅ Quality Control & Compliance',
        content: `Quality Assurance Framework:

🎯 QC Requirements:
• Control sample analysis with each batch
• Method validation and verification
• Instrument performance checks
• Analyst competency assessment

📊 Statistical Controls:
• Levey-Jennings charts for trending
• Westgard rules for error detection
• Control limits and alert thresholds
• Corrective action procedures

📑 Compliance Standards:
• ISO 15189 (Medical laboratories)
• CAP/CLIA requirements
• FDA regulations (if applicable)
• Internal quality policies

🔍 Audit Trail:
• Complete documentation chain
• Electronic signatures and timestamps
• Change control procedures
• Regular management review`
      };
    }

    // Instrument and equipment
    if (msgLower.includes('instrument') || msgLower.includes('equipment') || msgLower.includes('calibration') || msgLower.includes('maintenance')) {
      return {
        type: 'text',
        title: '⚙️ Instrument Management',
        content: `Laboratory Equipment Status:

🔧 Maintenance Schedule:
• Daily: Performance checks and QC
• Weekly: Cleaning and inspection
• Monthly: Calibration verification
• Quarterly: Preventive maintenance

📈 Performance Monitoring:
• Instrument uptime and availability
• Calibration curve correlation
• Control sample recovery
• Error log analysis

🎯 Calibration Standards:
• Reference materials traceability
• Calibration frequency requirements
• Measurement uncertainty assessment
• Out-of-specification investigations

📊 Equipment Utilization:
• Sample throughput metrics
• Resource allocation optimization
• Capacity planning and scheduling
• Cost per test analysis`
      };
    }

    // Data analysis and reporting
    if (msgLower.includes('data') || msgLower.includes('report') || msgLower.includes('result') || msgLower.includes('analysis')) {
      return {
        type: 'text',
        title: '📊 Data Analysis & Reporting',
        content: `Laboratory Data Management:

📈 Analysis Capabilities:
• Statistical analysis and trending
• Outlier detection and investigation
• Method comparison studies
• Control chart interpretation

📋 Report Generation:
• Individual test reports
• Batch summary reports
• Quality control summaries
• Management dashboards

🔍 Data Integrity:
• Electronic data capture
• Audit trail maintenance
• Data backup and recovery
• Access control and security

📊 Visualization Options:
• Real-time dashboards
• Trend analysis charts
• Control charts and histograms
• Custom report templates

💾 Export formats: PDF, Excel, CSV, LIMS integration`
      };
    }

    // Safety and emergency procedures
    if (msgLower.includes('safety') || msgLower.includes('emergency') || msgLower.includes('hazard') || msgLower.includes('incident')) {
      return {
        type: 'text',
        title: '🚨 Laboratory Safety & Emergency Procedures',
        content: `Safety Management System:

⚠️ Hazard Assessment:
• Chemical safety data sheets (SDS)
• Biological risk categories
• Physical hazard identification
• Personal protective equipment (PPE)

🚨 Emergency Procedures:
• Chemical spill response
• Fire evacuation protocols
• Medical emergency procedures
• Equipment failure protocols

📋 Incident Reporting:
• Near-miss documentation
• Accident investigation
• Root cause analysis
• Corrective action tracking

🎓 Training Requirements:
• Initial safety orientation
• Ongoing competency assessment
• Emergency drill participation
• Documentation and certification

📞 Emergency Contacts: Extension 911 (Internal), 911 (External)`
      };
    }

    // General help or greeting
    if (userMsgLower.includes('hello') || userMsgLower.includes('help') || msgLower.includes('assist') || msgLower.includes('main interface agent')) {
      return {
        type: 'text',
        title: '🤖 ALIMS Main Interface Agent',
        content: `Welcome to the Advanced Laboratory Information Management System!

🎯 I can help you with:

🧪 Sample Management:
• Sample registration and tracking
• Chain of custody documentation
• Test scheduling and prioritization

🔬 Analytical Services:
• Available test methods and capabilities
• Turnaround times and scheduling
• Quality control requirements

📋 Workflow Optimization:
• Protocol development and validation
• Process automation recommendations
• Resource allocation planning

📊 Data & Reporting:
• Result interpretation and trending
• Custom report generation
• Compliance documentation

⚙️ System Management:
• Instrument status and maintenance
• User access and permissions
• System configuration

💡 Just ask me about any laboratory operation, and I'll provide specific guidance and relevant options!`
      };
    }

    // Default: Show general laboratory options
    return {
      type: 'text',
      title: '🔬 Laboratory Operations Center',
      content: `Laboratory Management Options:

🧪 Sample Operations:
• Track samples through the workflow
• Schedule tests and assign priorities
• Monitor turnaround times

📊 Quality Management:
• Review control charts and trends
• Investigate out-of-specification results
• Generate compliance reports

⚙️ Instrument Management:
• Check equipment status and schedules
• Review calibration and maintenance
• Monitor performance metrics

📋 Workflow Optimization:
• Analyze process efficiency
• Identify bottlenecks and delays
• Implement improvement strategies

💡 Ask me about specific laboratory operations for detailed guidance and actionable insights.`
    };
  };

  return (
    <div className="flex flex-col h-full">
      {/* Chat Header with Clear Button */}
      <div className="p-2 border-b border-gray-700 bg-gray-800 flex justify-between items-center">
        <span className="text-xs text-gray-400">
          {conversationId ? `Conversation: ${conversationId.slice(0, 8)}...` : 'Connecting...'}
        </span>
        <button
          onClick={clearChat}
          className="px-2 py-1 text-xs bg-gray-600 hover:bg-gray-500 text-white rounded"
        >
          Clear Chat
        </button>
      </div>

      <div className="flex-1 overflow-auto p-4 space-y-4">
        {messages.map((msg, idx) => (
          <div key={idx} className={cn(
            "flex",
            msg.role === 'agent' ? 'justify-start' : 'justify-end'
          )}>
            <div className={cn(
              "max-w-xs p-3 rounded-lg",
              msg.role === 'agent' ? 'bg-gray-700 text-gray-200' : 'bg-blue-600 text-white'
            )}>
              {renderMessageContent(msg)}
              <div className="text-xs text-gray-500 mt-1 text-right">
                {new Date(msg.timestamp).toLocaleTimeString()}
                {msg.agent_source && msg.agent_source !== 'system' && (
                  <span className="ml-2 text-gray-600">({msg.agent_source})</span>
                )}
              </div>
            </div>
          </div>
        ))}
        <div ref={messagesEndRef} />
      </div>

      <div className="p-4 border-t border-gray-700 bg-gray-800 flex">
        <textarea
          className="flex-1 resize-none p-2 bg-gray-900 text-white rounded mr-2"
          rows={1}
          value={input}
          onChange={e => setInput(e.target.value)}
          onKeyPress={handleKeyPress}
          placeholder="Type your message..."
        />
        <button
          onClick={() => sendMessage()}
          className="px-4 bg-blue-600 hover:bg-blue-700 text-white rounded"
          disabled={isLoading}
        >
          {isLoading ? 'Sending...' : 'Send'}
        </button>
      </div>
    </div>
  );
}
