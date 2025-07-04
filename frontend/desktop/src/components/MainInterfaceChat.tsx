import React, { useState, useRef, useEffect } from 'react';
import { MainInterfaceAgentClient } from '../services/mainInterfaceClient';
import { cn } from '../utils/cn';
import { SampleRegistrationForm, WorkflowStatus, QuickActions } from './WorkflowComponents';

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

interface WorkflowState {
  current_workflow?: string;
  step?: number;
  data?: any;
  ui_component?: string;
}

// Enhanced agent intelligence to understand user intent
function analyzeUserIntent(message: string): {
  intent: string;
  messageType: string;
  suggestedComponent?: string;
  quickActions?: Array<{label: string; action: string; icon?: string}>;
} {
  const lowerMessage = message.toLowerCase();
  
  // Sample-related intents
  if (lowerMessage.includes('register') && (lowerMessage.includes('sample') || lowerMessage.includes('specimen'))) {
    return {
      intent: 'register_sample',
      messageType: 'SAMPLE_INQUIRY',
      suggestedComponent: 'sample_registration',
      quickActions: [
        { label: 'Register Sample', action: 'show_sample_form', icon: '🧪' },
        { label: 'Bulk Import', action: 'bulk_import', icon: '📁' },
        { label: 'Sample Status', action: 'sample_status', icon: '📊' },
        { label: 'Recent Samples', action: 'recent_samples', icon: '📋' }
      ]
    };
  }
  
  // Workflow-related intents
  if (lowerMessage.includes('workflow') || lowerMessage.includes('process') || lowerMessage.includes('procedure')) {
    return {
      intent: 'workflow_management',
      messageType: 'WORKFLOW_COMMAND',
      quickActions: [
        { label: 'Create Workflow', action: 'create_workflow', icon: '⚙️' },
        { label: 'View Active', action: 'active_workflows', icon: '🔄' },
        { label: 'Templates', action: 'workflow_templates', icon: '📝' },
        { label: 'Analytics', action: 'workflow_analytics', icon: '📈' }
      ]
    };
  }
  
  // System status and monitoring
  if (lowerMessage.includes('status') || lowerMessage.includes('monitor') || lowerMessage.includes('health')) {
    return {
      intent: 'system_monitoring',
      messageType: 'SYSTEM_QUERY',
      quickActions: [
        { label: 'System Health', action: 'system_health', icon: '💚' },
        { label: 'Agent Status', action: 'agent_status', icon: '🤖' },
        { label: 'Performance', action: 'performance_metrics', icon: '⚡' },
        { label: 'Alerts', action: 'system_alerts', icon: '🚨' }
      ]
    };
  }
  
  // Testing and QC
  if (lowerMessage.includes('test') || lowerMessage.includes('qc') || lowerMessage.includes('quality')) {
    return {
      intent: 'testing_qc',
      messageType: 'WORKFLOW_COMMAND',
      quickActions: [
        { label: 'Run Tests', action: 'run_tests', icon: '🔬' },
        { label: 'QC Results', action: 'qc_results', icon: '✅' },
        { label: 'Calibration', action: 'calibration', icon: '⚖️' },
        { label: 'Test Schedule', action: 'test_schedule', icon: '📅' }
      ]
    };
  }
  
  // Default to general inquiry
  return {
    intent: 'general_inquiry',
    messageType: 'SYSTEM_QUERY'
  };
}

export default function MainInterfaceChat(props: MainInterfaceChatProps = {}) {
  const { onVisualizationUpdate } = props;
  const [messages, setMessages] = useState<Message[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [input, setInput] = useState('');
  const [conversationId, setConversationId] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [currentWorkflow, setCurrentWorkflow] = useState<WorkflowState | null>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);
  
  const client = new MainInterfaceAgentClient();

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
    try {
      setError(null);
      const response = await client.startConversation();
      if (response.success && response.data) {
        setConversationId(response.data.conversation_id);
        setMessages([{
          role: 'agent',
          content: 'Hello! I\'m the ALIMS Main Interface Agent. I can help you with any laboratory task. Try saying things like:\n\n• "Let\'s register some samples"\n• "Show me workflow status"\n• "Check system health"\n• "Run quality control tests"\n\nWhat would you like to do today?',
          timestamp: new Date().toISOString(),
          ui_component: 'quick_actions',
          data: {
            actions: [
              { label: 'Register Samples', action: 'register_samples', icon: '🧪' },
              { label: 'View Workflows', action: 'view_workflows', icon: '⚙️' },
              { label: 'System Status', action: 'system_status', icon: '💚' },
              { label: 'Run Tests', action: 'run_tests', icon: '🔬' }
            ]
          }
        }]);
      } else {
        setError(response.error || 'Failed to start conversation');
      }
    } catch (err) {
      setError(`Failed to start conversation: ${err}`);
    }
  };

  const handleQuickAction = async (action: string) => {
    const actionMap: Record<string, string> = {
      'register_samples': 'Let\'s register some samples',
      'view_workflows': 'Show me current workflows',
      'system_status': 'What\'s the system status?',
      'run_tests': 'I need to run some tests',
      'show_sample_form': 'Show me the sample registration form',
      'bulk_import': 'I want to do bulk sample import',
      'sample_status': 'Check sample status',
      'recent_samples': 'Show recent samples'
    };

    const message = actionMap[action] || action;
    setInput(message);
    await sendMessage(message);
  };

  const handleSampleSubmit = async (sample: any) => {
    // Simulate sample registration
    const message = `Register sample: Patient ${sample.patientId}, Type: ${sample.sampleType}, Priority: ${sample.priority}, Tests: ${sample.testsRequested.join(', ')}`;
    await sendMessage(message);
    setCurrentWorkflow(null);
  };

  const sendMessage = async (messageText?: string) => {
    const messageToSend = messageText || input.trim();
    if (!messageToSend || !conversationId || isLoading) {
      return;
    }

    // Analyze user intent
    const intent = analyzeUserIntent(messageToSend);

    const userMessage: Message = {
      role: 'user',
      content: messageToSend,
      timestamp: new Date().toISOString()
    };

    setMessages(prev => [...prev, userMessage]);
    if (!messageText) setInput('');
    setIsLoading(true);
    setError(null);

    try {
      const response = await client.sendMessage(
        conversationId,
        messageToSend,
        intent.messageType,
        'MEDIUM'
      );

      if (response.success && response.data) {
        // Enhanced response with UI components based on intent
        const enhancedMessages = response.data.messages.map(msg => {
          if (msg.role === 'agent') {
            // Add UI component based on user intent
            const enhanced: Message = {
              ...msg,
              ui_component: intent.suggestedComponent,
              data: intent.quickActions ? { actions: intent.quickActions } : undefined
            };

            // Special handling for sample registration
            if (intent.intent === 'register_sample' && intent.suggestedComponent === 'sample_registration') {
              enhanced.content += '\n\nI\'ve prepared the sample registration form for you. Please fill in the details below:';
            }

            return enhanced;
          }
          return msg;
        });

        setMessages(enhancedMessages);

        // Update workflow state if needed
        if (intent.intent === 'register_sample') {
          setCurrentWorkflow({
            current_workflow: 'Sample Registration',
            step: 1,
            ui_component: 'sample_registration'
          });
        }
      } else {
        setError(response.error || 'Failed to send message');
      }
    } catch (err) {
      setError(`Failed to send message: ${err}`);
    } finally {
      setIsLoading(false);
    }
  };

  const handleKeyPress = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      sendMessage();
    }
  };

  const handleSendClick = () => {
    sendMessage();
  };

  const renderMessageContent = (message: Message) => {
    return (
      <div className="space-y-3">
        <p className="text-sm">{message.content}</p>
        
        {/* Render UI components based on message */}
        {message.ui_component === 'sample_registration' && currentWorkflow?.ui_component === 'sample_registration' && (
          <SampleRegistrationForm
            onSubmit={handleSampleSubmit}
            onCancel={() => setCurrentWorkflow(null)}
          />
        )}
        
        {message.ui_component === 'quick_actions' && message.data?.actions && (
          <QuickActions
            actions={message.data.actions}
            onAction={handleQuickAction}
          />
        )}
        
        {message.ui_component === 'workflow_status' && message.data && (
          <WorkflowStatus
            workflow={message.data.workflow}
            currentStep={message.data.currentStep}
            steps={message.data.steps}
            data={message.data.workflowData}
          />
        )}
        
        <p className={cn(
          "text-xs mt-1",
          message.role === 'user' 
            ? 'text-blue-100' 
            : 'text-gray-500 dark:text-gray-400'
        )}>
          {new Date(message.timestamp).toLocaleTimeString()}
          {message.agent_source && (
            <span className="ml-2">• {message.agent_source}</span>
          )}
        </p>
      </div>
    );
  };

  return (
    <div className="flex flex-col h-full bg-gradient-to-br from-blue-50 to-indigo-100 dark:from-gray-900 dark:to-gray-800">
      {/* Header */}
      <div className="bg-white dark:bg-gray-800 border-b border-gray-200 dark:border-gray-700 p-4 shadow-sm">
        <div className="flex items-center justify-between">
          <div>
            <h2 className="text-xl font-semibold text-gray-900 dark:text-white">
              ALIMS Main Interface Agent
            </h2>
            <p className="text-sm text-gray-600 dark:text-gray-400">
              Formally verified TLA+ agent for laboratory management
            </p>
          </div>
          <div className="flex items-center space-x-2">
            <div className={cn(
              "w-3 h-3 rounded-full",
              conversationId ? "bg-green-500" : "bg-red-500"
            )} />
            <span className="text-sm text-gray-600 dark:text-gray-400">
              {conversationId ? 'Connected' : 'Disconnected'}
            </span>
          </div>
        </div>
      </div>

      {/* Error Banner */}
      {error && (
        <div className="bg-red-100 border border-red-400 text-red-700 px-4 py-3 m-4 rounded">
          <p>{error}</p>
          <button 
            onClick={startNewConversation}
            className="mt-2 px-3 py-1 bg-red-500 text-white rounded text-sm hover:bg-red-600"
          >
            Retry Connection
          </button>
        </div>
      )}

      {/* Messages */}
      <div className="flex-1 overflow-y-auto p-4 space-y-4">
        {messages.map((message, index) => (
          <div
            key={index}
            className={cn(
              "flex",
              message.role === 'user' ? 'justify-end' : 'justify-start'
            )}
          >
            <div
              className={cn(
                "max-w-4xl px-4 py-2 rounded-lg shadow",
                message.role === 'user'
                  ? 'bg-blue-500 text-white'
                  : 'bg-white dark:bg-gray-700 text-gray-900 dark:text-white border border-gray-200 dark:border-gray-600'
              )}
            >
              {renderMessageContent(message)}
            </div>
          </div>
        ))}
        
        {isLoading && (
          <div className="flex justify-start">
            <div className="bg-white dark:bg-gray-700 rounded-lg p-4 shadow border border-gray-200 dark:border-gray-600">
              <div className="flex items-center space-x-2">
                <div className="w-2 h-2 bg-blue-500 rounded-full animate-bounce"></div>
                <div className="w-2 h-2 bg-blue-500 rounded-full animate-bounce" style={{ animationDelay: '0.1s' }}></div>
                <div className="w-2 h-2 bg-blue-500 rounded-full animate-bounce" style={{ animationDelay: '0.2s' }}></div>
              </div>
            </div>
          </div>
        )}
        
        <div ref={messagesEndRef} />
      </div>

      {/* Input */}
      <div className="bg-white dark:bg-gray-800 border-t border-gray-200 dark:border-gray-700 p-4">
        <div className="flex items-center space-x-2">
          <input
            type="text"
            value={input}
            onChange={(e) => setInput(e.target.value)}
            onKeyPress={handleKeyPress}
            placeholder="Ask about samples, workflows, or system status..."
            disabled={!conversationId || isLoading}
            className="flex-1 px-3 py-2 border border-gray-300 dark:border-gray-600 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 dark:bg-gray-700 dark:text-white disabled:opacity-50"
          />
          <button
            onClick={handleSendClick}
            disabled={!input.trim() || !conversationId || isLoading}
            className="px-4 py-2 bg-blue-500 text-white rounded-md hover:bg-blue-600 focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            Send
          </button>
        </div>
        <p className="text-xs text-gray-500 dark:text-gray-400 mt-2">
          Press Enter to send. Try asking about "ALIMS capabilities", "sample tracking", or "workflow management".
        </p>
      </div>
    </div>
  );
}
