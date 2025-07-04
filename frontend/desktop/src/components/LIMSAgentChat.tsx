import React, { useState, useRef, useEffect } from 'react';
import { invoke } from '@tauri-apps/api/core';
import { cn } from '../utils/cn';

// LIMS-specific types
export interface Sample {
  sample_id: string;
  patient_id: string;
  state: 'RECEIVED' | 'ACCESSIONED' | 'SCHEDULED' | 'TESTING' | 'QC_PENDING' | 'QC_APPROVED' | 'REPORTED' | 'ARCHIVED';
  barcode?: string;
  accession_number?: string;
  received_at: string;
  sample_type: string;
  tests_requested: string[];
  priority: 'ROUTINE' | 'URGENT' | 'STAT';
  location?: string;
}

export interface LIMSAgent {
  agent_id: string;
  name: string;
  specialization: string;
  state_handled: string;
  personality_traits: Record<string, number>;
  status: 'ACTIVE' | 'BUSY' | 'IDLE';
  current_tasks: number;
}

export interface SampleNotification {
  id: string;
  type: 'SAMPLE_ARRIVED' | 'URGENT_SAMPLE' | 'BATCH_COMPLETE' | 'QC_ISSUE';
  message: string;
  sample_id?: string;
  timestamp: string;
  priority: 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL';
  requires_action: boolean;
}

export interface LIMSConversation {
  id: string;
  agent: LIMSAgent;
  sample_context?: Sample;
  messages: Array<{
    role: 'user' | 'agent';
    content: string;
    timestamp: string;
    action_suggestions?: string[];
    workflow_context?: {
      current_state: string;
      next_states: string[];
      required_actions: string[];
    };
  }>;
  status: 'ACTIVE' | 'COMPLETED' | 'ESCALATED';
}

interface LIMSAgentChatProps {
  className?: string;
}

export const LIMSAgentChat: React.FC<LIMSAgentChatProps> = ({ className }) => {
  const [conversations, setConversations] = useState<LIMSConversation[]>([]);
  const [activeConversation, setActiveConversation] = useState<string | null>(null);
  const [notifications, setNotifications] = useState<SampleNotification[]>([]);
  const [availableAgents, setAvailableAgents] = useState<LIMSAgent[]>([]);
  const [samples, setSamples] = useState<Sample[]>([]);
  const [input, setInput] = useState('');
  const [isLoading, setIsLoading] = useState(false);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  // Initialize LIMS system
  useEffect(() => {
    const initLIMS = async () => {
      try {
        // Load available agents
        const agents = await invoke<LIMSAgent[]>('get_lims_agents');
        setAvailableAgents(agents || []);

        // Load pending samples
        const pendingSamples = await invoke<Sample[]>('get_pending_samples');
        setSamples(pendingSamples || []);

        // Check for notifications
        const activeNotifications = await invoke<SampleNotification[]>('get_sample_notifications');
        setNotifications(activeNotifications || []);
      } catch (err) {
        console.error('Failed to initialize LIMS:', err);
      }
    };

    initLIMS();
    
    // Poll for updates every 30 seconds
    const interval = setInterval(initLIMS, 30000);
    return () => clearInterval(interval);
  }, []);

  // Auto-scroll to bottom
  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  useEffect(() => {
    scrollToBottom();
  }, [conversations]);

  // Handle new sample arrival
  const handleSampleArrival = async (sampleData: Partial<Sample>) => {
    try {
      setIsLoading(true);
      
      // Create new sample
      const newSample = await invoke<Sample>('register_new_sample', { sampleData });
      setSamples(prev => [...prev, newSample]);

      // Find appropriate agent for reception
      const receptionAgent = availableAgents.find(
        agent => agent.specialization === 'sample_reception' && agent.status === 'IDLE'
      );

      if (receptionAgent) {
        // Start conversation with reception agent
        const conversationId = `conv_${Date.now()}`;
        const newConversation: LIMSConversation = {
          id: conversationId,
          agent: receptionAgent,
          sample_context: newSample,
          messages: [{
            role: 'agent',
            content: `Hello! I'm ${receptionAgent.name}, and I see we have a new sample that just arrived. Let me help you process it.

📋 **Sample Details:**
- Sample ID: ${newSample.sample_id}
- Patient ID: ${newSample.patient_id}
- Sample Type: ${newSample.sample_type}
- Priority: ${newSample.priority}
- Tests Requested: ${newSample.tests_requested.join(', ')}

I'm ready to help you verify the sample information, generate barcodes, and move it to the next step. What would you like to do?`,
            timestamp: new Date().toLocaleTimeString(),
            action_suggestions: [
              "Verify sample information",
              "Generate barcode",
              "Move to accessioning",
              "Flag as urgent"
            ],
            workflow_context: {
              current_state: 'RECEIVED',
              next_states: ['ACCESSIONED'],
              required_actions: ['Verify patient info', 'Generate barcode', 'Assign accession number']
            }
          }],
          status: 'ACTIVE'
        };

        setConversations(prev => [...prev, newConversation]);
        setActiveConversation(conversationId);

        // Add notification
        const notification: SampleNotification = {
          id: `notif_${Date.now()}`,
          type: newSample.priority === 'STAT' ? 'URGENT_SAMPLE' : 'SAMPLE_ARRIVED',
          message: `New ${newSample.priority.toLowerCase()} sample arrived: ${newSample.sample_id}`,
          sample_id: newSample.sample_id,
          timestamp: new Date().toLocaleTimeString(),
          priority: newSample.priority === 'STAT' ? 'CRITICAL' : 'MEDIUM',
          requires_action: true
        };
        setNotifications(prev => [...prev, notification]);
      }
    } catch (err) {
      console.error('Failed to handle sample arrival:', err);
    } finally {
      setIsLoading(false);
    }
  };

  // Send message to agent
  const handleSendMessage = async () => {
    if (!input.trim() || !activeConversation) return;

    const conversation = conversations.find(c => c.id === activeConversation);
    if (!conversation) return;

    try {
      setIsLoading(true);

      // Add user message
      const userMessage = {
        role: 'user' as const,
        content: input.trim(),
        timestamp: new Date().toLocaleTimeString()
      };

      setConversations(prev => prev.map(c => 
        c.id === activeConversation 
          ? { ...c, messages: [...c.messages, userMessage] }
          : c
      ));

      setInput('');

      // Send to LIMS agent
      const response = await invoke<{
        content: string;
        action_suggestions: string[];
        workflow_context: {
          current_state: string;
          next_states: string[];
          required_actions: string[];
        };
        sample_update?: Sample;
      }>('send_lims_message', {
        conversationId: activeConversation,
        message: userMessage.content,
        agentId: conversation.agent.agent_id,
        sampleContext: conversation.sample_context
      });

      // Add agent response
      const agentMessage = {
        role: 'agent' as const,
        content: response.content,
        timestamp: new Date().toLocaleTimeString(),
        action_suggestions: response.action_suggestions,
        workflow_context: response.workflow_context
      };

      setConversations(prev => prev.map(c => 
        c.id === activeConversation 
          ? { 
              ...c, 
              messages: [...c.messages, agentMessage],
              sample_context: response.sample_update || c.sample_context
            }
          : c
      ));

      // Update sample if changed
      if (response.sample_update) {
        setSamples(prev => prev.map(s => 
          s.sample_id === response.sample_update!.sample_id 
            ? response.sample_update!
            : s
        ));
      }

    } catch (err) {
      console.error('Failed to send message:', err);
    } finally {
      setIsLoading(false);
    }
  };

  // Quick action buttons for common LIMS tasks
  const quickActions = [
    { label: "New Sample Arrived", action: () => {
      const mockSample = {
        sample_id: `SAM${Date.now()}`,
        patient_id: `PAT${Math.floor(Math.random() * 10000)}`,
        sample_type: "Blood",
        tests_requested: ["CBC", "BMP"],
        priority: "ROUTINE" as const
      };
      handleSampleArrival(mockSample);
    }},
    { label: "Urgent Sample", action: () => {
      const urgentSample = {
        sample_id: `STAT${Date.now()}`,
        patient_id: `PAT${Math.floor(Math.random() * 10000)}`,
        sample_type: "Blood",
        tests_requested: ["Troponin", "CBC"],
        priority: "STAT" as const
      };
      handleSampleArrival(urgentSample);
    }},
    { label: "Batch Processing", action: () => setInput("I need help processing a batch of samples") },
    { label: "QC Issue", action: () => setInput("There's a quality control issue with sample results") }
  ];

  const activeConv = conversations.find(c => c.id === activeConversation);

  return (
    <div className={cn('flex h-screen bg-gray-50 dark:bg-gray-900', className)}>
      {/* Sidebar - Notifications & Agents */}
      <div className="w-80 bg-white dark:bg-gray-800 border-r border-gray-200 dark:border-gray-700 flex flex-col">
        {/* Header */}
        <div className="p-4 border-b border-gray-200 dark:border-gray-700">
          <h2 className="text-lg font-semibold text-gray-800 dark:text-white flex items-center">
            🧪 LIMS Agent Assistant
          </h2>
          <div className="text-sm text-gray-600 dark:text-gray-400 mt-1">
            {availableAgents.filter(a => a.status === 'ACTIVE').length} agents active
          </div>
        </div>

        {/* Quick Actions */}
        <div className="p-4 border-b border-gray-200 dark:border-gray-700">
          <h3 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">Quick Actions</h3>
          <div className="space-y-2">
            {quickActions.map((action, index) => (
              <button
                key={index}
                onClick={action.action}
                className={cn(
                  'w-full text-left px-3 py-2 rounded-lg text-sm',
                  'bg-blue-50 dark:bg-blue-900/20 hover:bg-blue-100 dark:hover:bg-blue-900/40',
                  'text-blue-700 dark:text-blue-300 transition-colors'
                )}
              >
                {action.label}
              </button>
            ))}
          </div>
        </div>

        {/* Notifications */}
        <div className="p-4 border-b border-gray-200 dark:border-gray-700">
          <h3 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">Notifications</h3>
          <div className="space-y-2 max-h-32 overflow-y-auto">
            {notifications.length === 0 ? (
              <div className="text-xs text-gray-500 dark:text-gray-400">No new notifications</div>
            ) : (
              notifications.map((notif) => (
                <div
                  key={notif.id}
                  className={cn(
                    'p-2 rounded-lg text-xs',
                    notif.priority === 'CRITICAL' && 'bg-red-50 dark:bg-red-900/20 text-red-700 dark:text-red-300',
                    notif.priority === 'HIGH' && 'bg-orange-50 dark:bg-orange-900/20 text-orange-700 dark:text-orange-300',
                    notif.priority === 'MEDIUM' && 'bg-yellow-50 dark:bg-yellow-900/20 text-yellow-700 dark:text-yellow-300',
                    notif.priority === 'LOW' && 'bg-green-50 dark:bg-green-900/20 text-green-700 dark:text-green-300'
                  )}
                >
                  <div className="font-medium">{notif.message}</div>
                  <div className="text-xs opacity-75 mt-1">{notif.timestamp}</div>
                </div>
              ))
            )}
          </div>
        </div>

        {/* Active Conversations */}
        <div className="flex-1 p-4 overflow-y-auto">
          <h3 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">Conversations</h3>
          <div className="space-y-2">
            {conversations.map((conv) => (
              <button
                key={conv.id}
                onClick={() => setActiveConversation(conv.id)}
                className={cn(
                  'w-full text-left p-3 rounded-lg border transition-colors',
                  activeConversation === conv.id
                    ? 'bg-blue-50 dark:bg-blue-900/20 border-blue-200 dark:border-blue-700'
                    : 'bg-gray-50 dark:bg-gray-700 border-gray-200 dark:border-gray-600 hover:bg-gray-100 dark:hover:bg-gray-600'
                )}
              >
                <div className="text-sm font-medium text-gray-800 dark:text-white">
                  {conv.agent.name}
                </div>
                <div className="text-xs text-gray-600 dark:text-gray-400">
                  {conv.sample_context?.sample_id || 'General chat'}
                </div>
                <div className="text-xs text-gray-500 dark:text-gray-500 mt-1">
                  {conv.messages.length} messages
                </div>
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* Main Chat Area */}
      <div className="flex-1 flex flex-col">
        {activeConv ? (
          <>
            {/* Chat Header */}
            <div className="p-4 border-b border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800">
              <div className="flex items-center justify-between">
                <div>
                  <h3 className="text-lg font-medium text-gray-800 dark:text-white">
                    {activeConv.agent.name}
                  </h3>
                  <div className="text-sm text-gray-600 dark:text-gray-400">
                    {activeConv.agent.specialization} • {activeConv.sample_context?.sample_id || 'General Assistant'}
                  </div>
                </div>
                {activeConv.sample_context && (
                  <div className="text-right">
                    <div className={cn(
                      'inline-block px-3 py-1 rounded-full text-xs font-medium',
                      activeConv.sample_context.state === 'RECEIVED' && 'bg-blue-100 text-blue-800',
                      activeConv.sample_context.state === 'ACCESSIONED' && 'bg-green-100 text-green-800',
                      activeConv.sample_context.state === 'TESTING' && 'bg-yellow-100 text-yellow-800'
                    )}>
                      {activeConv.sample_context.state}
                    </div>
                    <div className="text-xs text-gray-500 dark:text-gray-400 mt-1">
                      {activeConv.sample_context.priority} Priority
                    </div>
                  </div>
                )}
              </div>
            </div>

            {/* Messages */}
            <div className="flex-1 overflow-y-auto p-4 space-y-4">
              {activeConv.messages.map((message, index) => (
                <div
                  key={index}
                  className={cn(
                    'flex flex-col max-w-[80%]',
                    message.role === 'user' ? 'ml-auto' : 'mr-auto'
                  )}
                >
                  <div
                    className={cn(
                      'rounded-lg p-4',
                      message.role === 'user'
                        ? 'bg-blue-500 text-white'
                        : 'bg-white dark:bg-gray-700 border border-gray-200 dark:border-gray-600'
                    )}
                  >
                    <div className="text-sm whitespace-pre-wrap">{message.content}</div>
                    <div className={cn(
                      'text-xs mt-2',
                      message.role === 'user' 
                        ? 'text-blue-100' 
                        : 'text-gray-500 dark:text-gray-400'
                    )}>
                      {message.timestamp}
                    </div>
                  </div>

                  {/* Action suggestions */}
                  {message.action_suggestions && message.action_suggestions.length > 0 && (
                    <div className="mt-2 space-y-1">
                      {message.action_suggestions.map((action, actionIndex) => (
                        <button
                          key={actionIndex}
                          onClick={() => setInput(action)}
                          className={cn(
                            'text-xs px-3 py-1 rounded-full',
                            'bg-gray-100 dark:bg-gray-600 hover:bg-gray-200 dark:hover:bg-gray-500',
                            'text-gray-700 dark:text-gray-200 transition-colors mr-2'
                          )}
                        >
                          {action}
                        </button>
                      ))}
                    </div>
                  )}

                  {/* Workflow context */}
                  {message.workflow_context && (
                    <div className="mt-2 p-3 bg-gray-50 dark:bg-gray-800 rounded-lg text-xs">
                      <div className="font-medium text-gray-700 dark:text-gray-300 mb-1">
                        Workflow Status
                      </div>
                      <div className="text-gray-600 dark:text-gray-400">
                        Current: {message.workflow_context.current_state}
                      </div>
                      {message.workflow_context.next_states.length > 0 && (
                        <div className="text-gray-600 dark:text-gray-400">
                          Next: {message.workflow_context.next_states.join(', ')}
                        </div>
                      )}
                    </div>
                  )}
                </div>
              ))}
              <div ref={messagesEndRef} />
            </div>

            {/* Input */}
            <div className="p-4 border-t border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800">
              <div className="flex space-x-2">
                <textarea
                  value={input}
                  onChange={(e) => setInput(e.target.value)}
                  onKeyPress={(e) => {
                    if (e.key === 'Enter' && !e.shiftKey) {
                      e.preventDefault();
                      handleSendMessage();
                    }
                  }}
                  placeholder="Type your message to the agent..."
                  className={cn(
                    'flex-1 p-3 rounded-lg border border-gray-200 dark:border-gray-600',
                    'focus:outline-none focus:ring-2 focus:ring-blue-500',
                    'bg-white dark:bg-gray-700 text-gray-800 dark:text-white',
                    'resize-none'
                  )}
                  rows={2}
                  disabled={isLoading}
                />
                <button
                  onClick={handleSendMessage}
                  disabled={!input.trim() || isLoading}
                  className={cn(
                    'px-6 py-3 rounded-lg bg-blue-500 text-white',
                    'hover:bg-blue-600 transition-colors',
                    'disabled:opacity-50 disabled:cursor-not-allowed'
                  )}
                >
                  {isLoading ? '...' : 'Send'}
                </button>
              </div>
            </div>
          </>
        ) : (
          /* No conversation selected */
          <div className="flex-1 flex items-center justify-center bg-gray-50 dark:bg-gray-900">
            <div className="text-center">
              <div className="text-6xl mb-4">🧪</div>
              <h3 className="text-xl font-medium text-gray-800 dark:text-white mb-2">
                Welcome to LIMS Agent Chat
              </h3>
              <p className="text-gray-600 dark:text-gray-400 mb-6 max-w-md">
                Start a conversation with a LIMS agent when new samples arrive, or use quick actions to simulate common lab scenarios.
              </p>
              <div className="space-y-2">
                {quickActions.slice(0, 2).map((action, index) => (
                  <button
                    key={index}
                    onClick={action.action}
                    className={cn(
                      'px-6 py-3 rounded-lg bg-blue-500 text-white',
                      'hover:bg-blue-600 transition-colors block mx-auto'
                    )}
                  >
                    {action.label}
                  </button>
                ))}
              </div>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default LIMSAgentChat;
