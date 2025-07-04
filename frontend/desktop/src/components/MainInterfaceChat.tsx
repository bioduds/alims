import React, { useState, useRef, useEffect } from 'react';
import { MainInterfaceAgentClient } from '../services/mainInterfaceClient';
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
    console.log('Starting conversation...');
    try {
      const response = await client.startConversation();
      console.log('Conversation response:', response);
      if (response.success && response.data) {
        setConversationId(response.data.conversation_id);
        setMessages([
          {
            role: 'agent',
            content: `Hello! I am the ALIMS Main Interface Agent. How can I assist you today?`,
            timestamp: new Date().toISOString(),
            agent_source: 'system'
          }
        ]);
        console.log('Conversation started with ID:', response.data.conversation_id);
      } else {
        console.error('Failed to start conversation:', response.error);
        setMessages([
          {
            role: 'agent',
            content: 'Error: Failed to connect to Main Interface Agent. Please check if the backend is running.',
            timestamp: new Date().toISOString(),
            agent_source: 'error'
          }
        ]);
      }
    } catch (err) {
      console.error(`Failed to start conversation: ${err}`);
      setMessages([
        {
          role: 'agent',
          content: `Error: ${err}. Please check if the backend is running at http://localhost:8001`,
          timestamp: new Date().toISOString(),
          agent_source: 'error'
        }
      ]);
    }
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
      console.log('Calling client.sendMessage...');
      const resp = await client.sendMessage(conversationId, messageText);
      console.log('Send message response:', resp);

      if (resp.success && resp.data) {
        // Get the current message count before adding new ones
        const currentMessageCount = messages.length + 1; // +1 for the user message we just added

        // Get all messages from backend
        const allMessages = resp.data.messages;
        console.log('All messages from backend:', allMessages.length);
        console.log('Current frontend message count:', currentMessageCount);

        // Only take messages that are NEW (beyond our current count)
        const newMessages = allMessages.slice(currentMessageCount);

        const newMsgs: Message[] = newMessages.map(m => ({
          role: m.role as 'user' | 'agent',
          content: m.content,
          timestamp: m.timestamp,
          agent_source: m.agent_source
        }));

        console.log('New messages to add:', newMsgs);

        // Only add the NEW messages
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
        }
      } else {
        console.error('Send message failed:', resp.error);
        const errorMsg: Message = {
          role: 'agent',
          content: `Error: ${resp.error || 'Failed to send message'}`,
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
