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
        // Get all messages from backend
        const allMessages = data.messages;
        console.log('All messages from backend:', allMessages.length);
        console.log('Current messages before sending:', messages.length);

        // The backend returns: [old messages, user message, new agent responses]
        // We want only the NEW agent responses (everything after user message)
        // Find the user message we just sent in the backend response
        const userMsgIndex = allMessages.findIndex((m: any) =>
          m.role === 'user' && m.content === messageText
        );

        console.log('User message found at index:', userMsgIndex);

        // Take everything after the user message (agent responses only)
        const newAgentMessages = userMsgIndex >= 0 ? allMessages.slice(userMsgIndex + 1) : [];

        const newMsgs: Message[] = newAgentMessages.map((m: any) => ({
          role: m.role as 'user' | 'agent',
          content: m.content,
          timestamp: m.timestamp,
          agent_source: m.agent_source
        }));

        console.log('New agent messages to add:', newMsgs);
        console.log('Raw new agent messages from backend:', newAgentMessages);

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
