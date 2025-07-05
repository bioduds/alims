import React, { useState, useEffect, useCallback } from 'react';
import { LimsStageSystem } from './LimsStageSystem';
import { 
  StageComponent, 
  LimsChatMessage, 
  SystemState, 
  ChatMessageType
} from '../types/stage';
import { SampleTrackerComponent } from './stage/SampleTrackerComponent';
import { TestCatalogComponent } from './stage/TestCatalogComponent';
import { KnowledgeBaseComponent } from './stage/KnowledgeBaseComponent';

interface LimsStageSystemWrapperProps {
  onChatMessage?: (message: LimsChatMessage) => void;
  className?: string;
}

/**
 * React wrapper for the TLA+-validated LimsStageSystem
 * 
 * This component provides the React integration layer for our mathematically
 * verified LIMS stage system, ensuring every chat message triggers stage updates.
 */
export const LimsStageSystemWrapper: React.FC<LimsStageSystemWrapperProps> = ({
  onChatMessage,
  className = ''
}) => {
  const [stageSystem] = useState(() => new LimsStageSystem());
  const [systemState, setSystemState] = useState<SystemState>('INITIALIZING');
  const [activeComponents, setActiveComponents] = useState<StageComponent[]>([]);
  const [chatHistory, setChatHistory] = useState<LimsChatMessage[]>([]);
  const [error, setError] = useState<string | null>(null);

  // Initialize the stage system
  useEffect(() => {
    const initializeSystem = async () => {
      try {
        // Set up event listeners
        stageSystem.setEventCallbacks(
          setSystemState,
          setActiveComponents,
          setChatHistory
        );

        // Initialize the system
        await stageSystem.initialize();
      } catch (err) {
        console.error('Failed to initialize LIMS stage system:', err);
        setError(err instanceof Error ? err.message : 'Unknown error');
      }
    };

    initializeSystem();
  }, [stageSystem]);

  // Handle incoming chat messages from parent components
  const handleChatMessage = useCallback(async (
    content: string, 
    messageType: ChatMessageType = 'GENERAL_QUERY'
  ) => {
    try {
      setError(null);
      
      const message: LimsChatMessage = {
        id: `msg_${Date.now()}`,
        role: 'user',
        content,
        type: messageType,
        timestamp: new Date(),
        triggeredComponents: []
      };

      // Process the message through our TLA+-validated system
      await stageSystem.processChatMessageAsync(message);
      
      // Notify parent component
      if (onChatMessage) {
        onChatMessage(message);
      }
    } catch (err) {
      console.error('Error processing chat message:', err);
      setError(err instanceof Error ? err.message : 'Failed to process message');
    }
  }, [stageSystem, onChatMessage]);

  // Auto-classify message type based on content
  const classifyMessageType = (content: string): ChatMessageType => {
    const lowerContent = content.toLowerCase();
    
    if (lowerContent.includes('sample') || lowerContent.includes('specimen')) {
      return 'SAMPLE_INQUIRY';
    }
    if (lowerContent.includes('test') || lowerContent.includes('assay') || lowerContent.includes('analysis')) {
      return 'TEST_REQUEST';
    }
    if (lowerContent.includes('protocol') || lowerContent.includes('procedure') || 
        lowerContent.includes('regulation') || lowerContent.includes('standard')) {
      return 'KNOWLEDGE_QUERY';
    }
    
    return 'GENERAL_QUERY';
  };

  // Public method for external components to send messages
  const sendMessage = useCallback((content: string, explicitType?: ChatMessageType) => {
    const messageType = explicitType || classifyMessageType(content);
    handleChatMessage(content, messageType);
  }, [handleChatMessage]);

  // Expose the sendMessage method to parent components
  useEffect(() => {
    // Store reference for external access
    (window as any).limsStageSystem = { sendMessage };
    
    return () => {
      delete (window as any).limsStageSystem;
    };
  }, [sendMessage]);

  // Render individual stage components
  const renderComponent = (component: StageComponent) => {
    const commonProps = {
      key: component.id,
      component,
      onAction: (action: any) => {
        console.log('Stage component action:', action);
        // Handle component actions if needed
      }
    };

    // Map LIMS component types to existing stage component types
    const componentType = component.type;
    
    if (componentType === 'SampleTracker') {
      // Add required props for SampleTrackerComponent
      const sampleProps = {
        ...commonProps,
        conversationContext: {
          conversationId: 'current',
          messages: chatHistory,
          entities: [],
          intent: 'sample_inquiry',
          keywords: [],
          lastUpdate: new Date(),
          confidence: 0.8
        },
        userPermissions: ['read', 'write']
      };
      return <SampleTrackerComponent {...sampleProps} />;
    }
    
    if (componentType === 'TestCatalog') {
      // Add required props for TestCatalogComponent
      const testProps = {
        ...commonProps,
        conversationContext: {
          conversationId: 'current',
          messages: chatHistory,
          entities: [],
          intent: 'test_request',
          keywords: [],
          lastUpdate: new Date(),
          confidence: 0.8
        },
        userPermissions: ['read', 'write']
      };
      return <TestCatalogComponent {...testProps} />;
    }
    
    if (componentType === 'KnowledgeExplorer') {
      return <KnowledgeBaseComponent {...commonProps} />;
    }
    
    return (
      <div key={component.id} className="p-4 border rounded-lg bg-gray-50">
        <h3 className="font-medium text-gray-900">Unknown Component</h3>
        <p className="text-sm text-gray-600">Type: {component.type}</p>
      </div>
    );
  };

  const getSystemStateColor = (state: SystemState) => {
    switch (state) {
      case 'INITIALIZING': return 'bg-yellow-100 text-yellow-800';
      case 'READY': return 'bg-green-100 text-green-800';
      case 'PROCESSING_CHAT': return 'bg-blue-100 text-blue-800';
      case 'UPDATING_STAGE': return 'bg-purple-100 text-purple-800';
      case 'ERROR': return 'bg-red-100 text-red-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  return (
    <div className={`lims-stage-system ${className}`}>
      {/* System Status Header */}
      <div className="mb-4 p-3 bg-white rounded-lg shadow-sm border border-gray-200">
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-3">
            <span className="text-lg">🧪</span>
            <h2 className="text-lg font-semibold text-gray-900">LIMS Stage System</h2>
            <span className={`px-2 py-1 rounded-full text-xs font-medium ${getSystemStateColor(systemState)}`}>
              {systemState}
            </span>
          </div>
          <div className="text-sm text-gray-600">
            {activeComponents.length}/3 components active
          </div>
        </div>
        
        {error && (
          <div className="mt-2 p-2 bg-red-50 border border-red-200 rounded text-sm text-red-700">
            <strong>Error:</strong> {error}
          </div>
        )}
      </div>

      {/* Active Stage Components */}
      <div className="space-y-4">
        {activeComponents.length === 0 ? (
          <div className="text-center py-8 text-gray-500">
            <span className="block text-3xl mb-2">💬</span>
            <p className="text-lg font-medium">Ready for LIMS interaction</p>
            <p className="text-sm">
              Start a conversation to see relevant LIMS components appear here.
              <br />
              Every chat message will automatically update the stage with relevant panels.
            </p>
          </div>
        ) : (
          <div className="grid gap-4">
            {activeComponents.map(renderComponent)}
          </div>
        )}
      </div>

      {/* Chat History Summary (for debugging) */}
      {process.env.NODE_ENV === 'development' && chatHistory.length > 0 && (
        <div className="mt-6 p-3 bg-gray-50 rounded-lg">
          <h3 className="text-sm font-medium text-gray-700 mb-2">
            Recent Chat History ({chatHistory.length})
          </h3>
          <div className="space-y-1">
            {chatHistory.slice(-3).map((msg) => (
              <div key={msg.id} className="text-xs text-gray-600">
                <span className="font-medium">{msg.type}:</span> {msg.content.substring(0, 50)}...
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

export default LimsStageSystemWrapper;
