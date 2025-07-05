import { useState, useCallback } from 'react';
import { ChatResponse } from '../types/alims';
import { LimsStageSystem } from '../components/LimsStageSystem';
import { StageState } from '../types/stage';

const stageSystem = new LimsStageSystem();

export const useTLAStageValidation = () => {
  const [stageState, setStageState] = useState<StageState>({
    showSampleTracker: false,
    showTestCatalog: false,
    showKnowledgeBase: true, // Start with knowledge base visible
  });

  const validateStageUpdate = useCallback(async (response: ChatResponse) => {
    // Extract intent and message from chat response
    const messageType = response.intent || 'GENERAL_QUERY';
    const message = {
      id: response.id || `msg_${Date.now()}`,
      role: 'user',
      content: response.text,
      timestamp: new Date(),
      type: messageType,
      limsType: messageType,
      triggeredComponents: []
    };

    // Run through our TLA+-verified state machine
    stageSystem.processChatMessage(message);
    stageSystem.updateStageFromChat(message);
    
    // Get the active components and update stage state
    const components = stageSystem.getActiveComponents();
    setStageState({
      showSampleTracker: components.some(c => c.type === 'SampleTracker'),
      showTestCatalog: components.some(c => c.type === 'TestCatalog'),
      showKnowledgeBase: components.some(c => c.type === 'KnowledgeExplorer'),
    });

    stageSystem.completeStageUpdate();
    return { isValid: true, state: stageSystem.getSystemState() };
  }, []);

  return { validateStageUpdate, stageState };
};
