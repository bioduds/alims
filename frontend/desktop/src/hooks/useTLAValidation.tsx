import React, { createContext, useContext, useCallback } from 'react';

interface TLAState {
  validateStageTransition: (stageType: string, data: any) => boolean;
}

const TLAStateContext = createContext<TLAState | undefined>(undefined);

export function TLAStateProvider({ children }: { children: React.ReactNode }) {
  // TLA+ validation rules would be defined here
  const validateStageTransition = useCallback((stageType: string, data: any) => {
    // Implement TLA+ validation logic
    switch (stageType) {
      case 'visualization':
        // Example TLA+ validation rule for visualizations
        // - Must have a valid type
        // - Must maintain state consistency
        // - Must follow LIMS stage transitions
        if (!data.type && data.type !== null) {
          console.warn('TLA+ validation: Invalid visualization type');
          return false;
        }
        
        // Add more complex TLA+ validation logic here
        // ...

        return true;

      default:
        console.warn('TLA+ validation: Unknown stage type');
        return false;
    }
  }, []);

  const value = {
    validateStageTransition
  };

  return (
    <TLAStateContext.Provider value={value}>
      {children}
    </TLAStateContext.Provider>
  );
}

export function useTLAState() {
  const context = useContext(TLAStateContext);
  if (context === undefined) {
    throw new Error('useTLAState must be used within a TLAStateProvider');
  }
  return context;
}
