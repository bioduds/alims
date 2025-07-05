import React from 'react';
import { Box } from '@mui/material';
import { cn } from '../utils/cn';
import { SampleTrackerComponent } from './stage/SampleTrackerComponent';
import { TestCatalogComponent } from './stage/TestCatalogComponent';
import { KnowledgeBaseComponent } from './stage/KnowledgeBaseComponent';
import { StageState } from '../types/stage';

interface StageProps {
  className?: string;
  stageState?: StageState;
}

export const Stage: React.FC<StageProps> = ({ className, stageState }) => {
  return (
    <Box className={cn('bg-gray-900 p-4 overflow-auto', className)}>
      <div className="grid gap-4">
        {/* Sample Tracking Panel */}
        {stageState?.showSampleTracker && (
          <SampleTrackerComponent />
        )}

        {/* Test Catalog Panel */}
        {stageState?.showTestCatalog && (
          <TestCatalogComponent />
        )}

        {/* Knowledge Base Panel */}
        {stageState?.showKnowledgeBase && (
          <KnowledgeBaseComponent />
        )}
      </div>
    </Box>
  );
};
