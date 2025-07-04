import React, { useState } from 'react';
import { cn } from '../utils/cn';

interface Sample {
  id?: string;
  patientId: string;
  sampleType: string;
  priority: 'ROUTINE' | 'URGENT' | 'STAT';
  testsRequested: string[];
  notes?: string;
}

interface SampleRegistrationProps {
  onSubmit: (sample: Sample) => void;
  onCancel: () => void;
}

export function SampleRegistrationForm({ onSubmit, onCancel }: SampleRegistrationProps) {
  const [sample, setSample] = useState<Sample>({
    patientId: '',
    sampleType: '',
    priority: 'ROUTINE',
    testsRequested: [],
    notes: ''
  });

  const sampleTypes = ['Blood', 'Urine', 'Tissue', 'Swab', 'CSF', 'Sputum'];
  const testOptions = [
    'Complete Blood Count', 'Basic Metabolic Panel', 'Lipid Panel', 
    'Liver Function Tests', 'Thyroid Panel', 'Urinalysis',
    'Culture & Sensitivity', 'PCR', 'Serology'
  ];

  const handleTestToggle = (test: string) => {
    setSample(prev => ({
      ...prev,
      testsRequested: prev.testsRequested.includes(test)
        ? prev.testsRequested.filter(t => t !== test)
        : [...prev.testsRequested, test]
    }));
  };

  const handleSubmit = (e: React.FormEvent) => {
    e.preventDefault();
    if (sample.patientId && sample.sampleType && sample.testsRequested.length > 0) {
      onSubmit(sample);
    }
  };

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg p-6 border border-gray-200 dark:border-gray-700 max-w-2xl">
      <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
        Register New Sample
      </h3>
      
      <form onSubmit={handleSubmit} className="space-y-4">
        <div>
          <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">
            Patient ID *
          </label>
          <input
            type="text"
            value={sample.patientId}
            onChange={(e) => setSample(prev => ({ ...prev, patientId: e.target.value }))}
            className="w-full px-3 py-2 border border-gray-300 dark:border-gray-600 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 dark:bg-gray-700 dark:text-white"
            placeholder="Enter patient ID"
            required
          />
        </div>

        <div>
          <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">
            Sample Type *
          </label>
          <select
            value={sample.sampleType}
            onChange={(e) => setSample(prev => ({ ...prev, sampleType: e.target.value }))}
            className="w-full px-3 py-2 border border-gray-300 dark:border-gray-600 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 dark:bg-gray-700 dark:text-white"
            required
          >
            <option value="">Select sample type</option>
            {sampleTypes.map(type => (
              <option key={type} value={type}>{type}</option>
            ))}
          </select>
        </div>

        <div>
          <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">
            Priority
          </label>
          <select
            value={sample.priority}
            onChange={(e) => setSample(prev => ({ ...prev, priority: e.target.value as Sample['priority'] }))}
            className="w-full px-3 py-2 border border-gray-300 dark:border-gray-600 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 dark:bg-gray-700 dark:text-white"
          >
            <option value="ROUTINE">Routine</option>
            <option value="URGENT">Urgent</option>
            <option value="STAT">STAT</option>
          </select>
        </div>

        <div>
          <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">
            Tests Requested *
          </label>
          <div className="grid grid-cols-1 md:grid-cols-2 gap-2 max-h-40 overflow-y-auto">
            {testOptions.map(test => (
              <label key={test} className="flex items-center space-x-2">
                <input
                  type="checkbox"
                  checked={sample.testsRequested.includes(test)}
                  onChange={() => handleTestToggle(test)}
                  className="rounded border-gray-300 text-blue-600 focus:ring-blue-500"
                />
                <span className="text-sm text-gray-700 dark:text-gray-300">{test}</span>
              </label>
            ))}
          </div>
        </div>

        <div>
          <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">
            Notes
          </label>
          <textarea
            value={sample.notes}
            onChange={(e) => setSample(prev => ({ ...prev, notes: e.target.value }))}
            className="w-full px-3 py-2 border border-gray-300 dark:border-gray-600 rounded-md focus:outline-none focus:ring-2 focus:ring-blue-500 dark:bg-gray-700 dark:text-white"
            rows={3}
            placeholder="Additional notes..."
          />
        </div>

        <div className="flex space-x-3 pt-4">
          <button
            type="submit"
            disabled={!sample.patientId || !sample.sampleType || sample.testsRequested.length === 0}
            className="flex-1 bg-blue-500 text-white py-2 px-4 rounded-md hover:bg-blue-600 focus:outline-none focus:ring-2 focus:ring-blue-500 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            Register Sample
          </button>
          <button
            type="button"
            onClick={onCancel}
            className="flex-1 bg-gray-500 text-white py-2 px-4 rounded-md hover:bg-gray-600 focus:outline-none focus:ring-2 focus:ring-gray-500"
          >
            Cancel
          </button>
        </div>
      </form>
    </div>
  );
}

interface WorkflowStatusProps {
  workflow: string;
  currentStep: string;
  steps: string[];
  data?: any;
}

export function WorkflowStatus({ workflow, currentStep, steps, data }: WorkflowStatusProps) {
  const currentIndex = steps.indexOf(currentStep);

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg p-4 border border-gray-200 dark:border-gray-700">
      <h4 className="text-md font-semibold text-gray-900 dark:text-white mb-3">
        {workflow} Workflow
      </h4>
      
      <div className="space-y-2">
        {steps.map((step, index) => (
          <div key={step} className="flex items-center space-x-3">
            <div className={cn(
              "w-4 h-4 rounded-full flex items-center justify-center text-xs font-bold",
              index < currentIndex ? "bg-green-500 text-white" :
              index === currentIndex ? "bg-blue-500 text-white" :
              "bg-gray-300 dark:bg-gray-600 text-gray-700 dark:text-gray-300"
            )}>
              {index < currentIndex ? "✓" : index + 1}
            </div>
            <span className={cn(
              "text-sm",
              index === currentIndex ? "text-blue-600 dark:text-blue-400 font-medium" :
              index < currentIndex ? "text-green-600 dark:text-green-400" :
              "text-gray-500 dark:text-gray-400"
            )}>
              {step}
            </span>
          </div>
        ))}
      </div>

      {data && (
        <div className="mt-4 p-3 bg-gray-50 dark:bg-gray-700 rounded-md">
          <h5 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">Current Data:</h5>
          <pre className="text-xs text-gray-600 dark:text-gray-400">
            {JSON.stringify(data, null, 2)}
          </pre>
        </div>
      )}
    </div>
  );
}

interface QuickActionsProps {
  actions: Array<{
    label: string;
    action: string;
    icon?: string;
  }>;
  onAction: (action: string) => void;
}

export function QuickActions({ actions, onAction }: QuickActionsProps) {
  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg p-4 border border-gray-200 dark:border-gray-700">
      <h4 className="text-md font-semibold text-gray-900 dark:text-white mb-3">
        Quick Actions
      </h4>
      
      <div className="grid grid-cols-2 gap-2">
        {actions.map((action, index) => (
          <button
            key={index}
            onClick={() => onAction(action.action)}
            className="flex items-center space-x-2 p-3 text-left border border-gray-200 dark:border-gray-600 rounded-md hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
          >
            {action.icon && <span className="text-lg">{action.icon}</span>}
            <span className="text-sm text-gray-700 dark:text-gray-300">{action.label}</span>
          </button>
        ))}
      </div>
    </div>
  );
}
