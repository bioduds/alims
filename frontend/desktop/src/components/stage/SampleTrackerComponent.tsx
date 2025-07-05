import React, { useState, useEffect } from 'react';
import { Sample, StageComponent, ConversationContext, ActionItem } from '../types/stage';

interface SampleTrackerProps {
  component: StageComponent;
  conversationContext: ConversationContext;
  onAction: (action: ActionItem) => void;
  userPermissions: string[];
}

export const SampleTrackerComponent: React.FC<SampleTrackerProps> = ({
  component,
  conversationContext,
  onAction,
  userPermissions
}) => {
  const [samples, setSamples] = useState<Sample[]>([]);
  const [selectedSample, setSelectedSample] = useState<Sample | null>(null);
  const [filter, setFilter] = useState<'all' | 'active' | 'completed'>('all');

  useEffect(() => {
    if (component.data.samples) {
      setSamples(component.data.samples);
    }
  }, [component.data.samples]);

  const filteredSamples = samples.filter(sample => {
    if (filter === 'all') return true;
    if (filter === 'active') return ['received', 'in_progress'].includes(sample.status);
    if (filter === 'completed') return ['completed', 'archived'].includes(sample.status);
    return true;
  });

  const getStatusColor = (status: Sample['status']) => {
    switch (status) {
      case 'received': return 'bg-blue-100 text-blue-800';
      case 'in_progress': return 'bg-yellow-100 text-yellow-800';
      case 'completed': return 'bg-green-100 text-green-800';
      case 'archived': return 'bg-gray-100 text-gray-800';
      case 'rejected': return 'bg-red-100 text-red-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  const getPriorityColor = (priority: Sample['priority']) => {
    switch (priority) {
      case 'stat': return 'text-red-600 font-bold';
      case 'urgent': return 'text-orange-600 font-semibold';
      case 'routine': return 'text-gray-600';
      default: return 'text-gray-600';
    }
  };

  const sampleActions: ActionItem[] = [
    {
      id: 'register-sample',
      type: 'sample',
      label: 'Register New Sample',
      description: 'Add a new sample to the system',
      icon: '🧪',
      priority: 'medium',
      onExecute: () => {
        onAction({
          id: 'register-sample',
          type: 'sample',
          label: 'Register New Sample',
          description: 'Add a new sample to the system',
          icon: '🧪',
          priority: 'medium',
          onExecute: () => console.log('Opening sample registration')
        });
      }
    },
    {
      id: 'bulk-update',
      type: 'sample',
      label: 'Bulk Update',
      description: 'Update multiple samples at once',
      icon: '📋',
      priority: 'low',
      onExecute: () => {
        onAction({
          id: 'bulk-update',
          type: 'sample',
          label: 'Bulk Update',
          description: 'Update multiple samples at once',
          icon: '📋',
          priority: 'low',
          onExecute: () => console.log('Opening bulk update')
        });
      }
    }
  ];

  if (component.state === 'Loading') {
    return (
      <div className="stage-component bg-white rounded-lg shadow-sm border border-gray-200 p-4">
        <div className="flex items-center space-x-2 mb-4">
          <div className="w-4 h-4 bg-blue-500 rounded animate-pulse"></div>
          <h3 className="font-medium text-gray-900">Sample Tracker</h3>
        </div>
        <div className="animate-pulse space-y-3">
          <div className="h-4 bg-gray-200 rounded w-3/4"></div>
          <div className="h-4 bg-gray-200 rounded w-1/2"></div>
          <div className="h-4 bg-gray-200 rounded w-5/6"></div>
        </div>
      </div>
    );
  }

  return (
    <div className="stage-component bg-white rounded-lg shadow-sm border border-gray-200">
      {/* Header */}
      <div className="border-b border-gray-200 p-4">
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-2">
            <span className="text-blue-500 text-lg">🧪</span>
            <h3 className="font-medium text-gray-900">Sample Tracker</h3>
            <span className="bg-blue-100 text-blue-800 text-xs px-2 py-1 rounded-full">
              {filteredSamples.length} samples
            </span>
          </div>
          <div className="flex space-x-1">
            {['all', 'active', 'completed'].map((filterType) => (
              <button
                key={filterType}
                onClick={() => setFilter(filterType as any)}
                className={`px-3 py-1 text-xs rounded-md ${
                  filter === filterType
                    ? 'bg-blue-100 text-blue-700'
                    : 'text-gray-500 hover:text-gray-700'
                }`}
              >
                {filterType.charAt(0).toUpperCase() + filterType.slice(1)}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* Content */}
      <div className="p-4">
        {/* Quick Actions */}
        <div className="mb-4 flex flex-wrap gap-2">
          {sampleActions.map((action) => (
            <button
              key={action.id}
              onClick={action.onExecute}
              className="flex items-center space-x-1 px-3 py-1 bg-blue-50 text-blue-700 text-sm rounded-md hover:bg-blue-100 transition-colors"
            >
              <span>{action.icon}</span>
              <span>{action.label}</span>
            </button>
          ))}
        </div>

        {/* Sample List */}
        <div className="space-y-3">
          {filteredSamples.slice(0, 5).map((sample) => (
            <div
              key={sample.id}
              className={`p-3 rounded-lg border cursor-pointer transition-all ${
                selectedSample?.id === sample.id
                  ? 'border-blue-300 bg-blue-50'
                  : 'border-gray-200 hover:border-gray-300'
              }`}
              onClick={() => setSelectedSample(sample)}
            >
              <div className="flex items-center justify-between mb-2">
                <div className="flex items-center space-x-2">
                  <span className="font-medium text-gray-900">{sample.id}</span>
                  <span className={getPriorityColor(sample.priority)}>
                    {sample.priority.toUpperCase()}
                  </span>
                </div>
                <span className={`px-2 py-1 text-xs rounded-full ${getStatusColor(sample.status)}`}>
                  {sample.status.replace('_', ' ')}
                </span>
              </div>
              
              <div className="text-sm text-gray-600 space-y-1">
                <div className="flex justify-between">
                  <span>Type: {sample.sampleType}</span>
                  <span>Location: {sample.location}</span>
                </div>
                <div>
                  Tests: {sample.tests.join(', ')}
                </div>
                <div className="text-xs text-gray-500">
                  Registered: {sample.registrationDate.toLocaleDateString()}
                </div>
              </div>
            </div>
          ))}
        </div>

        {/* Show more samples if there are more */}
        {filteredSamples.length > 5 && (
          <div className="mt-3 text-center">
            <button className="text-blue-600 text-sm hover:text-blue-800">
              Show {filteredSamples.length - 5} more samples...
            </button>
          </div>
        )}

        {/* Empty state */}
        {filteredSamples.length === 0 && (
          <div className="text-center py-8 text-gray-500">
            <div className="text-4xl mb-2">🔍</div>
            <p>No samples found for the current filter</p>
            <p className="text-sm">Try adjusting your filter or register a new sample</p>
          </div>
        )}
      </div>

      {/* Selected Sample Details */}
      {selectedSample && (
        <div className="border-t border-gray-200 p-4 bg-gray-50">
          <h4 className="font-medium text-gray-900 mb-2">Sample Details</h4>
          <div className="grid grid-cols-2 gap-4 text-sm">
            <div>
              <span className="text-gray-600">Patient ID:</span>
              <span className="ml-2 text-gray-900">{selectedSample.patientId || 'N/A'}</span>
            </div>
            <div>
              <span className="text-gray-600">Volume:</span>
              <span className="ml-2 text-gray-900">{selectedSample.volume || 'N/A'} mL</span>
            </div>
            <div className="col-span-2">
              <span className="text-gray-600">Chain of Custody:</span>
              <div className="mt-1 space-y-1">
                {selectedSample.chainOfCustody.slice(0, 3).map((record, index) => (
                  <div key={index} className="text-xs text-gray-600 pl-2 border-l-2 border-gray-300">
                    {record.timestamp.toLocaleString()} - {record.action} by {record.userId}
                  </div>
                ))}
              </div>
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default SampleTrackerComponent;
