import React, { useState, useEffect } from 'react';
import { Test, StageComponent, ConversationContext, ActionItem } from '../../types/stage';

interface TestCatalogProps {
  component: StageComponent;
  conversationContext: ConversationContext;
  onAction: (action: ActionItem) => void;
  userPermissions: string[];
}

export const TestCatalogComponent: React.FC<TestCatalogProps> = ({
  component,
  conversationContext,
  onAction,
  userPermissions
}) => {
  const [tests, setTests] = useState<Test[]>([]);
  const [searchTerm, setSearchTerm] = useState('');
  const [selectedTest, setSelectedTest] = useState<Test | null>(null);
  const [filterCategory, setFilterCategory] = useState<'all' | 'chemistry' | 'hematology' | 'microbiology'>('all');

  useEffect(() => {
    if (component.data.tests) {
      setTests(component.data.tests);
    }
  }, [component.data.tests]);

  // Extract search terms from conversation context
  useEffect(() => {
    const keywords = conversationContext.keywords || [];
    const testKeywords = keywords.filter(keyword => 
      ['test', 'analysis', 'assay', 'method'].some(term => 
        keyword.toLowerCase().includes(term)
      )
    );
    if (testKeywords.length > 0 && !searchTerm) {
      setSearchTerm(testKeywords[0]);
    }
  }, [conversationContext.keywords, searchTerm]);

  const filteredTests = tests.filter(test => {
    const matchesSearch = !searchTerm || 
      test.name.toLowerCase().includes(searchTerm.toLowerCase()) ||
      test.method.toLowerCase().includes(searchTerm.toLowerCase()) ||
      test.analytes.some(analyte => 
        analyte.toLowerCase().includes(searchTerm.toLowerCase())
      );

    const matchesCategory = filterCategory === 'all' || 
      test.name.toLowerCase().includes(filterCategory);

    return matchesSearch && matchesCategory;
  });

  const getAccreditationColor = (status: Test['accreditationStatus']) => {
    switch (status) {
      case 'accredited': return 'bg-green-100 text-green-800';
      case 'non_accredited': return 'bg-yellow-100 text-yellow-800';
      case 'pending': return 'bg-blue-100 text-blue-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  const testActions: ActionItem[] = [
    {
      id: 'search-tests',
      type: 'test',
      label: 'Advanced Search',
      description: 'Search tests by multiple criteria',
      icon: '🔍',
      priority: 'high',
      onExecute: () => {
        onAction({
          id: 'search-tests',
          type: 'test',
          label: 'Advanced Search',
          description: 'Search tests by multiple criteria',
          icon: '🔍',
          priority: 'high',
          onExecute: () => console.log('Opening advanced search')
        });
      }
    },
    {
      id: 'compare-methods',
      type: 'test',
      label: 'Compare Methods',
      description: 'Compare analytical methods',
      icon: '⚖️',
      priority: 'medium',
      onExecute: () => {
        onAction({
          id: 'compare-methods',
          type: 'test',
          label: 'Compare Methods',
          description: 'Compare analytical methods',
          icon: '⚖️',
          priority: 'medium',
          onExecute: () => console.log('Opening method comparison')
        });
      }
    },
    {
      id: 'request-test',
      type: 'test',
      label: 'Request Test',
      description: 'Submit a test request',
      icon: '📝',
      priority: 'high',
      onExecute: () => {
        onAction({
          id: 'request-test',
          type: 'test',
          label: 'Request Test',
          description: 'Submit a test request',
          icon: '📝',
          priority: 'high',
          onExecute: () => console.log('Opening test request form')
        });
      }
    }
  ];

  if (component.state === 'Loading') {
    return (
      <div className="stage-component bg-white rounded-lg shadow-sm border border-gray-200 p-4">
        <div className="flex items-center space-x-2 mb-4">
          <div className="w-4 h-4 bg-green-500 rounded animate-pulse"></div>
          <h3 className="font-medium text-gray-900">Test Catalog</h3>
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
        <div className="flex items-center justify-between mb-3">
          <div className="flex items-center space-x-2">
            <span className="text-green-500 text-lg">⚗️</span>
            <h3 className="font-medium text-gray-900">Test Catalog</h3>
            <span className="bg-green-100 text-green-800 text-xs px-2 py-1 rounded-full">
              {filteredTests.length} tests
            </span>
          </div>
        </div>

        {/* Search and Filters */}
        <div className="flex flex-col sm:flex-row gap-3">
          <div className="flex-1">
            <input
              type="text"
              placeholder="Search tests, methods, or analytes..."
              value={searchTerm}
              onChange={(e) => setSearchTerm(e.target.value)}
              className="w-full px-3 py-2 border border-gray-300 rounded-md text-sm focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-transparent"
            />
          </div>
          <div className="flex space-x-1">
            {['all', 'chemistry', 'hematology', 'microbiology'].map((category) => (
              <button
                key={category}
                onClick={() => setFilterCategory(category as any)}
                className={`px-3 py-2 text-xs rounded-md ${
                  filterCategory === category
                    ? 'bg-green-100 text-green-700'
                    : 'text-gray-500 hover:text-gray-700 hover:bg-gray-100'
                }`}
              >
                {category.charAt(0).toUpperCase() + category.slice(1)}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* Content */}
      <div className="p-4">
        {/* Quick Actions */}
        <div className="mb-4 flex flex-wrap gap-2">
          {testActions.map((action) => (
            <button
              key={action.id}
              onClick={action.onExecute}
              className="flex items-center space-x-1 px-3 py-1 bg-green-50 text-green-700 text-sm rounded-md hover:bg-green-100 transition-colors"
            >
              <span>{action.icon}</span>
              <span>{action.label}</span>
            </button>
          ))}
        </div>

        {/* Test List */}
        <div className="space-y-3">
          {filteredTests.slice(0, 6).map((test) => (
            <div
              key={test.id}
              className={`p-3 rounded-lg border cursor-pointer transition-all ${
                selectedTest?.id === test.id
                  ? 'border-green-300 bg-green-50'
                  : 'border-gray-200 hover:border-gray-300'
              }`}
              onClick={() => setSelectedTest(test)}
            >
              <div className="flex items-start justify-between mb-2">
                <div className="flex-1">
                  <h4 className="font-medium text-gray-900 mb-1">{test.name}</h4>
                  <p className="text-sm text-gray-600">{test.method}</p>
                </div>
                <div className="flex flex-col items-end space-y-1">
                  <span className={`px-2 py-1 text-xs rounded-full ${getAccreditationColor(test.accreditationStatus)}`}>
                    {test.accreditationStatus.replace('_', ' ')}
                  </span>
                  <span className="text-xs text-gray-500">{test.turnaroundTime}</span>
                </div>
              </div>
              
              <div className="text-sm text-gray-600 space-y-1">
                <div>
                  <span className="font-medium">Analytes:</span> {test.analytes.slice(0, 3).join(', ')}
                  {test.analytes.length > 3 && ` +${test.analytes.length - 3} more`}
                </div>
                <div>
                  <span className="font-medium">Sample Types:</span> {test.sampleTypes.join(', ')}
                </div>
                <div className="flex justify-between items-center">
                  <span><span className="font-medium">Cost:</span> ${test.cost}</span>
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      onAction({
                        id: 'select-test',
                        type: 'test',
                        label: 'Select Test',
                        description: `Select ${test.name}`,
                        icon: '✓',
                        priority: 'high',
                        onExecute: () => console.log(`Selected test: ${test.name}`)
                      });
                    }}
                    className="px-2 py-1 bg-blue-100 text-blue-700 text-xs rounded hover:bg-blue-200"
                  >
                    Select
                  </button>
                </div>
              </div>
            </div>
          ))}
        </div>

        {/* Show more tests if there are more */}
        {filteredTests.length > 6 && (
          <div className="mt-3 text-center">
            <button className="text-green-600 text-sm hover:text-green-800">
              Show {filteredTests.length - 6} more tests...
            </button>
          </div>
        )}

        {/* Empty state */}
        {filteredTests.length === 0 && (
          <div className="text-center py-8 text-gray-500">
            <div className="text-4xl mb-2">🔍</div>
            <p>No tests found matching your criteria</p>
            <p className="text-sm">Try adjusting your search or filter</p>
          </div>
        )}
      </div>

      {/* Selected Test Details */}
      {selectedTest && (
        <div className="border-t border-gray-200 p-4 bg-gray-50">
          <h4 className="font-medium text-gray-900 mb-3">Test Details</h4>
          <div className="grid grid-cols-1 md:grid-cols-2 gap-4 text-sm">
            <div>
              <span className="text-gray-600 font-medium">Methodology:</span>
              <p className="text-gray-900 mt-1">{selectedTest.methodology}</p>
            </div>
            <div>
              <span className="text-gray-600 font-medium">QC Requirements:</span>
              <ul className="text-gray-900 mt-1 space-y-1">
                {selectedTest.qcRequirements.map((req, index) => (
                  <li key={index} className="text-xs">• {req}</li>
                ))}
              </ul>
            </div>
            <div>
              <span className="text-gray-600 font-medium">All Analytes:</span>
              <div className="mt-1 flex flex-wrap gap-1">
                {selectedTest.analytes.map((analyte, index) => (
                  <span 
                    key={index}
                    className="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded"
                  >
                    {analyte}
                  </span>
                ))}
              </div>
            </div>
            <div>
              <span className="text-gray-600 font-medium">Reference Ranges:</span>
              <p className="text-gray-900 mt-1 text-xs">
                {selectedTest.referenceRanges.length} range(s) available
              </p>
            </div>
          </div>
          
          <div className="mt-3 flex space-x-2">
            <button 
              className="px-3 py-1 bg-green-600 text-white text-sm rounded hover:bg-green-700"
              onClick={() => console.log('Request test:', selectedTest.name)}
            >
              Request This Test
            </button>
            <button 
              className="px-3 py-1 bg-gray-600 text-white text-sm rounded hover:bg-gray-700"
              onClick={() => console.log('View protocol:', selectedTest.name)}
            >
              View Protocol
            </button>
          </div>
        </div>
      )}
    </div>
  );
};

export default TestCatalogComponent;
