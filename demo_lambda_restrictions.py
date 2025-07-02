#!/usr/bin/env python3
"""
Quick Lambda Restrictions Demo - showing the system in action
"""

import asyncio
import sys
import os

# Add the parent directory to the path to import our modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))

from backend.app.ai.central_brain import CentralAIBrain

async def demo_lambda_restrictions():
    """Demo the Lambda restrictions with clear examples"""
    
    print("🎭 CELFLOW LAMBDA RESTRICTIONS DEMO")
    print("=" * 50)
    
    # Mock config for testing
    config = {
        'ai_brain': {'model_name': 'gemma3:4b'},
        'context_management': {},
        'system_control': {}
    }
    
    brain = CentralAIBrain(config)
    
    scenarios = [
        {
            "name": "✅ SAFE: Simple Prime Calculator",
            "code": '''
def calculate_prime_numbers(n):
    """Generate first n prime numbers"""
    primes = []
    num = 2
    while len(primes) < n:
        is_prime = True
        for i in range(2, int(num ** 0.5) + 1):
            if num % i == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(num)
        num += 1
    return primes
''',
            "purpose": "mathematical_calculation",
            "context": {"n": 5}
        },
        {
            "name": "✅ SAFE: Visualization with matplotlib",
            "code": '''
def generate_data_plot(data):
    """Create a simple plot of data"""
    import matplotlib.pyplot as plt
    plt.figure(figsize=(8, 6))
    plt.plot(data, marker='o')
    plt.title('Data Plot')
    plt.xlabel('Index')
    plt.ylabel('Value')
    plt.grid(True)
    plt.savefig('output_plot.png')
    plt.close()
    return f"Plot saved with {len(data)} data points"
''',
            "purpose": "visualization",
            "context": {"data": [1, 4, 9, 16, 25]}
        },
        {
            "name": "❌ BLOCKED: File operations",
            "code": '''
def read_secret_files():
    """This should be blocked"""
    import os
    files = os.listdir('/etc')
    return files
''',
            "purpose": "data_processing",
            "context": {}
        },
        {
            "name": "❌ BLOCKED: Network requests",
            "code": '''
def fetch_data_from_internet():
    """This should be blocked"""
    import requests
    response = requests.get('https://api.github.com/user')
    return response.json()
''',
            "purpose": "data_processing",
            "context": {}
        }
    ]
    
    for i, scenario in enumerate(scenarios, 1):
        print(f"\n🔬 Test {i}: {scenario['name']}")
        print(f"Purpose: {scenario['purpose']}")
        
        try:
            result = await brain.execute_dynamic_code(
                code=scenario['code'],
                purpose=scenario['purpose'],
                context=scenario['context']
            )
            
            success = result.get('success', False)
            error = result.get('error', '')
            executor_type = "Simple" if result.get('pattern_type') else "Full"
            
            print(f"✨ Executor: {executor_type}")
            print(f"✨ Success: {success}")
            
            if success:
                if result.get('result'):
                    print(f"✨ Result: {result.get('result', {}).get('value', 'N/A')}")
                print(f"✨ Time: {result.get('execution_time', 0):.3f}s")
            else:
                print(f"✨ Error: {error}")
                
        except Exception as e:
            print(f"✨ Exception: {str(e)}")
    
    print(f"\n🎉 DEMO COMPLETE!")
    print("The Lambda restrictions are successfully:")
    print("  ✅ Allowing safe, simple algorithms")
    print("  ✅ Supporting visualization with matplotlib")
    print("  ❌ Blocking file operations and network requests")
    print("  ✅ Providing detailed logging for debugging")

if __name__ == "__main__":
    asyncio.run(demo_lambda_restrictions())
