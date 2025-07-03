#!/usr/bin/env python3
"""
Debug chat endpoint to find the issue
"""

import asyncio
import aiohttp
import json
import time

async def test_simple_chat():
    """Test the chat endpoint with a simple message"""
    
    print("🔍 Testing ALims Chat API")
    
    # Simple test message
    payload = {
        "message": "hello world",
        "conversation_id": "debug_test",
        "user_id": "debug_user"
    }
    
    try:
        print("📤 Sending request to http://localhost:8000/chat")
        
        async with aiohttp.ClientSession() as session:
            # Test with a short timeout first
            async with session.post(
                "http://localhost:8000/chat",
                json=payload,
                timeout=aiohttp.ClientTimeout(total=10)
            ) as response:
                print(f"📨 Response status: {response.status}")
                
                if response.status == 200:
                    result = await response.json()
                    print("✅ Success! Response received:")
                    print(f"   Message: {result.get('message', 'No message')[:100]}...")
                    print(f"   Success: {result.get('success', 'No success field')}")
                    return True
                else:
                    print(f"❌ HTTP Error {response.status}")
                    text = await response.text()
                    print(f"   Error text: {text[:200]}...")
                    return False
                    
    except asyncio.TimeoutError:
        print("⏰ Request timed out")
        return False
    except Exception as e:
        print(f"❌ Exception: {e}")
        return False

async def test_web_search_chat():
    """Test chat with web search trigger"""
    
    if not await test_simple_chat():
        print("❌ Simple chat failed, skipping web search test")
        return False
    
    print("\n🌐 Testing web search in chat")
    
    payload = {
        "message": "What is the weather like in Tokyo today?",
        "conversation_id": "web_search_debug",
        "user_id": "debug_user"
    }
    
    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(
                "http://localhost:8000/chat",
                json=payload,
                timeout=aiohttp.ClientTimeout(total=20)
            ) as response:
                
                if response.status == 200:
                    result = await response.json()
                    message = result.get('message', '').lower()
                    
                    print("✅ Web search chat response received")
                    print(f"   Response: {result.get('message', '')[:200]}...")
                    
                    # Check for web search indicators
                    web_indicators = ['weather', 'tokyo', 'temperature', 'search', 'found']
                    found_indicators = [term for term in web_indicators if term in message]
                    
                    if found_indicators:
                        print(f"🌤️ Found web search indicators: {found_indicators}")
                        return True
                    else:
                        print("⚠️ No web search indicators found")
                        return False
                else:
                    print(f"❌ Web search chat failed: {response.status}")
                    return False
                    
    except Exception as e:
        print(f"❌ Web search test error: {e}")
        return False

async def main():
    print("🚀 Starting ALims Chat Debug Test\n")
    
    # Test 1: Simple chat
    simple_works = await test_simple_chat()
    
    # Test 2: Web search chat (only if simple works)
    web_works = False
    if simple_works:
        web_works = await test_web_search_chat()
    
    print(f"\n📊 Results:")
    print(f"   Simple chat: {'✅' if simple_works else '❌'}")
    print(f"   Web search chat: {'✅' if web_works else '❌'}")
    
    if simple_works and web_works:
        print("\n🎉 Both tests passed! Web search in chat is working!")
    elif simple_works:
        print("\n⚠️ Simple chat works, but web search needs debugging")
    else:
        print("\n❌ Basic chat is not working - need to fix API endpoint first")

if __name__ == "__main__":
    asyncio.run(main())
