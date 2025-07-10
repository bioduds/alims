---- MODULE LimsStageSystem ----

\* ALIMS LIMS-focused Stage System
\* This module specifies the reactive stage system where every chat interaction
\* must trigger a stage update with relevant LIMS/science/knowledge components.

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    \* Maximum number of stage components that can be active simultaneously
    MAX_COMPONENTS,
    
    \* Set of all possible LIMS component types
    COMPONENT_TYPES,
    
    \* Set of all possible chat message types that trigger stage updates
    CHAT_MESSAGE_TYPES,
    
    \* Maximum number of chat messages in history
    MAX_CHAT_HISTORY,
    
    \* Set of possible component IDs
    COMPONENT_IDS,
    
    \* Set of possible message IDs
    MESSAGE_IDS

VARIABLES
    \* Current active stage components (set of component records)
    activeComponents,
    
    \* Chat history (sequence of chat message records)
    chatHistory,
    
    \* Current stage context (record with metadata about current stage state)
    stageContext,
    
    \* System state tracking
    systemState

\* Type definitions for stage components
StageComponent == [
    id: COMPONENT_IDS,
    type: COMPONENT_TYPES,
    data: MESSAGE_IDS,
    isVisible: BOOLEAN,
    priority: 1..3,
    dependencies: SUBSET COMPONENT_IDS
]

\* Type definitions for chat messages
ChatMessage == [
    id: MESSAGE_IDS,
    content: MESSAGE_IDS,
    type: CHAT_MESSAGE_TYPES,
    timestamp: 1..10,
    triggeredComponents: SUBSET COMPONENT_IDS
]

\* Type definitions for stage context
StageContextType == [
    currentFocus: CHAT_MESSAGE_TYPES \cup {"GENERAL"},
    activeWorkflow: {"NONE"} \cup COMPONENT_TYPES,
    knowledgeBase: SUBSET MESSAGE_IDS,
    userPreferences: {"DEFAULT"}
]

\* Valid component types for LIMS/science/knowledge system (simplified for model checking)
ValidComponentTypes == {
    "SAMPLE_TRACKER",
    "TEST_CATALOG", 
    "KNOWLEDGE_BASE"
}

\* Valid chat message types that trigger stage updates (simplified for model checking)
ValidChatMessageTypes == {
    "SAMPLE_INQUIRY",
    "TEST_REQUEST",
    "KNOWLEDGE_QUERY",
    "GENERAL_QUERY"
}

\* System states
ValidSystemStates == {
    "INITIALIZING",
    "READY", 
    "PROCESSING_CHAT",
    "UPDATING_STAGE",
    "ERROR",
    "MAINTENANCE"
}

\* Type invariants
TypeInvariant == 
    /\ activeComponents \subseteq StageComponent
    /\ chatHistory \in Seq(ChatMessage)
    /\ stageContext \in StageContextType
    /\ systemState \in ValidSystemStates
    /\ COMPONENT_TYPES = ValidComponentTypes
    /\ CHAT_MESSAGE_TYPES = ValidChatMessageTypes

\* Initial state
Init == 
    /\ activeComponents = {}
    /\ chatHistory = <<>>
    /\ stageContext = [
        currentFocus |-> "GENERAL",
        activeWorkflow |-> "NONE", 
        knowledgeBase |-> {},
        userPreferences |-> "DEFAULT"
       ]
    /\ systemState = "INITIALIZING"

\* Determine which components should be activated for a given message type
DetermineComponentsForMessage(msgType) ==
    CASE msgType = "SAMPLE_INQUIRY" -> {"SAMPLE_TRACKER"}
    [] msgType = "TEST_REQUEST" -> {"TEST_CATALOG"}
    [] msgType = "KNOWLEDGE_QUERY" -> {"KNOWLEDGE_BASE"}
    [] msgType = "GENERAL_QUERY" -> {"KNOWLEDGE_BASE"}

\* Core rule: Every chat message MUST trigger a stage update
\* This is the fundamental invariant of the LIMS stage system
ChatTriggersStageUpdate(msg) ==
    \* For any chat message, there must be at least one component added or updated
    \E component \in StageComponent :
        /\ component.type \in DetermineComponentsForMessage(msg.type)
        /\ component.id \notin {c.id : c \in activeComponents}

\* Process a new chat message
ProcessChatMessage(msg) ==
    /\ systemState = "READY"
    /\ systemState' = "PROCESSING_CHAT"
    /\ chatHistory' = Append(chatHistory, msg)
    /\ UNCHANGED <<activeComponents, stageContext>>

\* Update stage based on processed chat message
UpdateStageFromChat(msg) ==
    /\ systemState = "PROCESSING_CHAT"
    /\ systemState' = "UPDATING_STAGE"
    /\ LET requiredComponents == DetermineComponentsForMessage(msg.type)
           newComponents == {[
               id |-> "comp1",
               type |-> cType,
               data |-> msg.content,
               isVisible |-> TRUE,
               priority |-> 1,
               dependencies |-> {}
           ] : cType \in requiredComponents}
       IN activeComponents' = activeComponents \union newComponents
    /\ stageContext' = [stageContext EXCEPT 
           !.currentFocus = msg.type,
           !.knowledgeBase = @ \union {msg.content}
       ]
    /\ UNCHANGED chatHistory

\* Complete stage update and return to ready state
CompleteStageUpdate ==
    /\ systemState = "UPDATING_STAGE"
    /\ systemState' = "READY"
    /\ UNCHANGED <<activeComponents, chatHistory, stageContext>>

\* Remove a component from the stage
RemoveComponent(componentId) ==
    /\ systemState = "READY"
    /\ \E component \in activeComponents : component.id = componentId
    /\ activeComponents' = {c \in activeComponents : c.id # componentId}
    /\ UNCHANGED <<chatHistory, stageContext, systemState>>

\* Error handling
HandleError ==
    /\ systemState \in {"PROCESSING_CHAT", "UPDATING_STAGE"}
    /\ systemState' = "ERROR"
    /\ UNCHANGED <<activeComponents, chatHistory, stageContext>>

\* Recovery from error
RecoverFromError ==
    /\ systemState = "ERROR"
    /\ systemState' = "READY"
    /\ UNCHANGED <<activeComponents, chatHistory, stageContext>>

\* System initialization complete
CompleteInitialization ==
    /\ systemState = "INITIALIZING"
    /\ systemState' = "READY"
    /\ UNCHANGED <<activeComponents, chatHistory, stageContext>>

\* Next state relation
Next == 
    \/ CompleteInitialization
    \/ \E msg \in ChatMessage : ProcessChatMessage(msg)
    \/ \E msg \in ChatMessage : UpdateStageFromChat(msg)
    \/ CompleteStageUpdate
    \/ \E id \in COMPONENT_IDS : RemoveComponent(id)
    \/ HandleError
    \/ RecoverFromError

\* Specification
Spec == Init /\ [][Next]_<<activeComponents, chatHistory, stageContext, systemState>>

\* SAFETY PROPERTIES

\* The fundamental rule: Every chat message must result in stage updates
ChatAlwaysTriggersStageUpdate ==
    \A i \in DOMAIN chatHistory :
        \E component \in activeComponents :
            /\ component.type \in DetermineComponentsForMessage(chatHistory[i].type)
            /\ component.id = chatHistory[i].id \o "_" \o component.type

\* No more than MAX_COMPONENTS active at once
ComponentLimit == Cardinality(activeComponents) <= MAX_COMPONENTS

\* Chat history never exceeds maximum
ChatHistoryLimit == Len(chatHistory) <= MAX_CHAT_HISTORY

\* All active components must have valid types
ValidActiveComponents == 
    \A component \in activeComponents : component.type \in ValidComponentTypes

\* System state is always valid
ValidSystemState == systemState \in ValidSystemStates

\* LIVENESS PROPERTIES

\* System eventually becomes ready after initialization
EventuallyReady == <>(systemState = "READY")

\* Every chat message eventually triggers stage update
ChatEventuallyProcessed ==
    \A i \in DOMAIN chatHistory :
        \E component \in activeComponents : 
            component.type \in DetermineComponentsForMessage(chatHistory[i].type)

\* System can always recover from errors
CanAlwaysRecover == [](systemState = "ERROR" => <>(systemState = "READY"))

\* COMBINED SAFETY INVARIANT
SafetyInvariant ==
    /\ TypeInvariant
    /\ ComponentLimit  
    /\ ChatHistoryLimit
    /\ ValidActiveComponents
    /\ ValidSystemState

====
