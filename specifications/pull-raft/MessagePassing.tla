--------------------------- MODULE MessagePassing ---------------------------

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          FetchRequest, FetchResponse,
          JoinRequest, JoinResponse

\* Used for filtering messages under different circumstances
CONSTANTS AnyEpoch, EqualEpoch

VARIABLE messages

\* Notes:
\* - There is some nuance here, for newcomers, skip these
\*   helpers and focus on the protocol actions.
\* - Messages are added to a pool of messages in a key/value
\*   fashion where the message is the key and the value is
\*   the delivery count. When the delivery count > 0 it can
\*   be received. When it is 0 is cannot be received. 
\* - In order to prevent some infinite cycles of requests
\*   and responses which increase state space and make liveness
\*   hard to check, some request types only can be sent once.            

\* Send the message even if an identical one was previously sent.
_SendNoRestriction(m) ==
    \/ /\ m \notin DOMAIN messages
       /\ messages' = messages @@ (m :> 1)
    \/ /\ m \in DOMAIN messages
       /\ messages' = [messages EXCEPT ![m] = @ + 1]
    
\* Will only send the message if it hasn't been sent before.
_SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)    

\* Add a message to the bag of messages. 
Send(m) ==
    IF \/ m.mtype = RequestVoteRequest
       \/ m.mtype = BeginQuorumRequest
       \/ m.mtype = JoinRequest
    THEN _SendOnce(m)
    ELSE _SendNoRestriction(m)

\* Will only send the messages if it hasn't done so before
\* Basically disables the parent action once sent.
SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]    

\* Explicit duplicate operator for when we purposefully want message duplication
Duplicate(m) == 
    /\ m \in DOMAIN messages
    /\ messages' = [messages EXCEPT ![m] = @ + 1]

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) ==
    /\ m \in DOMAIN messages
    /\ messages[m] > 0 \* message must exist
    /\ messages' = [messages EXCEPT ![m] = @ - 1]

\* Combination of Send and Discard
\* To prevent infinite empty fetches, we don't allow
\* two identical fetch responses. If an empty fetch response
\* was previously sent in the same epoch, then only when something
\* has changed such as the hwm will a response be sendable.
\* This allows us to avoid infinite fetch request and response cycles
\* and still be able to make progress and check liveness.
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ response.mtype # FetchResponse
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

=============================================================================
\* Modification History
\* Last modified Sat Jul 16 11:19:49 CEST 2022 by GUNMETAL
\* Last modified Sat Jul 16 11:14:02 CEST 2022 by jvanlightly
\* Created Sat Jul 16 11:13:38 CEST 2022 by jvanlightly
