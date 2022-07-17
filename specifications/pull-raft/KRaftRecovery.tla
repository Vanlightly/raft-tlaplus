--------------------------------- MODULE KRaftRecovery ---------------------------------
(*NOTES
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

-----------------------------------------------
Kafka KRaft TLA+ specification with possible recovery mechanism
-----------------------------------------------

See KRaft.tla for main description.

This specification adds to the original by including a recovery mode
where a broker that has lost its data (due to a failed volume for example)
can start-up in recovery mode and rehydrate itself without introducing
unsafe behaviour.

When a node loses its data and comes back with the same identity, it must not
be allowed to vote, else we could end up with data loss. The recovery mechanism
works as follows:

Recovery behaviour
1. Server starts up with 'Recovery mode' enabled.
2. Server sends out a 'quorum metadata request' to 
   all peers. Each peer responds with:
  - its current state (leader, follower etc)
  - current epoch and leader identity
  - the offset and epoch of the last committed log entry 
    (the entry at the high watermark).
2. Server can move to the next step iff the following 
   two conditions are met:
  a) must receive a quorum of responses that are 
     consistent (same epoch, same leader) and that 
     can be used to identify the current leader.
  b) the response from the leader shows that the 
     epoch of its last log entry matches its current epoch.
3. Server sets its 'recovery offset' as the last 
   committed entry offset (aka hwm) of the leader.
4. Transition to Follower. Start sending fetch requests
   to the leader (but from the beginning). While in 
   Recovery mode set a flag to indicate these are 
   recovery fetches (and some checks should not be 
   applied - and the end offset tracking should not
   be updated).
5. Once the recovery offset is reached, switch out 
   of Recovery mode, and fetch requests should no longer
   have the recovery flag set.

Notes of 'recovery offset'
- the recovery offset cannot be based on the high watermark
of the leader, without restriction, because its hwm might
be lower than the server's last offset when it lost its data.
- the recovery offset cannot be based on the last offset
of the leader as this can lead to a liveness issue (see below).
- the recovery offset can be based on the high watermark
of the leader if we can guarantee that the hwm is equal to
or higher than the last offset of the server when it lost
    its data - this is achieved by the high watermark entry
    having an epoch that matches the current epoch.

Potential liveness issue:
- the leader's last offset could be very high and its high
  watermark very low, then it lose leadership and truncate 
  its log massively. The in-recovery server now has a 
  'recovery offset' that is far higher than the new leader's 
  log and reaching that offset could take a very long time.

*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, 
          Unattached, Voted, PreRecovery

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          EndQuorumRequest,
          FetchRequest, FetchResponse,
          MetadataRequest, MetadataResponse

\* Fetch response codes          
CONSTANTS Ok, NotOk, Diverging

\* Errors
CONSTANTS FencedLeaderEpoch, NotLeader, UnknownLeader

\* Special state that indicates a server has entered an illegal state
CONSTANTS IllegalState       

\* Used for filtering messages under different circumstances
CONSTANTS AnyEpoch, EqualEpoch

\* Limiting state space by limiting the number of elections and restarts           
CONSTANTS MaxElections, MaxRestarts, MaxRecoveries
----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages
----
\* Auxilliary variables (used for state-space control, invariants etc)

\* The values that have been received from a client and whether
\* the value has been acked back to the client. Used in invariants to
\* detect data loss.
VARIABLE acked
\* Counter for elections and restarts (to control state space)
VARIABLE electionCtr, restartCtr, recoveryCtr
auxVars == <<acked, electionCtr, restartCtr, recoveryCtr>>
----
\* Per server variables (functions with domain Server).

\* The server's epoch number (the Raft term).
VARIABLE currentEpoch
\* The server's state (Follower, Candidate etc)
VARIABLE state
\* The candidate the server voted for in its current epoch.
VARIABLE votedFor
\* The peer that the server believes is the current leader
VARIABLE leader
\* Tracks the currently pending fetch request of a follower
VARIABLE pendingFetch
serverVars == <<currentEpoch, state, votedFor, leader, pendingFetch>>

\* A Sequence of log entries. The offset into this sequence is the offset of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with offset 1, so be careful not to use that!
VARIABLE log
\* The offset of the latest entry in the log the state machine may apply.
VARIABLE highWatermark
logVars == <<log, highWatermark>>

\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a vote in its
\* currentEpoch.
VARIABLE votesGranted

candidateVars == <<votesGranted>>

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate highWatermark on the leader.
VARIABLE endOffset

leaderVars == <<endOffset>>


\* TRUE when in-recovery
VARIABLE inRecovery
\* the responses to metadata requests
VARIABLE metadataResponses
\* the offset that a server must reach in order to switch
\* out of recovery mode.
VARIABLE recoveryOffset
\* An id (in the absence of an epoch) that identifies one recovery effort.
\* Required for this spec to prevent a server that recovers twice handling
\* a MetadataResponse from a prior recovery.
VARIABLE recoveryId
recoveryVars == <<inRecovery, metadataResponses, recoveryOffset, recoveryId>>
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars,
          recoveryVars, auxVars>>
view == <<messages, serverVars, candidateVars, leaderVars, logVars, 
          recoveryVars, acked >>
symmServers == Permutations(Server)
symmValues == Permutations(Value)
----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The epoch of the last entry in a log, or 0 if the log is empty.
LastEpoch(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].epoch

\* Send the message even if an identical one was previously sent.
\* This can happen with FetchRequests
_SendNoRestriction(m) ==
    \/ /\ m \notin DOMAIN messages
       /\ messages' = messages @@ (m :> 1)
    \/ /\ m \in DOMAIN messages
       /\ messages' = [messages EXCEPT ![m] = @ + 1]
    
\* Will only send the message if it hasn't been sent before.
\* Basically disables the parent action once sent. Allows us to
\* prevent infinite sending without adding an extra variable.
_SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)    

\* Add a message to the bag of messages. 
\* Note 1: to prevent infinite cycles, we allow the
\* sending some types of message once. In this specification
\* we do not need retries, each send is implicitly
\* retried forever as its delivery count remains 1
\* until processed. 
\* Note 2: a message can only match an existing message
\* if it is identical (all fields).
Send(m) ==
    IF \/ m.mtype = RequestVoteRequest
       \/ m.mtype = BeginQuorumRequest
    THEN _SendOnce(m)
    ELSE _SendNoRestriction(m)

\* Will only send the messages if it hasn't done so before
\* Basically disables the parent action once sent.
\* Again, retries are implicit here.
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
\* was previously sent, then only when something has changed
\* such as the hwm will a response be sendable.
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ response.mtype # FetchResponse
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

\* The message is of the type and has a matching epoch.
ReceivableMessage(m, mtype, epoch_match) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ epoch_match = AnyEpoch
       \/ /\ epoch_match = EqualEpoch
          /\ m.mepoch = currentEpoch[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Compares two entries, with epoch taking precedence. 
\* Offset only matters when both have the same epoch.
\* When entry1 > entry2 then 1
\* When entry1 = entry2 then 0
\* When entry1 < entry2 then 1
CompareEntries(offset1, epoch1, offset2, epoch2) ==
    CASE epoch1 > epoch2 -> 1
      [] epoch1 = epoch2 /\ offset1 > offset2 -> 1
      [] epoch1 = epoch2 /\ offset1 = offset2 -> 0
      [] OTHER -> -1

\* finds the highest offset in the log which
\* is <= to the supplied epoch and its last offset
HighestCommonOffset(i, endOffsetForEpoch, epoch) ==
      \* 1) the log is empty so no common offset
    CASE log[i] = <<>> -> 
            [offset |-> 0, epoch |-> 0]
      \* 2) there is no lower entry in the log, so no common offset
      [] ~\E offset \in DOMAIN log[i] :
            CompareEntries(offset, log[i][offset].epoch, 
                           endOffsetForEpoch, epoch) <= 0 -> 
            [offset |-> 0, epoch |-> 0]
      [] OTHER ->
      \* there is a common entry, so choose the highest one 
            LET offset == CHOOSE offset \in DOMAIN log[i] :
                            /\ CompareEntries(offset, log[i][offset].epoch, 
                                              endOffsetForEpoch, epoch) <= 0
                            /\ ~\E offset2 \in DOMAIN log[i] :
                                /\ CompareEntries(offset2, log[i][offset2].epoch, 
                                                  endOffsetForEpoch, epoch) <= 0
                                /\ offset2 > offset
            IN [offset |-> offset, epoch |-> log[i][offset].epoch]  

\* Create a new log, truncated to the highest common entry            
TruncateLog(i, m) ==
    LET highestCommonOffset == HighestCommonOffset(i,
                                                   m.mdivergingEndOffset,
                                                   m.mdivergingEpoch)
    IN IF highestCommonOffset.offset = 0
       THEN <<>>
       ELSE [offset \in 1..highestCommonOffset.offset |-> log[i][offset]]

\* the highest offset in the leader's log that has the same or lower epoch.
EndOffsetForEpoch(i, lastFetchedEpoch) ==
      \* 1) the log is empty so no end offset
    CASE log[i] = <<>> -> 
            [offset |-> 0, epoch |-> 0]
      \* 2) there is no entry at or below the epoch in the log, so no end offset
      [] ~\E offset \in DOMAIN log[i] :
            log[i][offset].epoch <= lastFetchedEpoch -> 
            [offset |-> 0, epoch |-> 0]
      \* 3) there is an entry at or below the epoch in the log,
      \*    so return the highest one
      [] OTHER ->
            LET offset == CHOOSE offset \in DOMAIN log[i] :
                            /\ log[i][offset].epoch <= lastFetchedEpoch
                            /\ ~\E offset2 \in DOMAIN log[i] :
                                /\ log[i][offset2].epoch <= lastFetchedEpoch
                                /\ offset2 > offset
            IN [offset |-> offset, epoch |-> log[i][offset].epoch] 

\* TRUE if the fetch position of the follower is consistent
\* with the log of the leader
ValidFetchPosition(i, m) ==
    \/ /\ m.mfetchOffset = 0
       /\ m.mlastFetchedEpoch = 0 
    \/ LET endOffsetAndEpoch == EndOffsetForEpoch(i, m.mlastFetchedEpoch)
       IN /\ m.mfetchOffset <= endOffsetAndEpoch.offset
          /\ m.mlastFetchedEpoch = endOffsetAndEpoch.epoch

\* Transition helpers ------------------------------

\* TRUE if server i and the peer have a consistent view on leadership,
\* FALSE if not.
HasConsistentLeader(i, leaderId, epoch) ==
    IF leaderId = i /\ currentEpoch[i] = epoch
    THEN \* if the peer thinks I am leader, and I am really leader
         \* then TRUE, else FALSE
         state[i] = Leader
    ELSE \* either the peer doesn't know there is a leader, or this
         \* node doesn't know a leader, or both agree on the same leader,
         \* or they have different epochs
         \/ epoch # currentEpoch[i]
         \/ leaderId = Nil
         \/ leader[i] = Nil
         \/ leader[i] = leaderId

SetIllegalState ==
    [state |-> IllegalState, epoch |-> 0, leader |-> Nil]

NoTransition(i) ==
    [state |-> state[i], epoch |-> currentEpoch[i], leader |-> leader[i]]

TransitionToVoted(i, epoch, state0) ==
    IF /\ state0.epoch = epoch
       /\ state0.state # Unattached
    THEN SetIllegalState
    ELSE [state |-> Voted, epoch |-> epoch, leader |-> Nil]

TransitionToUnattached(epoch) ==
    [state |-> Unattached, epoch |-> epoch, leader |-> Nil]
    
TransitionToFollower(i, leaderId, epoch) ==
    IF /\ currentEpoch[i] = epoch
       /\ \/ state[i] = Follower
          \/ state[i] = Leader
    THEN SetIllegalState
    ELSE [state |-> Follower, epoch |-> epoch, leader |-> leaderId]

MaybeTransition(i, leaderId, epoch) ==
    CASE ~HasConsistentLeader(i, leaderId, epoch) ->
            SetIllegalState
      [] epoch > currentEpoch[i] ->
            \* the epoch of the node is stale, become a follower
            \* if the request contained the leader id, else become
            \* unattached
            IF leaderId = Nil
            THEN TransitionToUnattached(epoch)
            ELSE TransitionToFollower(i, leaderId, epoch)
      [] leaderId # Nil /\ leader[i] = Nil ->
            \* the request contained a leader id and this node does not know
            \* of a leader, so become a follower of that leader
            TransitionToFollower(i, leaderId, epoch)
      [] OTHER ->
            \* no changes
            NoTransition(i)

MaybeHandleCommonResponse(i, leaderId, epoch, errors) ==
    CASE state[i] = PreRecovery ->
                \* not ready to join cluster operations yet, do nothing
                [state   |-> state[i],
                 epoch   |-> currentEpoch[i], 
                 leader  |-> leader[i],
                 handled |-> TRUE]
      [] epoch < currentEpoch[i] ->
                \* stale epoch, do nothing
                [state |-> state[i],
                 epoch |-> currentEpoch[i],
                 leader |-> leader[i],
                 handled |-> TRUE]
      [] epoch > currentEpoch[i] \/ errors # Nil ->
                \* higher epoch or an error
                MaybeTransition(i, leaderId, epoch) @@ [handled |-> TRUE]
      [] /\ epoch = currentEpoch[i]
         /\ leaderId # Nil
         /\ leader[i] = Nil ->
                \* become a follower
                [state   |-> Follower, 
                 leader  |-> leaderId,
                 epoch   |-> currentEpoch[i],
                 handled |-> TRUE]
      [] OTHER -> 
                \* no changes to state or leadership
                [state   |-> state[i],
                 epoch   |-> currentEpoch[i], 
                 leader  |-> leader[i],
                 handled |-> FALSE]
         
----
\* Define initial values for all variables

InitServerVars == /\ currentEpoch = [i \in Server |-> 1]
                  /\ state        = [i \in Server |-> Unattached]
                  /\ leader       = [i \in Server |-> Nil]
                  /\ votedFor     = [i \in Server |-> Nil]
                  /\ pendingFetch = [i \in Server |-> Nil]
InitCandidateVars == /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ endOffset  = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log           = [i \in Server |-> << >>]
               /\ highWatermark = [i \in Server |-> 0]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ recoveryCtr = 0
               /\ acked = [v \in Value |-> Nil]
InitRecoveryVars ==
    /\ inRecovery        = [i \in Server |-> FALSE]
    /\ metadataResponses = [i \in Server |-> {}]
    /\ recoveryOffset    = [i \in Server |-> Nil]
    /\ recoveryId        = [i \in Server |-> Nil]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitAuxVars
        /\ InitRecoveryVars

----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentEpoch, leader and log.
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state'         = [state EXCEPT ![i] = Follower]
    /\ leader'        = [leader EXCEPT ![i] = Nil]
    /\ votesGranted'  = [votesGranted EXCEPT ![i] = {}]
    /\ endOffset'     = [endOffset EXCEPT ![i] = [j \in Server |-> 0]]
    /\ highWatermark' = [highWatermark EXCEPT ![i] = 0]
    /\ pendingFetch'  = [pendingFetch EXCEPT ![i] = Nil]
    /\ restartCtr'    = restartCtr + 1
    /\ UNCHANGED <<messages, currentEpoch, votedFor, recoveryVars, log, acked,
                   electionCtr, recoveryCtr>>

\* ACTION: RequestVote -----------------------------------------------
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ electionCtr < MaxElections 
    /\ state[i] \in {Follower, Candidate, Unattached, Voted}
    /\ inRecovery[i] = FALSE \* cannot start an election if its in-recovery
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentEpoch' = [currentEpoch EXCEPT ![i] = currentEpoch[i] + 1]
    /\ leader'       = [leader EXCEPT ![i] = Nil]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
    /\ electionCtr'  = electionCtr + 1
    /\ SendMultipleOnce(
           {[mtype          |-> RequestVoteRequest,
             mepoch         |-> currentEpoch[i] + 1,
             mlastLogEpoch  |-> LastEpoch(log[i]),
             mlastLogOffset |-> Len(log[i]),
             msource        |-> i,
             mdest          |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<recoveryVars, acked, leaderVars, logVars, restartCtr, recoveryCtr>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j.
\* Server i will vote for j if:
\* 1) it is not in recovery
\* 2) epoch of j >= epoch of i
\* 3) last entry of i is <= to the last entry of j
\* 4) i has not already voted for a different server
HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               state0   == IF state[i] # PreRecovery /\ m.mepoch > currentEpoch[i]
                           THEN TransitionToUnattached(m.mepoch)
                           ELSE NoTransition(i)
               logOk == CompareEntries(m.mlastLogOffset,
                                       m.mlastLogEpoch,
                                       Len(log[i]),
                                       LastEpoch(log[i])) >= 0
               grant == /\ inRecovery[i] = FALSE \* cannot grant a vote if its in-recovery
                        /\ \/ state0.state = Unattached
                           \/ /\ state0.state = Voted
                              /\ votedFor[i] = j
                        /\ logOk
               finalState == IF grant /\ state0.state = Unattached
                             THEN TransitionToVoted(i, m.mepoch, state0)
                             ELSE state0                         
            IN /\ IF error = Nil
                  THEN
                       /\ state' = [state EXCEPT ![i] = finalState.state]
                       /\ currentEpoch' = [currentEpoch EXCEPT ![i] = finalState.epoch]
                       /\ leader' = [leader EXCEPT ![i] = finalState.leader]
                       /\ \/ /\ grant
                             /\ votedFor' = [votedFor EXCEPT ![i] = j]
                          \/ /\ ~grant
                             /\ UNCHANGED votedFor
                       /\ IF state # state'
                          THEN pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                          ELSE UNCHANGED pendingFetch
                       /\ Reply([mtype         |-> RequestVoteResponse,
                                 mepoch        |-> m.mepoch,
                                 mleader       |-> finalState.leader,
                                 mvoteGranted  |-> grant,
                                 merror        |-> Nil,
                                 msource       |-> i,
                                 mdest         |-> j], m)
                  ELSE /\ Reply([mtype         |-> RequestVoteResponse,
                                 mepoch        |-> currentEpoch[i],
                                 mleader       |-> leader[i],
                                 mvoteGranted  |-> FALSE,
                                 merror        |-> error,
                                 msource       |-> i,
                                 mdest         |-> j], m)
                       /\ UNCHANGED << serverVars>>
               /\ UNCHANGED <<recoveryVars, candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j.
\* If the response is stale the server i will not register the vote
\* either way.
HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ IF newState.handled = TRUE
                 THEN /\ state' = [state EXCEPT ![i] = newState.state]
                      /\ leader' = [leader EXCEPT ![i] = newState.leader]
                      /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                      /\ UNCHANGED <<votesGranted>>
                 ELSE
                      /\ state[i] = Candidate
                      /\ \/ /\ m.mvoteGranted
                            /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                      votesGranted[i] \cup {j}]
                         \/ /\ ~m.mvoteGranted
                            /\ UNCHANGED <<votesGranted>>
                      /\ UNCHANGED <<state, leader, currentEpoch>>
              /\ Discard(m)
              /\ UNCHANGED <<votedFor, pendingFetch, recoveryVars, leaderVars, logVars, 
                             auxVars>>               

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader and notifies all peers of its
\* leadership via the BeginQuorumRequest.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'  = [state EXCEPT ![i] = Leader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ endOffset' = [endOffset EXCEPT ![i] = [j \in Server |-> 0]]
    /\ SendMultipleOnce(
          {[mtype    |-> BeginQuorumRequest,
            mepoch   |-> currentEpoch[i],
            msource  |-> i,
            mdest    |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<currentEpoch, votedFor, pendingFetch, recoveryVars,
                   candidateVars, auxVars, logVars>>

\* ACTION: HandleBeginQuorumRequest -------------------------------------------
\* A server receives a BeginQuorumRequest and transitions to a follower
\* unless the message is stale.
\* Note: this action is only enabled when not in state PendingRecoveryOffset. The
\* reason for this is that the server cannot become a follower until
\* it can discover its recovery offset. In the implementation it can
\* respond with an error code that indicates its recovery state.
HandleBeginQuorumRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, BeginQuorumRequest, AnyEpoch)
        /\ state[m.mdest] # PreRecovery \* only respond when not in first stage of recovery (see above)
        /\ LET i        == m.mdest
               j        == m.msource
               error    == IF m.mepoch < currentEpoch[i]
                           THEN FencedLeaderEpoch
                           ELSE Nil
               newState == MaybeTransition(i, m.msource, m.mepoch)
           IN IF error = Nil
              THEN
                   /\ state' = [state EXCEPT ![i] = newState.state]
                   /\ leader' = [leader EXCEPT ![i] = newState.leader]
                   /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
                   /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
                   /\ Reply([mtype      |-> BeginQuorumResponse,
                             mepoch     |-> m.mepoch,
                             msource    |-> i,
                             mdest      |-> j,
                             merror     |-> Nil], m)
              ELSE /\ Reply([mtype      |-> BeginQuorumResponse,
                             mepoch     |-> currentEpoch[i],
                             msource    |-> i,
                             mdest      |-> j,
                             merror     |-> error], m)
                   /\ UNCHANGED <<state, leader, currentEpoch, pendingFetch>>
        /\ UNCHANGED <<votedFor, recoveryVars, log, candidateVars,
                       leaderVars, highWatermark, auxVars>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ LET entry == [epoch |-> currentEpoch[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
    /\ UNCHANGED <<messages, serverVars, candidateVars, recoveryVars,
                   leaderVars, highWatermark, electionCtr, restartCtr, recoveryCtr>>
                       
\* ACTION: SendFetchRequest ----------------------------------------
\* Follower i sends leader j a FetchRequest.
SendFetchRequest(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ leader[i] = j
    /\ pendingFetch[i] = Nil
    /\ LET lastLogOffset == Len(log[i])
           lastLogEpoch == IF lastLogOffset > 0 
                           THEN log[i][lastLogOffset].epoch
                           ELSE 0
           fetchMsg     == [mtype             |-> FetchRequest,
                            mepoch            |-> currentEpoch[i],
                            mfetchOffset      |-> lastLogOffset,
                            mlastFetchedEpoch |-> lastLogEpoch,
                            mrecovery         |-> inRecovery[i],
                            msource           |-> i,
                            mdest             |-> j]
       IN /\ pendingFetch' = [pendingFetch EXCEPT ![i] = fetchMsg]
          /\ Send(fetchMsg)
    /\ UNCHANGED <<currentEpoch, state, votedFor, leader, recoveryVars,
                   candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: RejectFetchRequest -------------------
\* Server i rejects a FetchRequest due to either:
\* - i is not a leader
\* - the message epoch is lower than the server epoch
\* - the message epoch is higher than the server epoch
RejectFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, AnyEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               error               == CASE state[i] # Leader -> NotLeader
                                        [] m.mepoch < currentEpoch[i] -> FencedLeaderEpoch
                                        [] m.mepoch > currentEpoch[i] -> UnknownLeader
                                        [] OTHER -> Nil
           IN  /\ error # Nil
               /\ Reply([mtype       |-> FetchResponse,
                         mresult     |-> NotOk,
                         merror      |-> error,
                         mleader     |-> leader[i],
                         mepoch      |-> currentEpoch[i],
                         mhwm        |-> highWatermark[i],
                         msource     |-> i,
                         mdest       |-> j,
                         correlation |-> m], m)
               /\ UNCHANGED <<candidateVars, leaderVars, serverVars, 
                              recoveryVars, logVars, auxVars>>

\* ACTION: DivergingFetchRequest -------------------
\* Leader i receives a FetchRequest from an inconsistent log
\* position so it responds with the highest offset that matches
\* the epoch of the followe fetch position so it can truncate its
\* log and start fetching from a consistent offset.
DivergingFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               valid               == ValidFetchPosition(i, m)
               validOffsetAndEpoch == EndOffsetForEpoch(i, m.mlastFetchedEpoch)
           IN  /\ state[i] = Leader
               /\ ~valid 
               /\ Reply([mtype               |-> FetchResponse,
                         mepoch              |-> currentEpoch[i],
                         mresult             |-> Diverging,
                         merror              |-> Nil,
                         mdivergingEpoch     |-> validOffsetAndEpoch.epoch,
                         mdivergingEndOffset |-> validOffsetAndEpoch.offset,
                         mleader             |-> leader[i],
                         mhwm                |-> highWatermark[i],
                         msource             |-> i,
                         mdest               |-> j,
                         correlation         |-> m], m)
               /\ UNCHANGED <<candidateVars, leaderVars, serverVars, 
                              recoveryVars, logVars, auxVars>>

\* ACTION: AcceptFetchRequest ------------------
\* Leader i receives a FetchRequest from a valid position
\* and responds with an entry if there is one or an empty
\* response if not.
\* The leader updates the end offset of the fetching peer
\* and advances the high watermark if it can.
\* It can only advance the high watermark to an entry of the
\* current epoch. 
NewHighwaterMark(i, newEndOffset) ==
    LET Agree(offset) == {i} \cup {k \in Server :
                            /\ newEndOffset[k] >= offset }
        \* The maximum offsets for which a quorum agrees
        agreeOffsets  == {offset \in 1..Len(log[i]) : 
                            Agree(offset) \in Quorum}
    IN 
        IF /\ agreeOffsets # {}
           /\ log[i][Max(agreeOffsets)].epoch = currentEpoch[i]
        THEN
            Max(agreeOffsets)
        ELSE
            highWatermark[i]

AcceptFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i       == m.mdest
               j       == m.msource
               valid   == ValidFetchPosition(i, m)
               offset  == m.mfetchOffset + 1
               entries == IF offset > Len(log[i])
                          THEN <<>>
                          ELSE <<log[i][offset]>>
           IN 
              /\ state[i] = Leader
              /\ valid
              /\ LET newEndOffset == [endOffset[i] EXCEPT ![j] = m.mfetchOffset]
                     newHwm == IF m.mrecovery = FALSE
                               THEN NewHighwaterMark(i, newEndOffset)
                               ELSE highWatermark[i]
                 IN
                    /\ \/ /\ m.mrecovery = FALSE
                          /\ endOffset' = [endOffset EXCEPT ![i] = newEndOffset]
                          /\ highWatermark' = [highWatermark EXCEPT ![i] = newHwm]
                          /\ acked' = [v \in Value |-> 
                                          IF acked[v] = FALSE
                                          THEN v \in { log[i][ind].value : ind \in highWatermark[i]+1..newHwm }
                                          ELSE acked[v]]
                       \/ UNCHANGED <<endOffset, highWatermark, acked>>
                    /\ Reply([mtype       |-> FetchResponse,
                              mepoch      |-> currentEpoch[i],
                              mleader     |-> leader[i],
                              mresult     |-> Ok,
                              merror      |-> Nil,
                              mentries    |-> entries,
                              mhwm        |-> Min({newHwm, offset}),
                              msource     |-> i,
                              mdest       |-> j,
                              correlation |-> m], m)
                    /\ UNCHANGED <<candidateVars, currentEpoch, log, state, votedFor,
                                   pendingFetch, leader, recoveryVars, electionCtr, 
                                   restartCtr, recoveryCtr>>
       
\* ACTION: HandleSuccessFetchResponse
\* Follower i receives a valid Fetch response from server j
\* and appends any entries to its log and updates its
\* high watermark.
MayBeSwitchOutOfRecovery(i, m) ==
    IF /\ inRecovery[i] = TRUE
       /\ state[i] = Follower
       /\ recoveryOffset[i] <= Len(log[i]) + Len(m.mentries)
    THEN /\ inRecovery'        = [inRecovery EXCEPT ![i] = FALSE]
         /\ metadataResponses' = [metadataResponses EXCEPT ![i] = {}]
         /\ recoveryOffset'    = [recoveryOffset EXCEPT ![i] = Nil]
         /\ recoveryId'        = [recoveryId EXCEPT ![i] = Nil]
    ELSE UNCHANGED <<recoveryVars>>

HandleSuccessFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN /\ state[i] = Follower
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Ok
              /\ highWatermark'  = [highWatermark  EXCEPT ![i] = m.mhwm]
              /\ IF Len(m.mentries) > 0
                 THEN log' = [log EXCEPT ![i] = Append(@, m.mentries[1])]
                 ELSE UNCHANGED log      
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ MayBeSwitchOutOfRecovery(i, m)
              /\ Discard(m)
              /\ UNCHANGED <<currentEpoch, state, leader, votedFor, 
                             candidateVars, endOffset, auxVars>>

\* ACTION: HandleDivergingFetchResponse
\* Follower i receives a Fetch response from server j and the response
\* indicates that the fetch position is inconsistent. The response includes 
\* the highest offset of the last common epoch the leader and follower share,
\* so the follower truncates its log to the highest entry it has at or below that
\* point which will be the highest common entry that the leader and follower share.
\* After this it can send another FetchRequest to the leader from a valid fetch position.
HandleDivergingFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ state[i] = Follower
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Diverging
              /\ log' = [log EXCEPT ![i] = TruncateLog(i, m)]
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil] 
              /\ Discard(m)
        /\ UNCHANGED <<currentEpoch, state, leader, votedFor, recoveryVars, 
                       candidateVars, leaderVars, highWatermark, auxVars>>
                       
\* ACTION: HandleErrorFetchResponse
\* Server i receives a FetchResponse with an error from server j with
\* Depending on the error, the follower may transition to being unattached
\* or being the follower of a new leader that it was no aware of.
HandleErrorFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ state[i] = Follower
              /\ newState.handled = TRUE
              /\ pendingFetch[i] = m.correlation
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Discard(m)
        /\ UNCHANGED <<votedFor, recoveryVars, candidateVars, leaderVars, 
                       logVars, auxVars>>                       

\* ACTION: Restart In-Recovery
RestartInRecovery(i) ==
    /\ recoveryCtr < MaxRecoveries
    /\ state'             = [state EXCEPT ![i] = PreRecovery]
    /\ currentEpoch'      = [currentEpoch EXCEPT ![i] = 0]
    /\ leader'            = [leader EXCEPT ![i] = Nil]
    /\ votedFor'          = [leader EXCEPT ![i] = Nil]
    /\ pendingFetch'      = [pendingFetch EXCEPT ![i] = Nil]
    /\ highWatermark'     = [highWatermark EXCEPT ![i] = 0]
    /\ log'               = [log EXCEPT ![i] = <<>>]
    /\ votesGranted'      = [votesGranted EXCEPT ![i] = {}]
    /\ endOffset'         = [endOffset EXCEPT ![i] = [j \in Server |-> 0]]
    /\ inRecovery'        = [inRecovery EXCEPT ![i] = TRUE]
    /\ recoveryId'        = [recoveryId EXCEPT ![i] = recoveryCtr + 1]
    /\ metadataResponses' = [metadataResponses EXCEPT ![i] = {}]
    /\ recoveryOffset'    = [recoveryOffset EXCEPT ![i] = Nil]
    /\ recoveryCtr'       = recoveryCtr + 1
    /\ SendMultipleOnce(
           {[mtype       |-> MetadataRequest,
             msource     |-> i,
             mdest       |-> j,
             mrecoveryId |-> recoveryCtr + 1] : j \in Server \ {i}})
    /\ UNCHANGED <<acked, electionCtr, restartCtr>>    

\* ACTION: HandleMetadataRequest
\* Note: to avoid the need for explicitly modelling retries
\* in this spec, the server does not respond unless:
\* - it knows who the leader is
\* - has an entry of the current epoch in its log if it is the leader
\* This prevents the need for an explicit retry mechanism
HandleMetadataRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, MetadataRequest, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
           IN /\ leader[i] # Nil
              /\ IF state[i] = Leader
                 THEN LastEpoch(log[i]) = currentEpoch[i]
                 ELSE TRUE
              /\ Reply([mtype         |-> MetadataResponse,
                        mepoch        |-> currentEpoch[i],
                        mleader       |-> leader[i],
                        mHwmLogEpoch  |-> LastEpoch(log[i]),
                        mHwmLogOffset |-> Len(log[i]),
                        mrecoveryId   |-> m.mrecoveryId,
                        msource       |-> i,
                        mdest         |-> j], m)
        /\ UNCHANGED <<serverVars, candidateVars, leaderVars, 
                       logVars, recoveryVars, auxVars>>

\* ACTION: HandleMetadataResponse

\* A consistent quorum is reached when:
\* 1. A majority quorum of responses agree with each other 
\*    on the current leader and epoch and 
\* 2. One of the responses is from the indicated leader
\*    and it has a committed entry of the current epoch.
IsConsistentQuorum(r) ==
    /\ Cardinality(r) >= (Cardinality(Server) \div 2) + 1
    /\ \A r1, r2 \in r :
        /\ r1.mepoch = r2.mepoch
        /\ r1.mleader = r2.mleader
        /\ r1.mleader # Nil
    /\ \E res \in r : res.msource = res.mleader
    /\ LET leaderRes == CHOOSE res \in r : res.msource = res.mleader
       IN leaderRes.mHwmLogEpoch = leaderRes.mepoch

ConsistentQuorum(allResponses) ==
    IF \E r \in SUBSET allResponses : IsConsistentQuorum(r)
    THEN CHOOSE r \in SUBSET allResponses : IsConsistentQuorum(r)
    ELSE Nil

HandleMetadataResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, MetadataResponse, AnyEpoch)
        /\ LET i                == m.mdest
               j                == m.msource
               allResponses     == metadataResponses[i] \union {m}
               consistentQuorum == ConsistentQuorum(allResponses)
           IN /\ recoveryId[i] = m.mrecoveryId
              /\ inRecovery[i] = TRUE
              /\ state[i] = PreRecovery
              /\ IF consistentQuorum # Nil
                 THEN  LET leaderRes == CHOOSE res \in consistentQuorum : res.msource = res.mleader
                       IN 
                          \* then switch to being a follower in recovery
                          /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = leaderRes.mHwmLogOffset]
                          /\ metadataResponses' = [metadataResponses EXCEPT ![i] = allResponses]
                          /\ state' = [state EXCEPT ![i] = Follower]
                          /\ leader' = [leader EXCEPT ![i] = leaderRes.mleader]
                          /\ currentEpoch' = [currentEpoch EXCEPT ![i] = leaderRes.mepoch]
                 ELSE /\ metadataResponses' = [metadataResponses EXCEPT ![i] = allResponses]
                      /\ UNCHANGED <<recoveryOffset, state, leader, currentEpoch>>
              /\ Discard(m)
              /\ UNCHANGED <<votedFor, pendingFetch, inRecovery, recoveryId,
                             leaderVars, candidateVars, logVars, auxVars>>
              
----
\* Network state transitions

\* The network duplicates a message
\* There is no state-space control for this action, it causes
\* infinite state space
DuplicateMessage(m) ==
    /\ Duplicate(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* The network drops a message
\* In reality is not required as the specification
\* does not force any server to receive a message, so we
\* already get this for free.
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

----
\* Defines how the variables may transition.
Next == 
        \/ \E i \in Server : Restart(i)
        \* elections
        \/ \E i \in Server : RequestVote(i)
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \/ \E i \in Server : BecomeLeader(i)
        \* leader actions
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ RejectFetchRequest
        \/ DivergingFetchRequest
        \/ AcceptFetchRequest
        \* follower actions
        \/ HandleBeginQuorumRequest
        \/ \E i,j \in Server : SendFetchRequest(i, j)
        \/ HandleSuccessFetchResponse
        \/ HandleDivergingFetchResponse
        \/ HandleErrorFetchResponse
        \* recovery
        \/ \E i \in Server : RestartInRecovery(i)
        \/ HandleMetadataRequest
        \/ HandleMetadataResponse
        
\*        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.

NoStuttering ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars

LivenessSpec == Init /\ [][Next]_vars /\ NoStuttering

----
\* LIVENESS -------------------------

\* ValuesNotStuck -----------------
\* A client value will either get committed and be
\* fully replicated or it will be truncated and
\* not be found on any server log.
\* Note that due to the number of elections being limited,
\* the last possible election could fail and prevent
\* progress, so this liveness formula only apples in cases
\* a behaviour does not end with all elections used up
\* and no elected leader.
ValueInServerLog(i, v) ==
    \E index \in DOMAIN log[i] :
        log[i][index].value = v

ValueAllOrNothing(v) ==
    IF /\ electionCtr = MaxElections
       /\ ~\E i \in Server : state[i] = Leader
    THEN TRUE
    ELSE \/ \A i \in Server : ValueInServerLog(i, v)
         \/ ~\E i \in Server : ValueInServerLog(i, v)

ValuesNotStuck ==
    \A v \in Value : []<>ValueAllOrNothing(v)

\* RehydrationCompletes
RehydrationCompletes ==
    \A i \in Server : 
        inRecovery[i] = TRUE
        ~>
        \/ /\ electionCtr = MaxElections
           /\ ~\E j \in Server : state[j] = Leader
        \/ inRecovery[i] = FALSE

\*        \/ /\ leader[i] # Nil
\*              /\ IF state[i] = Leader
\*                 THEN LastEpoch(log[i]) = currentEpoch[i]
\*                 ELSE TRUE  

\* INVARIANTS -------------------------

\* INV: NoIllegalState
\* If a server enters an illegal state then something went wrong.
\* An IllegalState should not be possible.
NoIllegalState ==
    ~\E i \in Server :
        state[i] = IllegalState

\* INV: NoLogDivergence
\* Each log offset is consistent across all servers (on those
\* servers whose highWatermark is equal or higher than the offset).
MinHighWatermark(s1, s2) ==
    IF highWatermark[s1] < highWatermark[s2]
    THEN highWatermark[s1]
    ELSE highWatermark[s2]

NoLogDivergence ==
    \A s1, s2 \in Server :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowestCommonHWM == MinHighWatermark(s1, s2)
            IN IF lowestCommonHWM > 0
               THEN \A offset \in 1..lowestCommonHWM : log[s1][offset] = log[s2][offset]
               ELSE TRUE

\* INV: Used in debugging
TestInv ==
    TRUE

\* INV: NeverTwoLeadersInSameEpoch
\* We cannot have two servers having a conflicting
\* view on who the leader is in the same epoch    
NeverTwoLeadersInSameEpoch ==    
    ~\E i, j \in Server :
        /\ leader[i] # Nil
        /\ leader[j] # Nil
        /\ leader[i] # leader[j]
        /\ currentEpoch[i] = currentEpoch[j]

\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
LeaderHasAllAckedValues ==
    \* for every acknowledged value
    \A v \in Value :
        IF acked[v] = TRUE
        THEN
            \* there does not exist a server that
            ~\E i \in Server :
                \* is a leader
                /\ state[i] = Leader
                \* and which is the newest leader (aka not stale)
                /\ ~\E l \in Server : 
                    /\ l # i
                    /\ currentEpoch[l] > currentEpoch[i]
                \* and that is missing the value
                /\ ~\E offset \in DOMAIN log[i] :
                    log[i][offset].value = v
        ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ highWatermark[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ highWatermark[i] > 0
           /\ \E quorum \in SUBSET Server :
               /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= highWatermark[i]
                   /\ log[j][highWatermark[i]] = log[i][highWatermark[i]]
    ELSE TRUE

===============================================================================

\* Changelog:
