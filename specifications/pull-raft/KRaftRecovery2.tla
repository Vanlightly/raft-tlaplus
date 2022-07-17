--------------------------------- MODULE KRaftRecovery2 ---------------------------------
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


For correctness, the minimum condition we require is that the 
recovered node must re-replicate all of the state it had prior 
to failure before participating in elections. Since we have no 
way of knowing what that state was, we are looking for a 
sufficient condition to guarantee it. The one we propose 
here is the following:

1. Find a leader and epoch which is recognized by a majority 
of non-recovering nodes.
2. Ensure that a majority of non-recovering nodes have reached 
the log end offset of the found leader.

Note that when a leader is first elected, it immediately writes 
a LeaderChange control record to its log. So verifying that a 
majority of nodes have reached the current log end offset of 
the leader also ensures that the leader has committed data in 
its own epoch.

Currently we have no API implemented which lets us inspect the 
log end offset of followers. However, we do have existing APIs 
which are straightforward to implement for KRaft. The one we 
propose here is OffsetForLeaderEpoch, which gives us a way to 
find the end offset corresponding to a given epoch.

Implementation
In terms of implementation, we will implement a new Recovering 
state which will be added to the state machine. Here is a quick 
sketch of the state that the recovering node will maintain:

class RecoveringState implements EpochState {
  final int epoch;
  final Set<Integer> voters;

  // The current leader if known
  OptionalInt currentLeader = OptionalInt.empty();

  // The log end offset of the current leader once known
  long recoveryOffset = -1;

  // The set of voters which have replicated up to `recoveryOffset`.
  // This always includes the current leader once the recovery
  // offset is known and never includes the local voter ID.
  Set<Int> votersReachedRecoveryOffset;

  @Override
  boolean canGrantVote(int candidateId, boolean isLogUpToDate) {
    // All votes are rejected while in recovery
    return false;
  }
}
This state is immediately entered when the recovering node starts up. 
There are two possible transitions from this state:

Recovering -> Recovering: If a new election takes place, then the 
RecoveringState will be reinitialized with a new epoch and leader. 
The recovering node will reset the recoveryOffset as well as 
votersReachedRecoveryOffset and repeat the work in the new epoch.

Recovering -> Follower: If the size of votersReachedRecoveryOffset 
is greater than or equal to a majority of the voters and if the 
local state has reached the recoveryOffset, then we will transition 
to a normal follower of the current leader in the same epoch.

As with the existing states, the recovering node has some work to 
do in order to keep up with current quorum activity. The following 
logic would be implemented in a pollRecovering method in 
KafkaRaftClient:
- If the current leader is not known, send Fetch with 
replicaId=-1  to a random voter in order to find the current leader.
- If the leader is known, then we will send Fetch requests 
with replicaId=-1 to the current leader. This lets the node 
begin catching up and also ensures that we get timely 
notification of leader changes.
- If the leader is known, but no recoveryOffset has been set, 
then send OffsetForLeaderEpoch to the leader with the current epoch.
- If the recoveryOffset is known, then begin sending Fetch 
requests to the current leader in order to catch up. Also 
send OffsetForLeaderEpoch to remaining non-leader voters to 
determine if they have caught up to the recoveryOffset.

OffsetForLeaderEpoch Handling
On receiving an OffsetForLeaderEpoch request, a node will inspect 
its local epoch cache to find the end offset for the requested epoch. 
As we do in the broker handling of this request, when the requested 
epoch matches the current epoch, then the node will return its 
current log end offset. If a recovering node receives this request, 
then it will return UNKNOWN_LEADER_EPOCH. This handles the case 
when the operator tries to recover multiple nodes at the same 
time: the state from a recovering node cannot be used to get 
another node out of recovery.

On receiving an OffsetForLeaderEpoch response, the recovering 
node will do the following:

1. Verify that the response does not indicate an error
2. Verify that the epoch in the response matches the current epoch
3. Check whether the response is from the current leader:

If so, then set recoveryOffset as the end offset from the response. 
Also add the leader to votersReachedRecoveryOffset.

Otherwise, check whether the end offset in the response is 
larger than the recovery offset. If it is, then the node 
will be added to votersReachedRecoveryOffset.

If the node is added to votersReachedRecoveryOffset, 
then check whether this set contains a majority of voters. 
If so, check whether the local node has also caught up to 
recoveryOffset. If both conditions are satisfied, then 
transition to Follower.

Fetch Request Handling
As in the handling of OffsetForLeaderEpoch, nodes which are 
recovering will not respond to Fetch requests. This is handled 
automatically since only leaders respond to Fetch requests 
in the current implementation.

On receiving a Fetch response, the recovering node will do 
the following:

1. Verify that the response does not indicate an error.
2. If the response indicates a higher leader epoch, then 
we will transition to Recovering with the new epoch.

If the response indicates a previously unknown leader in 
the current epoch, then we will set the current leader in 
RecoveringState.

Once the data has been written and flushed to disk, check 
whether the recoveryOffset has been reached. If so, then 
check whether votersReachedRecoveryOffset contains a 
majority of voters

Vote Request Handling
Recovering voters will reject all vote requests. Additionally, 
recovering nodes will not become candidates. In many ways, 
they act like observers until they transition out of the 
Recovering state.

*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, 
          Unattached, Voted, Recovering

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          EndQuorumRequest,
          FetchRequest, FetchResponse,
          DFetchRequest, DFetchResponse,
          OffsetForLeaderEpochRequest, OffsetForLeaderEpochResponse

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
VARIABLE pendingReply
serverVars == <<currentEpoch, state, votedFor, leader, pendingReply>>

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

\* the offset that a server must reach in order to switch
\* out of recovery mode.
VARIABLE recoveryOffset
recoveryVars == <<recoveryOffset>>
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

\* Add a message to the bag of messages. 
\* Note 1: to prevent infinite cycles, we allow the
\* sending some types of message once. In this specification
\* we do not need retries, each send is implicitly
\* retried forever as its delivery count remains 1
\* until processed. 
\* Note 2: a message can only match an existing message
\* if it is identical (all fields).
Send(m) ==
    \/ /\ m \notin DOMAIN messages
       /\ messages' = messages @@ (m :> 1)
    \/ /\ m \in DOMAIN messages
       /\ messages' = [messages EXCEPT ![m] = @ + 1]
    
DiscardAndSend(discard, send) ==
    LET without == [messages EXCEPT ![discard] = 0]
    IN  
        \/ /\ send \notin DOMAIN without
           /\ messages' = without @@ (send :> 1)
        \/ /\ send \in DOMAIN without
           /\ messages' = [without EXCEPT ![send] = @ + 1]
        
\* Will only send the messages if it hasn't done so before
\* Basically disables the parent action once sent.
SendMultipleOnce(msgs) ==
    /\ \A m \in msgs : m \notin DOMAIN messages
    /\ messages' = messages @@ [msg \in msgs |-> 1]    

DiscardAndSendMultiple(discard, msgs) ==
    LET without == [messages EXCEPT ![discard] = 0]
    IN
        /\ \A m \in msgs : m \notin DOMAIN without
        /\ messages' = without @@ [msg \in msgs |-> 1] 

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

SetPendingReplies(i, pending) ==
    pendingReply' = [pendingReply EXCEPT ![i] = pending]

AddPendingReply(i, m) ==
    pendingReply' = [pendingReply EXCEPT ![i] = @ \union {m}]

UpdatePendingReplies(i, receivedMsgs, pendingMsgs) ==
    pendingReply' = [pendingReply EXCEPT ![i] = (@ \union pendingMsgs) \ receivedMsgs]

ClearPendingReplies(i) ==
    pendingReply' = [pendingReply EXCEPT ![i] = {}]
    
ExpectingReply(i, m) ==
    m.mcorrelation \in pendingReply[i]
    
NoPendingReplies(i) ==
    pendingReply[i] = {} 

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

TransitionToRecovering(i, leaderId, epoch) ==
    \* else can result in inconsistent view of leader in same epoch
    IF leaderId = i 
    THEN [state          |-> Recovering, 
          epoch          |-> currentEpoch[i],
          leader         |-> leader[i],
          recoveryOffset |-> Nil]
    ELSE [state          |-> Recovering, 
          epoch          |-> epoch,
          leader         |-> leaderId,
          recoveryOffset |-> Nil]

MaybeTransition(i, leaderId, epoch) ==
    CASE ~HasConsistentLeader(i, leaderId, epoch) ->
            SetIllegalState
      [] epoch > currentEpoch[i] ->
            \* the epoch of the node is stale, become a follower
            \* if the request contained the leader id, else become
            \* unattached
            CASE state[i] = Recovering ->
                    TransitionToRecovering(i, leaderId, epoch)
              [] leaderId = Nil ->
                    TransitionToUnattached(epoch)
              [] OTHER -> TransitionToFollower(i, leaderId, epoch)
      [] state[i] # Recovering /\ leaderId # Nil /\ leader[i] = Nil ->
            \* the request contained a leader id and this node does not know
            \* of a leader, so become a follower of that leader
            TransitionToFollower(i, leaderId, epoch)
      [] OTHER ->
            \* no changes
            NoTransition(i)

MaybeHandleCommonResponse(i, leaderId, epoch, errors) ==
    CASE epoch < currentEpoch[i] ->
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
                [state   |-> IF state[i] = Recovering
                             THEN Recovering ELSE Follower, 
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
                  /\ pendingReply = [i \in Server |-> {}]
InitCandidateVars == /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ endOffset  = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log           = [i \in Server |-> << >>]
               /\ highWatermark = [i \in Server |-> 0]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ recoveryCtr = 0
               /\ acked = [v \in Value |-> Nil]
InitRecoveryVars ==
    /\ recoveryOffset    = [i \in Server |-> Nil]
    
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
    /\ ClearPendingReplies(i)
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
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentEpoch' = [currentEpoch EXCEPT ![i] = currentEpoch[i] + 1]
    /\ leader'       = [leader EXCEPT ![i] = Nil]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr'  = electionCtr + 1
    /\ LET msgs == {[mtype          |-> RequestVoteRequest,
                     mepoch         |-> currentEpoch[i] + 1,
                     mlastLogEpoch  |-> LastEpoch(log[i]),
                     mlastLogOffset |-> Len(log[i]),
                     msource        |-> i,
                     mdest          |-> j] : j \in Server \ {i}}
       IN /\ SendMultipleOnce(msgs)
          /\ SetPendingReplies(i, msgs)
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
               state0   == IF state[i] # Recovering /\ m.mepoch > currentEpoch[i]
                           THEN TransitionToUnattached(m.mepoch)
                           ELSE NoTransition(i)
               logOk == CompareEntries(m.mlastLogOffset,
                                       m.mlastLogEpoch,
                                       Len(log[i]),
                                       LastEpoch(log[i])) >= 0
               grant == /\ \/ state0.state = Unattached
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
                          THEN ClearPendingReplies(i)
                          ELSE UNCHANGED pendingReply
                       /\ Reply([mtype         |-> RequestVoteResponse,
                                 mepoch        |-> finalState.epoch,
                                 mleader       |-> finalState.leader,
                                 mvoteGranted  |-> grant,
                                 merror        |-> Nil,
                                 mcorrelation  |-> m,
                                 msource       |-> i,
                                 mdest         |-> j], m)
                  ELSE /\ Reply([mtype         |-> RequestVoteResponse,
                                 mepoch        |-> currentEpoch[i],
                                 mleader       |-> leader[i],
                                 mvoteGranted  |-> FALSE,
                                 merror        |-> error,
                                 mcorrelation  |-> m,
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
              \* cannot safely execute MaybeHandleCommonResponse here due to
              \* triggering inconsistent leader error
              /\ ExpectingReply(i, m)
              /\ state[i] # Recovering
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
              /\ UNCHANGED <<votedFor, pendingReply, recoveryVars, leaderVars, logVars, 
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
    /\ ClearPendingReplies(i)
    /\ SendMultipleOnce(
          {[mtype    |-> BeginQuorumRequest,
            mepoch   |-> currentEpoch[i],
            msource  |-> i,
            mdest    |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<currentEpoch, votedFor, pendingReply, recoveryVars,
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
        /\ state[m.mdest] # Recovering \* ignore if recovering
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
                   /\ pendingReply' = [pendingReply EXCEPT ![i] = {}]
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
                   /\ UNCHANGED <<state, leader, currentEpoch, pendingReply>>
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
    /\ state[i] \in {Follower, Recovering}
    /\ leader[i] = j
    /\ NoPendingReplies(i)
    /\ LET lastLogOffset == Len(log[i])
           lastLogEpoch == IF lastLogOffset > 0 
                           THEN log[i][lastLogOffset].epoch
                           ELSE 0
           fetchMsg     == [mtype             |-> FetchRequest,
                            mepoch            |-> currentEpoch[i],
                            mfetchOffset      |-> lastLogOffset,
                            mlastFetchedEpoch |-> lastLogEpoch,
                            mobserver         |-> state[i] = Recovering,
                            msource           |-> i,
                            mdest             |-> j]
       IN /\ AddPendingReply(i, fetchMsg)
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
               /\ Reply([mtype        |-> FetchResponse,
                         mresult      |-> NotOk,
                         merror       |-> error,
                         mleader      |-> leader[i],
                         mepoch       |-> currentEpoch[i],
                         mhwm         |-> highWatermark[i],
                         mcorrelation |-> m,
                         msource      |-> i,
                         mdest        |-> j], m)
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
                         mcorrelation        |-> m,
                         msource             |-> i,
                         mdest               |-> j], m)
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
                     newHwm == IF m.mobserver = FALSE
                               THEN NewHighwaterMark(i, newEndOffset)
                               ELSE highWatermark[i]
                 IN
                    /\ IF m.mobserver = FALSE
                       THEN /\ endOffset' = [endOffset EXCEPT ![i] = newEndOffset]
                            /\ highWatermark' = [highWatermark EXCEPT ![i] = newHwm]
                            /\ acked' = [v \in Value |-> 
                                            IF acked[v] = FALSE
                                            THEN v \in { log[i][ind].value : ind \in highWatermark[i]+1..newHwm }
                                            ELSE acked[v]]
                       ELSE UNCHANGED <<endOffset, highWatermark, acked>>
                    /\ Reply([mtype        |-> FetchResponse,
                              mepoch       |-> currentEpoch[i],
                              mleader      |-> leader[i],
                              mresult      |-> Ok,
                              merror       |-> Nil,
                              mentries     |-> entries,
                              mhwm         |-> Min({newHwm, offset}),
                              mcorrelation |-> m,
                              msource      |-> i,
                              mdest        |-> j], m)
                    /\ UNCHANGED <<candidateVars, currentEpoch, log, state, votedFor,
                                   pendingReply, leader, recoveryVars, electionCtr, 
                                   restartCtr, recoveryCtr>>
       
\* ACTION: HandleSuccessFetchResponse
\* Follower i receives a valid Fetch response from server j
\* and appends any entries to its log and updates its
\* high watermark.
MayBeSwitchOutOfRecovery(i, m) ==
    IF /\ state[i] = Recovering
       /\ recoveryOffset[i] <= Len(log[i]) + Len(m.mentries)
    THEN /\ state'          = [state EXCEPT ![i] = Follower]
         /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = Nil]
    ELSE UNCHANGED <<state, recoveryVars>>

HandleSuccessFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN /\ state[i] \in {Follower, Recovering}
              /\ newState.handled = FALSE
              /\ ExpectingReply(i, m)
              /\ m.mresult = Ok
              /\ highWatermark'  = [highWatermark  EXCEPT ![i] = m.mhwm]
              /\ IF Len(m.mentries) > 0
                 THEN log' = [log EXCEPT ![i] = Append(@, m.mentries[1])]
                 ELSE UNCHANGED log      
              /\ pendingReply' = [pendingReply EXCEPT ![i] = @ \ {m}]
              /\ MayBeSwitchOutOfRecovery(i, m)
              /\ Discard(m)
              /\ UNCHANGED <<currentEpoch, leader, votedFor, 
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
              /\ state[i] \in {Follower, Recovering}
              /\ newState.handled = FALSE
              /\ ExpectingReply(i, m)
              /\ m.mresult = Diverging
              /\ log' = [log EXCEPT ![i] = TruncateLog(i, m)]
              /\ pendingReply' = [pendingReply EXCEPT ![i] = @ \ {m}] 
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
              /\ state[i] \in {Follower, Recovering}
              /\ newState.handled = TRUE
              /\ ExpectingReply(i, m)
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
              /\ pendingReply' = [pendingReply EXCEPT ![i] = @ \ {m}]
              /\ IF state[i] = Recovering
                 THEN recoveryOffset = [recoveryOffset EXCEPT ![i] = newState.recoveryOffset]
                 ELSE UNCHANGED recoveryOffset
              /\ Discard(m)
        /\ UNCHANGED <<votedFor, candidateVars, leaderVars, 
                       logVars, auxVars>>                       

\* ACTION: Restart In-Recovery
RestartInRecovery(i, j) ==
    /\ recoveryCtr < MaxRecoveries
    /\ i # j
    /\ state'             = [state EXCEPT ![i] = Recovering]
    /\ currentEpoch'      = [currentEpoch EXCEPT ![i] = 0]
    /\ leader'            = [leader EXCEPT ![i] = Nil]
    /\ votedFor'          = [leader EXCEPT ![i] = Nil]
    /\ highWatermark'     = [highWatermark EXCEPT ![i] = 0]
    /\ log'               = [log EXCEPT ![i] = <<>>]
    /\ votesGranted'      = [votesGranted EXCEPT ![i] = {}]
    /\ endOffset'         = [endOffset EXCEPT ![i] = [ii \in Server |-> 0]]
    /\ recoveryOffset'    = [recoveryOffset EXCEPT ![i] = Nil]
    /\ recoveryCtr'       = recoveryCtr + 1
    /\ LET fetchMsg     == [mtype             |-> DFetchRequest,
                            mepoch            |-> 0,
                            msource           |-> i]
       IN /\ SetPendingReplies(i, {fetchMsg})
          /\ Send(fetchMsg)
    /\ UNCHANGED <<acked, electionCtr, restartCtr>>

HandleDiscoveryFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, DFetchRequest, AnyEpoch)
        /\ \E i \in Server :
            /\ i # m.msource
            /\ leader[i] # Nil
            /\ Reply([mtype        |-> DFetchResponse,
                      mepoch       |-> currentEpoch[i],
                      mleader      |-> leader[i],
                      mcorrelation |-> m,
                      mdest        |-> m.msource,
                      msource      |-> i], m)
        /\ UNCHANGED << serverVars, candidateVars, leaderVars, 
                        logVars, recoveryVars, auxVars >>

HandleDiscoveryFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, DFetchResponse, AnyEpoch)
        /\ LET i == m.mdest
               j == m.msource
           IN /\ state[i] = Recovering
              /\ ExpectingReply(i, m)
              /\ leader' = [leader EXCEPT ![i] = m.mleader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = m.mepoch]
              /\ LET msg ==   [mtype     |-> OffsetForLeaderEpochRequest,
                               mepoch    |-> m.mepoch,
                               mleader   |-> m.mleader,
                               msource   |-> i,
                               mdest     |-> j]
                 IN /\ Send(msg)
                    /\ pendingReply' = [pendingReply EXCEPT ![i] = @ \union {msg}]  
        /\ UNCHANGED << state, votedFor, candidateVars, leaderVars,
                        logVars, recoveryVars, auxVars >>  
              
(*
- If the current leader is not known, send Fetch with 
replicaId=-1  to a random voter in order to find the current leader.
- If the leader is known, then we will send Fetch requests 
with replicaId=-1 to the current leader. This lets the node 
begin catching up and also ensures that we get timely 
notification of leader changes.
- If the leader is known, but no recoveryOffset has been set, 
then send OffsetForLeaderEpoch to the leader with the current epoch.
- If the recoveryOffset is known, then begin sending Fetch 
requests to the current leader in order to catch up. Also 
send OffsetForLeaderEpoch to remaining non-leader voters to 
determine if they have caught up to the recoveryOffset.
*)

\*\* ACTION: SendOffsetForLeaderEpochRequest
\*\* Occurs when the first request was rejected but contains the 
\*\* leader id in the response.   
\*SendOffsetForLeaderEpochRequest(i, j) ==
\*    /\ state[i] = Recovering
\*    /\ leader[i] = j
\*    /\ recoveryOffset = Nil
\*    /\ pendingReply[i] = Nil
\*    /\ LET msg == [mtype     |-> OffsetForLeaderEpochRequest,
\*                   mepoch    |-> currentEpoch[i],
\*                   mleader   |-> leader[i],
\*                   msource   |-> i,
\*                   mdest     |-> j]
\*       IN /\ Send(msg)
\*          /\ pendingReply' = [pendingReply EXCEPT ![i] = msg]                 
\*    /\ UNCHANGED << state, leader, votedFor, candidateVars, leaderVars,
\*                    logVars, recoveryVars, auxVars >>  
    

\* ACTION: HandleOffsetForLeaderEpochRequest
HandleOffsetForLeaderEpochRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, OffsetForLeaderEpochRequest, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               endOffsetAndEpoch == EndOffsetForEpoch(i, m.mepoch)
               error             == IF state[i] = Recovering \/ m.mepoch > currentEpoch[i]
                                    THEN UnknownLeader
                                    ELSE Nil
           IN 
              /\ \* not part of the protocol, just a trick to avoid endless retries and state space explosion
                 \* this server, who is not the leader (as per the message) will on;y reploy
                 \* if it reaches the target offset. Avoids the need for the recovering server
                 \* to repeatedly send the same OffsetForLeaderEpochRequest to the non-leaders over and over.
                 IF state[i] # Recovering /\ i # m.mleader
                 THEN endOffsetAndEpoch.offset >= m.mtargetOffset
                 ELSE TRUE
              /\ Reply([mtype        |-> OffsetForLeaderEpochResponse,
                        mepoch       |-> currentEpoch[i],
                        mleader      |-> leader[i],
                        mendOffset   |-> endOffsetAndEpoch.offset,
                        mcorrelation |-> m,
                        merrors      |-> error,
                        msource      |-> i,
                        mdest        |-> j], m)
        /\ UNCHANGED <<serverVars, candidateVars, leaderVars, 
                       logVars, recoveryVars, auxVars>>

\* ACTION: HandleMetadataResponse

HandleOffsetForLeaderEpochResponseFromLeader ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, OffsetForLeaderEpochResponse, AnyEpoch)
        /\ LET i                == m.mdest
               j                == m.msource
           IN /\ state[i] = Recovering
              /\ ExpectingReply(i, m)
              /\ leader[i] = m.msource
              /\ IF m.merrors = Nil
                 THEN
                      /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = m.mendOffset]
                      /\ LET msgs == {[mtype         |-> OffsetForLeaderEpochRequest,
                                       mepoch        |-> m.mepoch,
                                       mleader       |-> m.mleader,
                                       mtargetOffset |-> m.mendOffset, \* just for model checking, not in protocol
                                       msource       |-> i,
                                       mdest         |-> peer] : peer \in Server \ {i, m.mleader}}
                         IN /\ DiscardAndSendMultiple(m, msgs)
                            /\ SetPendingReplies(i, msgs)
                            /\ UNCHANGED << leader >>
                 ELSE 
                      /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = Nil]
                      /\ leader' = [leader EXCEPT ![i] = m.mleader] 
                      /\ LET msg == IF m.mleader = Nil
                                    THEN [mtype   |-> DFetchRequest,
                                          mepoch  |-> 0,
                                          msource |-> i]
                                    ELSE [mtype   |-> OffsetForLeaderEpochRequest,
                                          mepoch  |-> m.mepoch,
                                          mleader |-> m.mleader,
                                          msource |-> i,
                                          mdest   |-> m.mleader]
                         IN /\ SetPendingReplies(i, {msg})
                            /\ DiscardAndSend(m, msg)
              /\ UNCHANGED <<currentEpoch, state, votedFor, leaderVars, candidateVars, logVars, auxVars>>
              
HandleOffsetForLeaderEpochResponseFromNonLeader ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, OffsetForLeaderEpochResponse, AnyEpoch)
        /\ LET i                == m.mdest
               j                == m.msource
           IN /\ state[i] = Recovering
              /\ ExpectingReply(i, m)
              /\ leader[i] # m.msource
              /\ IF m.merrors = Nil
                 THEN
                      /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = m.mendOffset]
                      /\ LET msgs == {[mtype         |-> OffsetForLeaderEpochRequest,
                                       mepoch        |-> m.mepoch,
                                       mleader       |-> m.mleader,
                                       mtargetOffset |-> m.mendOffset, \* just for model checking, not in protocol
                                       msource       |-> i,
                                       mdest         |-> peer] : peer \in Server \ {i, m.mleader}}
                         IN /\ DiscardAndSendMultiple(m, msgs)
                            /\ SetPendingReplies(i, msgs)
                            /\ UNCHANGED << leader >>
                 ELSE 
                      /\ recoveryOffset' = [recoveryOffset EXCEPT ![i] = Nil]
                      /\ leader' = [leader EXCEPT ![i] = m.mleader] 
                      /\ LET msg == IF m.mleader = Nil
                                    THEN [mtype   |-> DFetchRequest,
                                          mepoch  |-> 0,
                                          msource |-> i]
                                    ELSE [mtype   |-> OffsetForLeaderEpochRequest,
                                          mepoch  |-> m.mepoch,
                                          mleader |-> m.mleader,
                                          msource |-> i,
                                          mdest   |-> m.mleader]
                         IN /\ SetPendingReplies(i, {msg})
                            /\ DiscardAndSend(m, msg)
              /\ UNCHANGED <<currentEpoch, state, votedFor, leaderVars, candidateVars, logVars, auxVars>>

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
        \/ \E i, j \in Server : RestartInRecovery(i, j)
\*        \/ \E i, j \in Server : SendOffsetForLeaderEpochRequest(i, j)
        \/ HandleDiscoveryFetchRequest
        \/ HandleDiscoveryFetchResponse
        \/ HandleOffsetForLeaderEpochRequest
        \/ HandleOffsetForLeaderEpochResponse
        
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
    TRUE
\*    \A i \in Server : 
\*        inRecovery[i] = TRUE
\*        ~>
\*        \/ /\ electionCtr = MaxElections
\*           /\ ~\E j \in Server : state[j] = Leader
\*        \/ inRecovery[i] = FALSE

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
