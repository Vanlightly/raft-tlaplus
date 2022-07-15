--------------------------------- MODULE KRaftWithReconfig ---------------------------------
(*NOTES
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

-----------------------------------------------
Kafka KRaft TLA+ specification
-----------------------------------------------

This is a specification that has been reverse engineered from the Kafka KRaft implementation.
It makes some effort to reuse some of the functions of the implementation in order to
ensure it is accurately modelling the behaviour. 

KRaft is a pull variant of Raft, which is push based. 

Note the following messages are not modelled:
- BeginQuorumResponse as this is only required by the implementation for liveness.
  If the leader doesn't receive a response it resends the BeginQuorumRequest. However,
  in the specification, message retries are implicit and so explicit retries
  are not required.
- EndQuorumRequest/Response as this exists as an optimization for a leader
  that gracefully shutsdown. It is not needed for correctness and so is not
  included.
- FetchSnapshotRequest/Response. This is a straight forward optimization
  and so has not been explicitly modelled. 

The KRaft implementation uses a cache object as an index for epochs and their start offsets
which is required for leaders to be able to give followers the information they need
to truncate their logs. This specification does not model this cache but simply looks up this
information from the log itself.

State transitions (taken from https://github.com/apache/kafka/blob/trunk/raft/src/main/java/org/apache/kafka/raft/QuorumState.java):
* Unattached|Resigned transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Voted: After granting a vote to a candidate
 *    Candidate: After expiration of the election timeout
 *    Follower: After discovering a leader with an equal or larger epoch
 *
 * Voted transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the election timeout
 *
 * Candidate transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the election timeout
 *    Leader: After receiving a majority of votes
 *
 * Leader transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Resigned: When shutting down gracefully
 *
 * Follower transitions to:
 *    Unattached: After learning of a new election with a higher epoch
 *    Candidate: After expiration of the fetch timeout
 *    Follower: After discovering a leader with a larger epoch

--------------------------------
Reconfiguration ----------------

KRaft implements the one-at-a-time add or remove member reconfiguration
algorithm instead of the Joint Consensus algorithm. This restricts
reconfiguration operations to one-at-a-time.

Please review the Raft thesis (not the paper) for a detailed description of
the nuances of this reconfiguration protocol: https://web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf
Also note this bug in this thesis: https://groups.google.com/g/raft-dev/c/t4xj6dJTP6E?spm=a2c65.11461447.0.0.72ff5798NIE11G
This bug is fixed by the leader only adding reconfiguration commands
once it has committed an entry in the current epoch.

Reconfigurations are performed by adding commands to the log. As soon
as a server sees a reconfiguration command they immediately assume
the new configuration. A reconfiguration is complete once the command gets
committed. This means that a server can assume a new configuration but later
revert back to the prior configuration in the case of truncating their
log after a leader election.

Adding a member
-----------------

In order to avoid liveness issues, before an AddServerCommand is added to the log, the
joining member must first catch up to the leader. The Raft thesis recommends
that this be addressed by making new members non-voting until they catch-up. However,
this specification reverses the order by making a joinee catch-up first and
then adding the reconfig command once it has done so. This makes for a simpler
design.

In order to add a server, the server itself must request to join the cluster.
It does so with the following sequence:

Joinee server                               Leader
  |                                           |
  ----PrepareJoinRequest{identity}----------->
  <---PrepareJoinResponse{snapshot, config}---
(apply snapshot - now caught up)
  ----JoinRequest(identity, config id)------->
                                       (append AddServerCommand to log)
  <---JoinResponse{ok}------------------------

The PrepareJoinResponse contains a snapshot and the current configuraton.
The implementation would instead pass a snapshot id that the joinee would then request
but that is ommitted from this specification.

The JoinRequest includes the configuration id that was received by the joinee
in the PrepareJoinResponse. 

To be valid a JoinRequest the following conditions are required:
- request received by a leader
- the joining node cannot already be a member
- the config id in the request must match the current config id of the leader
- the leader have no in-progress reconfiguration
- the leader must have committed an offset in the current epoch.

The JoinResponse is sent as soon as the AddServerCommand
has been appended to the leader's log.

Further protecting liveness
Between receiving a snapshot and sending the JoinRequest there
may be a large number of new entries. This can still present
a liveness challenge if this server would be required in order to make
progress. So to avoid that the implementation can do the following:
- Joinee includes its end offset in the JoinRequest
- The leader can reject the request if the lag is too large.
- After a snapshot, the joinee can continue to keep pace
  with the leader by fetching as an observer.
- The joinee can send a JoinRequest once it has caught up to
  the leader and avoid being rejected for being too far behind.

Removing a member
--------------------
Requester                                   Leader
   |                                          |
   ----LeaveRequest--------------------------->
                                          (add RemoveServerCommand to log)
   <---LeaveResponse---------------------------                                       


The LeaveResponse is sent as soon as the command has been
added to the leader's log.

To be valid a LeaveRequest the following conditions are required:
- request received by a leader
- the leaving node must be a member of the current configuration
- the leader have no in-progress reconfiguration
- the leader must have committed an offset in the current epoch.

A leader may have appended a RemoveServerCommand to its log
where it is the server being removed. The leader still
switches to this new configuration where it is no longer
a member but continues to be leader in order to commit the
command. While it is leader but not a member it does not 
include itself in the quorum for advancing the high watermark.
As soon as the command is committed the server resigns 
from leadership.

Additional nuance
--------------------------------
- A server can only start an election if it believes itself
  to be a member.
- A server can still do the following, even if it believes it
  isn't a member of the cluster: 
  - participate in elections, this is because it may have 
    switched to a new configuration where it isn't a member
    but that configuration doesn't ultimately get committed.
  - Accept a BeginQuorumRequest
- Because servers immediately switch to new configurations,
  they must always be prepared to revert back to the prior
  configuration if the command of the current configuration
  gets removed during a log truncation.
- How to track progress of a reconfiguration is not included in 
  this specification but should be simple enough by querying the leader
  about the state of its current configuration.
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* The initial cluster size (the size can change over time due to reconfigurations)
CONSTANTS InitClusterSize, MinClusterSize, MaxClusterSize

\* The set of server IDs
CONSTANTS Hosts

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, Unattached, Voted, NotMember, Dead

\* Commands
CONSTANTS AppendCommand,        \* contains a client value
          InitClusterCommand,   \* contains the initial configuration
          AddServerCommand,     \* reconfiguration command to add a server
          RemoveServerCommand   \* reconfiguration command to remove a server

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          BeginQuorumRequest, BeginQuorumResponse,
          EndQuorumRequest,
          FetchRequest, FetchResponse,
          PrepareJoinRequest, PrepareJoinResponse,
          JoinRequest, LeaveRequest

\* Fetch response codes          
CONSTANTS Ok, NotOk, Diverging, UnknownMember

\* Errors
CONSTANTS FencedLeaderEpoch, NotLeader, UnknownLeader

\* Special state that indicates a server has entered an illegal state
CONSTANTS IllegalState       

\* Used for filtering messages under different circumstances
CONSTANTS AnyEpoch, EqualEpoch

\* Limiting state space by limiting the number of elections and restarts           
CONSTANTS MaxElections, MaxRestarts,
          MaxAddReconfigs, MaxRemoveReconfigs
----
\* Global variables

VARIABLE servers

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
VARIABLE electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr
\* A counter used to generate a unique disk id. An implementation would
\* use a random UUID but this spec uses a global counter for simplicity.
VARIABLE diskIdGen
auxVars == <<acked, electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr, diskIdGen>>
----
\* Per server variables (functions with domain Server).

\* The current configuration
VARIABLE config
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
serverVars == <<config, currentEpoch, state, votedFor, leader, pendingFetch>>

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

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<servers, messages, serverVars, candidateVars, leaderVars, logVars,
          auxVars>>
view == <<servers, messages, serverVars, candidateVars, leaderVars, logVars, acked >>
symmHosts == Permutations(Hosts)
symmValues == Permutations(Value)
----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(ensemble) == {i \in SUBSET(ensemble) : Cardinality(i) * 2 > Cardinality(ensemble)}

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
    /\ state[m.mdest] # Dead
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
    IF leaderId = i
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

\* the offset points to a reconfiguration command in the log
IsConfigCommand(serverLog, offset) ==
    serverLog[offset].command \in {InitClusterCommand,
                                   AddServerCommand, 
                                   RemoveServerCommand}

\* A leader only allows one uncommitted reconfiguration command
\* at a time.
HasPendingConfigCommand(i) ==
    config[i].committed = FALSE

\* Returns the most recent config command entry
MostRecentReconfigEntry(serverLog) ==
    LET offset == CHOOSE index \in DOMAIN serverLog : 
                    /\ IsConfigCommand(serverLog, index)
                    /\ ~\E index2 \in DOMAIN serverLog : 
                        /\ IsConfigCommand(serverLog, index2)
                        /\ index2 > index
    IN [offset |-> offset, entry |-> serverLog[offset]]

NoConfig == 
    [id        |-> 0,
     members   |-> {},
     committed |-> FALSE]
              
ConfigFor(offset, reconfigEntry, ci) ==
    [id        |-> reconfigEntry.value.id,
     members   |-> reconfigEntry.value.members,
     committed |-> ci >= offset]
     
LeaderHasCommittedOffsetsInCurrentEpoch(i) ==
    \E offset \in DOMAIN log[i] :
        /\ log[i][offset].epoch = currentEpoch[i]
        /\ highWatermark[i] >= offset     

SetStateOfNewAndDeadIdentity(newIdentity, deadIdentity) ==
    /\ servers'         = servers \union {newIdentity}
    /\ config'          = config @@ (newIdentity :> NoConfig)
    /\ state'           = IF deadIdentity # Nil
                          THEN [state EXCEPT ![deadIdentity] = Dead] @@ (newIdentity :> NotMember)
                          ELSE state @@ (newIdentity :> NotMember)
    /\ currentEpoch'    = currentEpoch @@ (newIdentity :> 0)
    /\ leader'          = leader @@ (newIdentity :> Nil)
    /\ votedFor'        = votedFor @@ (newIdentity :> Nil)
    /\ pendingFetch'    = pendingFetch @@ (newIdentity :> Nil) 
    /\ votesGranted'    = votesGranted @@ (newIdentity :> {})
    /\ endOffset'       = endOffset @@ (newIdentity :> <<>>)
    /\ log'             = log @@ (newIdentity :> <<>>)
    /\ highWatermark'   = highWatermark @@ (newIdentity :> 0) 

SetStateOfNewIdentity(identity) ==
    SetStateOfNewAndDeadIdentity(identity, Nil)

----
\* Define initial values for all variables

InitServerVars(initLeader, members) == 
    /\ servers      = members
    /\ currentEpoch = [i \in members |-> 1]
    /\ state        = [i \in members |-> IF i = initLeader 
                                         THEN Leader
                                         ELSE Follower]
    /\ leader       = [i \in members |-> initLeader]
    /\ votedFor     = [i \in members |-> Nil]
    /\ pendingFetch = [i \in members |-> Nil]
    /\ config       = [i \in members |-> [id        |-> 1,
                                          members   |-> members,
                                          committed |-> TRUE]]
InitCandidateVars(members) == 
    votesGranted   = [i \in members |-> {}]

InitLeaderVars(members) == 
    endOffset  = [i \in members |-> [j \in members |-> 1]]

InitLogVars(members, firstEntry) == 
    /\ log           = [i \in members |-> << firstEntry >>]
    /\ highWatermark = [i \in members |-> 1]

InitAuxVars == 
    /\ electionCtr = 0
    /\ restartCtr = 0
    /\ addReconfigCtr = 0
    /\ removeReconfigCtr = 0
    /\ diskIdGen = 0
    /\ acked = [v \in Value |-> Nil]

\* note that the diskId is the same for all servers of the initial cluster
\* which wouldn't be the case in reality but is simpler here and does not
\* violate the global identity uniqueness.
Init == LET hosts      == CHOOSE s \in SUBSET Hosts :
                              Cardinality(s) = InitClusterSize
            members    == {[host |-> i, diskId |-> 0] : i \in hosts}                             
            initLeader == CHOOSE i \in members : TRUE
            firstEntry == [command |-> InitClusterCommand,
                           epoch   |-> 1,
                           value   |-> [id      |-> 1,
                                        members |-> members]]
        IN
            /\ messages = [m \in {} |-> 0]
            /\ InitServerVars(initLeader, members)
            /\ InitCandidateVars(members)
            /\ InitLeaderVars(members)
            /\ InitLogVars(members, firstEntry)
            /\ InitAuxVars

----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentEpoch, leader and log.
RestartWithState ==
    \E i \in servers :
        /\ restartCtr < MaxRestarts
        /\ state[i] # Dead
        /\ state'         = [state EXCEPT ![i] = Follower]
        /\ leader'        = [leader EXCEPT ![i] = Nil]
        /\ votesGranted'  = [votesGranted EXCEPT ![i] = {}]
        /\ endOffset'     = [endOffset EXCEPT ![i] = [j \in servers |-> 0]]
        /\ highWatermark' = [highWatermark EXCEPT ![i] = 0]
        /\ pendingFetch'  = [pendingFetch EXCEPT ![i] = Nil]
        /\ restartCtr'    = restartCtr + 1
        /\ UNCHANGED <<servers, messages, config, currentEpoch, 
                       votedFor, log, acked, electionCtr,
                       addReconfigCtr, removeReconfigCtr, diskIdGen>>

\* ACTION: RestartWithoutState
\* A server that has state and is a member of the cluster
\* restarts with all state lost. Starting from blank state
\* causes the server to generate a new identity.
\* Either the original server is dead, or is remains as a
\* functioning zombie server.
RestartWithoutState ==
    \E i \in servers, leaveZombie \in BOOLEAN :
        /\ state[i] # Dead
        /\ \E j \in servers : i \in config[j].members
        /\ restartCtr < MaxRestarts
        /\ LET identity == [host |-> i.host, diskId |-> diskIdGen + 1]
           IN /\ IF leaveZombie
                 THEN SetStateOfNewAndDeadIdentity(identity, i)
                 ELSE SetStateOfNewIdentity(identity)
              /\ restartCtr'    = restartCtr + 1
              /\ diskIdGen'       = diskIdGen + 1
        /\ UNCHANGED <<messages, acked, electionCtr,
                       addReconfigCtr, removeReconfigCtr>>

\* ACTION: RequestVote -----------------------------------------------
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote ==
    \E i \in servers :
        /\ electionCtr < MaxElections 
        /\ state[i] \in {Follower, Candidate, Unattached}
        /\ i \in config[i].members
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
                 mdest          |-> j] : j \in config[i].members \ {i}})
        /\ UNCHANGED <<servers, config, acked, leaderVars, logVars, restartCtr,
                       addReconfigCtr, diskIdGen, removeReconfigCtr>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j.
\* Server i will vote for j if:
\* 1) epoch of j >= epoch of i
\* 2) last entry of i is <= to the last entry of j
\* 3) i has not already voted for a different server
HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ \E i \in servers :
            /\ ReceivableMessage(m, RequestVoteRequest, AnyEpoch)
            /\ i.host = m.mdest.host
            /\ LET j     == m.msource
                   error    == IF m.mepoch < currentEpoch[i]
                               THEN FencedLeaderEpoch
                               ELSE Nil
                   state0   == IF m.mepoch > currentEpoch[i]
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
                           /\ UNCHANGED << currentEpoch, state, leader, votedFor, pendingFetch>>
                   /\ UNCHANGED <<servers, config, candidateVars, leaderVars, logVars, auxVars>>

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
              /\ UNCHANGED <<servers, config, votedFor, pendingFetch, leaderVars, logVars, 
                             auxVars>>               

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader and notifies all peers of its
\* leadership via the BeginQuorumRequest.
BecomeLeader ==
    \E i \in servers : 
        /\ state[i] = Candidate
        /\ votesGranted[i] \in Quorum(config[i].members)
        /\ state'  = [state EXCEPT ![i] = Leader]
        /\ leader' = [leader EXCEPT ![i] = i]
        /\ endOffset' = [endOffset EXCEPT ![i] = [j \in config[i].members |-> 0]]
        /\ SendMultipleOnce(
              {[mtype    |-> BeginQuorumRequest,
                mepoch   |-> currentEpoch[i],
                msource  |-> i,
                mdest    |-> j] : j \in config[i].members \ {i}})
        /\ UNCHANGED <<servers, config, currentEpoch, votedFor, pendingFetch,
                       candidateVars, auxVars, logVars>>

\* ACTION: HandleBeginQuorumRequest -------------------------------------------
\* A server receives a BeginQuorumRequest and transitions to a follower
\* unless the message is stale.
HandleBeginQuorumRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, BeginQuorumRequest, AnyEpoch)
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
        /\ UNCHANGED <<servers, config, votedFor, log, candidateVars,
                       leaderVars, highWatermark, auxVars>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest ==
    \E i \in servers, v \in Value : 
        /\ state[i] = Leader
        /\ acked[v] = Nil \* prevent submitting the same value repeatedly
        /\ LET entry == [command |-> AppendCommand,
                         epoch   |-> currentEpoch[i],
                         value   |-> v]
               newLog == Append(log[i], entry)
           IN  /\ log' = [log EXCEPT ![i] = newLog]
               /\ acked' = [acked EXCEPT ![v] = FALSE]
        /\ UNCHANGED <<servers, messages, serverVars, candidateVars,
                       leaderVars, highWatermark, electionCtr, restartCtr,
                       addReconfigCtr, removeReconfigCtr, diskIdGen>>
                       
\* ACTION: SendFetchRequest ----------------------------------------
\* Follower i sends leader j a FetchRequest.
SendFetchRequest ==
    \E i,j \in servers : 
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
                                msource           |-> i,
                                mdest             |-> j]
           IN /\ pendingFetch' = [pendingFetch EXCEPT ![i] = fetchMsg]
              /\ Send(fetchMsg)
        /\ UNCHANGED <<servers, config, currentEpoch, state, 
                       votedFor, leader, candidateVars, leaderVars, 
                       logVars, auxVars>>

\* ACTION: RejectFetchRequest -------------------
\* Server i rejects a FetchRequest due to either:
\* - i is not a leader
\* - the message epoch is lower than the server epoch
\* - the message epoch is higher than the server epoch
\* - the request is from a server not in the current configuration
RejectFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, AnyEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               error               == CASE state[i] # Leader -> NotLeader
                                        [] m.mepoch < currentEpoch[i] -> FencedLeaderEpoch
                                        [] m.mepoch > currentEpoch[i] -> UnknownLeader
                                        [] j \notin config[i].members -> UnknownMember
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
               /\ UNCHANGED <<servers, candidateVars, leaderVars, serverVars, 
                              logVars, auxVars>>

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
               /\ j \in config[i].members
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
               /\ UNCHANGED <<servers, candidateVars, leaderVars, serverVars, 
                              logVars, auxVars>>

\* ACTION: AcceptFetchRequest ------------------
\* Leader i receives a FetchRequest from a valid position
\* and responds with an entry if there is one or an empty
\* response if not.
\* The leader updates the end offset of the fetching peer
\* and advances the high watermark if it can.
\* It can only advance the high watermark to an entry of the
\* current epoch.
IsRemovedFromCluster(i, newHwm) ==
    \E offset \in DOMAIN log[i] :
        /\ offset > highWatermark[i]
        /\ offset <= newHwm
        /\ log[i][offset].command = RemoveServerCommand
        /\ i \notin log[i][offset].value.members

NewHighwaterMark(i, newEndOffset) ==
    LET \* The set of servers that agree up through the given offset.
        \* If the leader is not in the current member set due
        \* to an in-progress reconfiguration then it does not 
        \* include itself in the quorum
        Agree(offset, members) == 
            IF i \in members
            THEN {i} \cup {k \in config[i].members : newEndOffset[k] >= offset }
            ELSE {k \in config[i].members : newEndOffset[k] >= offset }
        \* The maximum offsets for which a quorum agrees
        agreeOffsets  == {offset \in 1..Len(log[i]) : 
                            Agree(offset, config[i].members) \in Quorum(config[i].members)}
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
              /\ j \in config[i].members
              /\ valid
              /\ LET newEndOffset  == [endOffset[i] EXCEPT ![j] = m.mfetchOffset]
                     newHwm        == NewHighwaterMark(i, newEndOffset)
                     leavesCluster == IsRemovedFromCluster(i, newHwm)
                 IN
                    /\ IF newHwm > highWatermark[i]
                       THEN /\ acked' = [v \in Value |-> 
                                            IF acked[v] = FALSE
                                            THEN v \in { log[i][ind].value : ind \in highWatermark[i]+1..newHwm }
                                            ELSE acked[v]]
                            /\ IF leavesCluster
                               THEN /\ state'          = [state EXCEPT ![i] = NotMember]
                                    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                                    /\ endOffset'      = [endOffset EXCEPT ![i] = <<>>]
                                    /\ highWatermark'  = [highWatermark EXCEPT ![i] = 0]
                               ELSE /\ endOffset' = [endOffset EXCEPT ![i] = newEndOffset]
                                    /\ highWatermark' = [highWatermark EXCEPT ![i] = newHwm]
                                    /\ UNCHANGED <<state, votesGranted>>
                       ELSE UNCHANGED <<state, votesGranted, highWatermark, acked, endOffset>>
                    /\ Reply([mtype       |-> FetchResponse,
                              mepoch      |-> currentEpoch[i],
                                              \* TODO: review this, should implement resignation in this spec?
                              mleader     |-> IF leavesCluster THEN Nil ELSE leader[i],
                              mresult     |-> Ok,
                              merror      |-> Nil,
                              mentries    |-> entries,
                              mhwm        |-> Min({newHwm, offset}),
                              msource     |-> i,
                              mdest       |-> j,
                              correlation |-> m], m)
                    /\ UNCHANGED <<servers, candidateVars, config, currentEpoch, log, 
                                   state, votedFor, pendingFetch, leader, electionCtr, 
                                   restartCtr, addReconfigCtr, removeReconfigCtr, diskIdGen>>
       
\* ACTION: HandleSuccessFetchResponse
\* Follower i receives a valid Fetch response from server j
\* and appends any entries to its log and updates its
\* high watermark.
HandleSuccessFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i           == m.mdest
               j           == m.msource
               newState    == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
               newLog      == IF Len(m.mentries) > 0
                              THEN [log EXCEPT ![i] = Append(@, m.mentries[1])]
                              ELSE log 
               configEntry == MostRecentReconfigEntry(newLog[i])
               currConfig  == ConfigFor(configEntry.offset,
                                        configEntry.entry,
                                        m.mhwm)
           IN /\ j \in config[i].members
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Ok
              \* could have a new config
              /\ config' = [config EXCEPT ![i] = currConfig]
              /\ state' = [state EXCEPT ![i] = IF i \in currConfig.members
                                                     THEN Follower   \* still a member
                                                     ELSE NotMember] \* has been removed
              \* update log and hwm
              /\ highWatermark'  = [highWatermark  EXCEPT ![i] = m.mhwm]
              /\ log' = newLog
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Discard(m)
              /\ UNCHANGED <<servers, currentEpoch, leader, votedFor, 
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
               newLog      == [log EXCEPT ![i] = TruncateLog(i, m)] 
               configEntry == MostRecentReconfigEntry(newLog[i])
               currConfig  == ConfigFor(configEntry.offset,
                                        configEntry.entry,
                                        m.mhwm)
           IN 
              /\ j \in config[i].members
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Diverging
              \* could have truncated the current config
              /\ config' = [config EXCEPT ![i] = currConfig]
              /\ state' = [state EXCEPT ![i] = IF i \in currConfig.members
                                                     THEN Follower   \* still a member
                                                     ELSE NotMember] \* has been removed
              \* update log
              /\ log' = newLog
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil] 
              /\ Discard(m)
        /\ UNCHANGED <<servers, currentEpoch, leader, 
                       votedFor, candidateVars, leaderVars, 
                       highWatermark, auxVars>>
                       
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
              /\ j \in config[i].members
              /\ newState.handled = TRUE
              /\ pendingFetch[i] = m.correlation
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Discard(m)
        /\ UNCHANGED <<servers, config, votedFor, candidateVars, leaderVars, 
                       logVars, auxVars>>                       

\* ----------------------------------------------
\* RECONFIGURATION ------------------------------

\* ACTION: StartNewServer ----------------------------
\* A server starts with a blank disk and generates
\* an composite identity based on host and a random id
\* called diskId.
\* It then sends a PrepareJoinRequest to a server that
\* it has been told is the leader.
\* Note that selection of the leader could be made more
\* complex, but this spec assumes the new start is given
\* the id of the current leader. Having the correct leader
\* is not required for safety.
StartNewServer ==
    /\ addReconfigCtr < MaxAddReconfigs
    /\ \E host \in Hosts, anyLeader \in servers :
        LET diskId    == diskIdGen + 1
            identity  == [host |-> host, diskId |-> diskId]
        IN /\ state[anyLeader] = Leader \* this is a shortcut, but a safe one.
           /\ SetStateOfNewIdentity(identity)
           /\ addReconfigCtr'  = addReconfigCtr + 1
           /\ diskIdGen'       = diskIdGen + 1
           /\ Send([mtype   |-> PrepareJoinRequest,
                    mdest   |-> anyLeader,
                    msource |-> identity])
           /\ UNCHANGED << acked, electionCtr, restartCtr, removeReconfigCtr >>

\* ACTION: AcceptPrepareJoinRequest ----------------------------------
\* The leader handles a valid PrepareJoinRequest by
\* sending a response with a snapshot and current configuration.
\* To be valid a PrepareJoinRequest the following conditions are required:
\* - request received by a leader
\* - the leader have no in-progress reconfiguration
\* - the leader must have committed an offset in the current epoch.
PrepareJoinCheck(i, m) ==
    CASE state[i] # Leader -> NotLeader
      [] HasPendingConfigCommand(i) -> "PendingReconfig"
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(i) -> "LeaderNotReady"
      [] OTHER -> Ok
           
AcceptPrepareJoinRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PrepareJoinRequest, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               check == PrepareJoinCheck(i, m)
           IN 
              /\ Cardinality(config[i].members) < MaxClusterSize
              /\ check = Ok
              /\ Reply([mtype     |-> PrepareJoinResponse,
                        mepoch    |-> currentEpoch[i],
                        mconfig   |-> config[i],
                        msnapshot |-> log[i],
                        mhwm      |-> highWatermark[i],
                        mmembers  |-> config[i].members,
                        msource   |-> i,
                        mdest     |-> j], m)
              /\ UNCHANGED <<servers, serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: HandlePrepareJoinResponse ----------------------------------
\* The joining server handles a successful PrepareJoinResponse
\* by writing the snapshot, config, epoch and hwm to disk.
\* It now sends the actual JoinRequest to the leader, including
\* the config id, to ensure that the join request is still valid.        
HandlePrepareJoinResponse ==
     \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PrepareJoinResponse, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
           IN /\ config'        = [config EXCEPT ![i] = m.mconfig]
              /\ currentEpoch'  = [currentEpoch EXCEPT ![i] = m.mepoch]
              /\ log'           = [log EXCEPT ![i]    = m.msnapshot]
              /\ highWatermark' = [highWatermark EXCEPT ![i] = m.mhwm]
              /\ Reply([mtype      |-> JoinRequest,
                        mconfigId  |-> m.mconfig.id,
                        mepoch     |-> m.mepoch,
                        maddMember |-> i,
                        mdest      |-> j,
                        msource    |-> i], m)
        /\ UNCHANGED <<servers, state, pendingFetch, leader, votedFor, candidateVars,
                       leaderVars, auxVars>>
              
\* ACTION: AcceptJoinRequest ----------------------------------
\* Leader i accepts a valid JoinRequest and
\* appends an AddServerCommand with the new server identity 
\* to its log and assumes the new configuration immediately.
\* To be valid a JoinRequest the following conditions are required:
\* - request received by a leader
\* - the joining node cannot already be a member
\* - the config id in the request must match the current config id
\* - the leader have no in-progress reconfiguration
\* - the leader must have committed an offset in the current epoch.
JoinCheck(i, m) ==
    CASE state[i] # Leader -> NotLeader
      [] m.msource \notin config[i].members -> "AlreadyMember"
      [] config[i].id # m.mconfigId -> "StaleConfig"
      [] HasPendingConfigCommand(i) -> "PendingReconfig"
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(i) -> "LeaderNotReady"
      [] OTHER -> Ok

AcceptJoinRequest ==
    /\ \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, JoinRequest, AnyEpoch)
        /\ LET i == m.mdest
               check == JoinCheck(i, m)
           IN
              /\ Cardinality(config[i].members) < MaxClusterSize
              /\ check = Ok
              \* state changes
              /\ LET addMember == m.maddMember
                     entry     == [command |-> AddServerCommand,
                                   epoch   |-> currentEpoch[i],
                                   value   |-> [id      |-> config[i].id + 1,
                                                new     |-> addMember,
                                                members |-> config[i].members \union {addMember}]]
                     newLog    == Append(log[i], entry)
                 IN  /\ log' = [log EXCEPT ![i] = newLog]
                     /\ config' = [config EXCEPT ![i] = 
                                        ConfigFor(Len(newLog),
                                                  entry, 
                                                  highWatermark[i])]
                     \* start tracking the end offset of this new member
                     /\ endOffset' = [endOffset EXCEPT ![i] = @ @@ (addMember :> 0)]
              /\ UNCHANGED <<servers, messages, candidateVars,
                             currentEpoch, state, leader, votedFor, pendingFetch,
                             highWatermark, auxVars>>  

\* ACTION: HandleLeaveRequest ----------------------------------
\* Leader i accepts a valid LeaveRequest and
\* appends a RemoveServerCommand, with identity of the server to remove, 
\* to its log and assumes the new configuration immediately.
\* To be valid a LeaveRequest the following conditions are required:
\* - request received by a leader
\* - the leaving node must be a member of the current configuration
\* - the leader have no in-progress reconfiguration
\* - the leader must have committed an offset in the current epoch.
LeaveCheck(i, j) ==
    CASE state[i] # Leader -> NotLeader
      [] j \in config[i].members -> "UnknownMember"
      [] HasPendingConfigCommand(i) -> "PendingReconfig"
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(i) -> "LeaderNotReady"
      [] OTHER -> Ok

HandleLeaveRequest ==
    \E i, leaver \in servers :
        /\ LeaveCheck(i, leaver) = Ok
        /\ Cardinality(config[i].members) > MinClusterSize
        \* state changes
        /\ LET entry        == [command |-> RemoveServerCommand,
                                epoch   |-> currentEpoch[i],
                                value   |-> [id      |-> config[i].id + 1,
                                             old     |-> leaver,
                                             members |-> config[i].members \ {leaver}]]
               newLog    == Append(log[i], entry)
           IN  /\ log' = [log EXCEPT ![i] = newLog]
               /\ config' = [config EXCEPT ![i] = 
                                  ConfigFor(Len(newLog),
                                            entry, 
                                            highWatermark[i])]
               \* remove tracking of the end offset of this member
               /\ endOffset' = [endOffset EXCEPT ![i] = 
                                  [j \in entry.value.members |-> endOffset[i][j]]]
        /\ UNCHANGED <<servers, messages, candidateVars,
                       currentEpoch, state, leader, votedFor, pendingFetch,
                       highWatermark, auxVars>>  

----
\* Defines how the variables may transition.
Next == 
\*        \/ RestartWithState
        \/ RestartWithoutState
        \* elections
        \/ RequestVote
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \/ BecomeLeader
        \* leader actions
        \/ ClientRequest
        \/ RejectFetchRequest
        \/ DivergingFetchRequest
        \/ AcceptFetchRequest
        \* follower actions
        \/ HandleBeginQuorumRequest
        \/ SendFetchRequest
        \/ HandleSuccessFetchResponse
        \/ HandleDivergingFetchResponse
        \/ HandleErrorFetchResponse
        \* reconfiguration actions
        \/ StartNewServer
        \/ AcceptPrepareJoinRequest
        \/ HandlePrepareJoinResponse
        \/ AcceptJoinRequest
        \/ HandleLeaveRequest
        
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
    \E offset \in DOMAIN log[i] :
        log[i][offset].value = v

ValueAllOrNothing(v) ==
    IF /\ electionCtr = MaxElections
       /\ ~\E i \in servers : state[i] = Leader
    THEN TRUE
    ELSE \/ \A i \in servers : ValueInServerLog(i, v)
         \/ ~\E i \in servers : ValueInServerLog(i, v)

ValuesNotStuck ==
    \A v \in Value : []<>ValueAllOrNothing(v)
    

\* INVARIANTS -------------------------

\* INV: NoIllegalState
\* If a server enters an illegal state then something went wrong.
\* An IllegalState should not be possible.
NoIllegalState ==
    ~\E i \in servers :
        state[i] = IllegalState

\* INV: NoLogDivergence
\* Each log offset is consistent across all servers (on those
\* servers whose highWatermark is equal or higher than the offset).
MinHighWatermark(s1, s2) ==
    IF highWatermark[s1] < highWatermark[s2]
    THEN highWatermark[s1]
    ELSE highWatermark[s2]

NoLogDivergence ==
    \A s1, s2 \in servers :
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
    ~\E i, j \in servers :
        /\ i # j
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
            ~\E i \in servers :
                \* is a leader
                /\ state[i] = Leader
                \* and which is the newest leader (aka not stale)
                /\ ~\E l \in servers : 
                    /\ l # i
                    /\ currentEpoch[l] > currentEpoch[i]
                \* and that is missing the value
                /\ ~\E offset \in DOMAIN log[i] :
                    log[i][offset].value = v
        ELSE TRUE



===============================================================================

\* Changelog:
