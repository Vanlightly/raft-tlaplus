--------------------------------- MODULE KRaftWithReconfig ---------------------------------
(*NOTES
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla.

-----------------------------------------------
Kafka KRaft TLA+ specification
-----------------------------------------------

This is a specification that is a mix of reverse engineering the
existing Kafka KRaft implementation (as of v3.2.0) plus the addition 
of reconfiguration and composite server identity which is at the time
of this writing being designed by myself and the Kafka core team at
Confluent.

This spec makes some effort to reuse some of the functions of the 
implementation in order to ensure it is accurately modelling 
the behaviour. 

KRaft is a pull variant of Raft, the original is push based. 

Note the following messages are not modelled:
- BeginQuorumResponse as this is only required by the implementation for liveness.
  If the leader doesn't receive a response it resends the BeginQuorumRequest. However,
  in the specification, message retries are implicit and so explicit retries
  are not required.
- EndQuorumRequest/Response as this exists as an optimization for a leader
  that gracefully shutsdown or has been removed from the congifuration. 
  It is not needed for correctness and so is not included.
- FetchSnapshotRequest/Response. This is a straight forward optimization
  and so has not been explicitly modelled. 

The KRaft implementation uses a cache object as an index for epochs and their start offsets
which is required for leaders to be able to give followers the information they need
to truncate their logs. This specification does not model this cache but simply looks up this
information from the log itself.

------------------------------------------------
Roles and Transitions

A KRaft server is either a Voter or an Observer. Voters
are full Raft partipants whereas observers can only
fetch and not change voter state.

Observers are able to keep fetching from the leader after
leader elections because when leadership changes, fetches
received by non-leaders are rejected reject and the response 
includes the current leader. If an observer doesn't know 
who the leader is then it chooses voters at random to 
fetch from until a voter can tell it who the leader is.

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
 
------------------------------------------------ 
Server identity - targeted for v3.3

A server's identity is a composite of the host and a randomly
generated disk id. The purpose of this randomly generated
component is to avoid a server from participating
in the cluster after being restarted without its state
such as after a disk failure or volume mount misconfiguration.

When a server starts without state it generates a fresh identity.
If it previously had state and a prior identity, this new identity
will not match and so the peer servers will not consider it
the same server and will not accept requests from it.

The only way to add a server with a new identity to the cluster
is via reconfiguration.

This specification uses a global counter to produce diskIds 
but an implementation would use a UUID. 

Each server uses a record like the following as its identity:
[host |-> s1, diskId |-> 7]

------------------------------------------------
Reconfiguration - targeted for v3.3

KRaft implements the one-at-a-time add or remove member 
reconfiguration algorithm instead of the Joint Consensus
algorithm. This restricts reconfiguration operations to 
one-at-a-time.

Please review the Raft thesis (not the paper) for a detailed 
description of the nuances of this reconfiguration protocol: 
https://web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf

Also note this bug in this thesis: 
https://groups.google.com/g/raft-dev/c/t4xj6dJTP6E?spm=a2c65.11461447.0.0.72ff5798NIE11G
This bug is fixed by the leader only adding reconfiguration 
commands once it has committed an entry in the current epoch.

Reconfigurations are performed by adding commands to the log. 
As soon as a server sees a reconfiguration command they 
immediately assume the new configuration. A reconfiguration 
is complete once the command gets committed. This means 
that a server can assume a new configuration but later
revert back to the prior configuration in the case of 
truncating their log after a leader election.

Adding a member
-----------------

In order to avoid liveness issues, the Raft thesis recommends 
that new members be non-voting until they catch-up. However,
this specification reverses the order by making a joinee 
catch-up first as an observer and then once it has done so,
allow it to send a JoinRequest to the leader who will add 
an AddServerCommand to its log. This makes for a simpler design.

Join sequence is the following:

===================
Joinee server                               Leader
  |                                           |  
  ----Fetch as an observer------------------->
  ...
(caught up to the leader)  
  ----JoinRequest(identity)------------------>
                                       (append AddServerCommand to log)
  <---JoinResponse{ok}------------------------
  ----Fetch as an observer------------------->
  ...
(receives the AddServerCommand and switches to this configuration)
  ----Fetch as voter ------------------------>
  ...  
===================

To be valid a JoinRequest the following conditions are required:
- request received by a leader (NotLeader error)
- the joining node cannot already be a member (AlreadyMember error)
- the leader have no in-progress reconfiguration (ReconfigInProgress error)
- the leader must have committed an offset in the current epoch. (LeaderNotReady error)

The JoinResponse is sent immediately (does not wait for the
command to be committed) and is either a success
response as the request met the conditions or an rejection.

In the case of a success response the joinee will continue fetching
as an observer until it receives the AddServerCommand. Once 
received it immediately assumes the configuration, becoming a Voter
follower.

If the joinee doesn't receive the command after a timeout time period it can resend
the join request.

In the case of a reject response, it depends on the error:
- NotLeader: If the response contains the real leader the joinee
             then sends a JoinRequest to that server.
             If the response contains no leader id then the joinee will
             revert to Unattached and start fetching from voters
             at random until it discovers the real leadeer and can then
             send it a join request.
- AlreadyMember: treats it as a success response.
- LeaderNotReady: waits a while and retries the join request
- ReconfigInProgress: waits a while and retries the join request


Removing a member
--------------------
An administrator will use a CLI to send a RemoveRequest to the current
leader, including the identity of the server to be removed.

Administrator                               Leader
   |                                          |
   ----RemoveRequest-------------------------->
                                (add RemoveServerCommand to log)
   <---RemoveResponse--------------------------                                       

To be valid a RemoveRequest the following conditions are required:
- request received by a leader (NotLeader error)
- the leaving node must be a member of the current 
  configuration (NotMember error).
- the leader have no in-progress reconfiguration 
  (ReconfigInProgress error).
- the leader must have committed an offset in 
  the current epoch. (LeaderNotReady error).

The RemoveResponse is sent immediately (does not 
wait for the command to be committed) and is 
either a success response as the request met 
the conditions or a rejection. In the case of a 
rejection the Administrator can decide whether
to wait or issue the command again.

A leader may have appended a RemoveServerCommand 
to its log where it is the server being removed. 
The leader switches immediately to this new configuration 
where it is no longer a voter and:
- becomes an observer
- continues to be leader in order to commit the command.

While it is a non-voter leader it does not include 
itself in the quorum for advancing the high watermark.
As soon as the command is committed the server resigns 
from leadership - becomes an regular observer.

Also very importantly, a voter follower that switches to
the new configuration where the leader is no longer
a member will still continue to send fetch requests to
the leader. This is required in order for the leader
to commit the command. Once the leader resigns it will
reject further fetch requests. Either an election timeout
will occur or a follower will receive an EndQuorumRequest
from the resigned leader.

This means that removing leaders puts us in a weird
situation where we have:
- an observer leader.
- voter followers fetching from an observer.
But as counterintuitive as this seems, it satisfies
both safety and liveness properties.

Additional reconfiguration nuance
--------------------------------
- A server can transition from observer to voter by either:
  - receiving an AddServerCommand in its log
  - truncating its log and reverting to the prior configuration
    where it was a member.
- A server can only start an election if it believes itself
  to be a voter. It can only be a voter if it is a member
  of the current configuration, else it would be an observer.
- A server can still do the following, even if it believes it
  is only an observer: 
  - participate in elections, this is because it may have 
    switched to a new configuration where it isn't a voter
    but that configuration doesn't ultimately get committed.
    So it may in fact still be required for the cluster to
    make progress.
- A server cannot do the following if it is not a voter:
  - Accept a BeginQuorumRequest, it must wait until it has joined the
    configuration by either else it could become a leader and yet not be
    a member. 
- Because servers immediately switch to new configurations,
  they must always be prepared to revert back to the prior
  configuration if the command of the current configuration
  gets removed during a log truncation.  
- How to track progress of a reconfiguration is not included in 
  this specification but should be simple enough by querying the leader
  about the state of its current configuration.
  
Note: final design may vary after KIP is posted and discussed by the community.  
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC, MessagePassing

\* The initial cluster size (the size can change over time due to reconfigurations)
CONSTANTS InitClusterSize, MinClusterSize, MaxClusterSize

\* The set of server IDs
CONSTANTS Hosts

\* The set of requests that can go into the log
CONSTANTS Value

\* Server roles
CONSTANTS Voter, Observer

\* Server states.
CONSTANTS Follower, Candidate, Leader, Unattached, Voted, Dead

\* Commands
CONSTANTS AppendCommand,        \* contains a client value
          InitClusterCommand,   \* contains the initial configuration
          AddServerCommand,     \* reconfiguration command to add a server
          RemoveServerCommand   \* reconfiguration command to remove a server

\* A reserved value.
CONSTANTS Nil

\* Response codes          
CONSTANTS Ok, NotOk, Diverging

\* Errors
CONSTANTS UnknownMember, AlreadyMember, ReconfigInProgress, LeaderNotReady,
          FencedLeaderEpoch, NotLeader, UnknownLeader

\* Special state that indicates a server has entered an illegal state
CONSTANTS IllegalState       

\* Limiting state space by limiting the number of elections and restarts           
CONSTANTS MaxElections, MaxRestarts,
          MaxAddReconfigs, MaxRemoveReconfigs,
          MaxTotalServers \* the maximum number of servers ever started
----
\* Global variables

VARIABLE servers

----
\* Per server variables (functions with domain Server).

\* The current configuration
VARIABLE config
\* The server's epoch number (the Raft term).
VARIABLE currentEpoch
\* The server's role (Voter or Observer)
VARIABLE role
\* The server's state (Follower, Candidate, Observer etc)
VARIABLE state
\* The candidate the server voted for in its current epoch.
VARIABLE votedFor
\* The peer that the server believes is the current leader
VARIABLE leader
\* Tracks the currently pending fetch request of a follower
VARIABLE pendingFetch
serverVars == <<config, currentEpoch, role, state, votedFor, leader, pendingFetch>>

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
\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<servers, messages, serverVars, candidateVars, leaderVars, logVars,
          auxVars>>
view == <<servers, messages, serverVars, candidateVars, leaderVars, logVars, acked >>
symmHosts == Permutations(Hosts)
symmValues == Permutations(Value)

----

\* Helpers

\* The message is of the type and has a matching epoch.
ReceivableMessage(m, mtype, epoch_match) ==
    /\ messages[m] > 0
    /\ state[m.mdest] # Dead
    /\ m.mtype = mtype
    /\ \/ epoch_match = AnyEpoch
       \/ /\ epoch_match = EqualEpoch
          /\ m.mepoch = currentEpoch[m.mdest]

VoterStates ==
    {Leader, Candidate, Follower, Unattached, Voted}
    
\* Note that a leader can be an observer as it
\* has been removed from the current configuration but
\* has no yet committed the RemoveServerCommand    
ObserverStates ==
    {Leader, Follower, Unattached, Voted}

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(ensemble) == {i \in SUBSET(ensemble) : Cardinality(i) * 2 > Cardinality(ensemble)}

\* The epoch of the last entry in a log, or 0 if the log is empty.
LastEpoch(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].epoch

NoOffsetTracker ==
    [s \in servers |-> 0]

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
\* Note that a leader may have resigned after being removed
\* from the configuration and have sent a fetch request to
\* a voter who still thinks this server is the leader.
\* So this conflicting view needs to be handled.
HasConsistentLeader(i, leaderId, epoch) ==
    IF leaderId = i
    THEN IF currentEpoch[i] = epoch /\ role[i] = Observer
         THEN TRUE \* no conflict, I may have resigned after being removed
         ELSE \* if the peer thinks I am leader, and I am really leader
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
      []  /\ leaderId # Nil  \* request contains leader 
          /\ leader[i] = Nil \* this server doesn't know who the leader is
          /\ leaderId # i    \* request leader is not this server 
                             \* (which can happen after a remove reconfig and this
                             \*  server was the leader and resigned to become an observer)
                          ->
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
    LET offset == CHOOSE offset \in DOMAIN serverLog : 
                    /\ IsConfigCommand(serverLog, offset)
                    /\ ~\E offset2 \in DOMAIN serverLog : 
                        /\ IsConfigCommand(serverLog, offset2)
                        /\ offset2 > offset
    IN [offset |-> offset, entry |-> serverLog[offset]]

NoConfig == 
    [id        |-> 0,
     members   |-> {},
     committed |-> FALSE]
              
ConfigFor(offset, reconfigEntry, ci) ==
    [id        |-> reconfigEntry.value.id,
     members   |-> reconfigEntry.value.members,
     committed |-> ci >= offset]

\* if the last configuration in the log is not
\* the same as the current cached configuration
\* then switch to the last configuration in the log.
\* This may be assuming a new configuration or
\* reverting to the prior configuration.  
MaybeSwitchConfigurations(i, currConfig) ==
    IF config[i].id = currConfig.id
    THEN UNCHANGED << config, role, state, endOffset>>
    ELSE
         /\ config' = [config EXCEPT ![i] = currConfig]
         /\ CASE role[i] = Voter /\ i \notin currConfig.members ->
                    /\ role'  = [role EXCEPT ![i] = Observer]
                    /\ state' = [state EXCEPT ![i] = Follower]
              [] role[i] = Observer /\ i \in currConfig.members ->
                    /\ role'  = [role EXCEPT ![i] = Voter]
                    /\ state' = [state EXCEPT ![i] = Follower]
              [] OTHER -> 
                    UNCHANGED << role, state >>
         \* ensure all members are in the endOffset map
         \* this is just so the model checker doesn't barf later
         /\ endOffset' = [endOffset EXCEPT ![i] =
                            [j \in servers |-> 
                                IF j \in DOMAIN endOffset[i]
                                THEN endOffset[i][j]
                                ELSE 0]]    

LeaderHasCommittedOffsetsInCurrentEpoch(i) ==
    \E offset \in DOMAIN log[i] :
        /\ log[i][offset].epoch = currentEpoch[i]
        /\ highWatermark[i] >= offset     

SetStateOfNewAndDeadIdentity(newIdentity, firstFetch, deadIdentity) ==
    /\ servers'         = servers \union {newIdentity}
    /\ config'          = config @@ (newIdentity :> NoConfig)
    /\ role'            = IF deadIdentity # Nil
                          THEN [role EXCEPT ![deadIdentity] = Dead] @@ (newIdentity :> Observer)
                          ELSE role @@ (newIdentity :> Observer)    
    /\ state'           = IF deadIdentity # Nil
                          THEN [state EXCEPT ![deadIdentity] = Dead] @@ (newIdentity :> Unattached)
                          ELSE state @@ (newIdentity :> Unattached)
    /\ currentEpoch'    = currentEpoch @@ (newIdentity :> 0)
    /\ leader'          = leader @@ (newIdentity :> Nil)
    /\ votedFor'        = votedFor @@ (newIdentity :> Nil)
    /\ pendingFetch'    = pendingFetch @@ (newIdentity :> firstFetch) 
    /\ votesGranted'    = votesGranted @@ (newIdentity :> {})
    /\ endOffset'       = endOffset @@ (newIdentity :> [j \in servers |-> 0])
    /\ log'             = log @@ (newIdentity :> <<>>)
    /\ highWatermark'   = highWatermark @@ (newIdentity :> 0) 

SetStateOfNewIdentity(identity, firstFetch) ==
    SetStateOfNewAndDeadIdentity(identity, firstFetch, Nil)

----
\* Define initial values for all variables

InitServerVars(initLeader, members) == 
    /\ servers      = members
    /\ currentEpoch = [i \in members |-> 1]
    /\ role         = [i \in members |-> Voter]
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
        /\ state'         = [state EXCEPT ![i] = Unattached]
        /\ leader'        = [leader EXCEPT ![i] = Nil]
        /\ votesGranted'  = [votesGranted EXCEPT ![i] = {}]
        /\ endOffset'     = [endOffset EXCEPT ![i] = [j \in servers |-> 0]]
        /\ highWatermark' = [highWatermark EXCEPT ![i] = 0]
        /\ pendingFetch'  = [pendingFetch EXCEPT ![i] = Nil]
        /\ restartCtr'    = restartCtr + 1
        /\ UNCHANGED <<servers, messages, config, currentEpoch, role, 
                       votedFor, log, acked, electionCtr,
                       addReconfigCtr, removeReconfigCtr, diskIdGen>>

\* ACTION: RestartWithoutState
\* A server that has state and is a member of the cluster
\* restarts with all state lost. Starting from blank state
\* causes the server to generate a new identity.
\* Either the original server is dead, or is remains as a
\* functioning zombie server.
RestartWithoutState ==
    /\ Cardinality(servers) < MaxTotalServers
    /\ \E i \in servers, leaveZombie \in BOOLEAN :
        /\ state[i] # Dead
        /\ \E j \in servers : i \in config[j].members
        /\ LET identity == [host |-> i.host, diskId |-> diskIdGen + 1]
           IN /\ IF leaveZombie
                 THEN SetStateOfNewAndDeadIdentity(identity, Nil, i)
                 ELSE SetStateOfNewIdentity(identity, Nil)
              /\ diskIdGen'       = diskIdGen + 1
        /\ UNCHANGED <<messages, acked, electionCtr, restartCtr,
                       addReconfigCtr, removeReconfigCtr>>

\* ACTION: RequestVote -----------------------------------------------
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote ==
    \E i \in servers :
        /\ electionCtr < MaxElections 
        /\ role[i] = Voter
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
        /\ UNCHANGED <<servers, config, role, acked, leaderVars, logVars, restartCtr,
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
                   /\ UNCHANGED <<servers, role, config, candidateVars, leaderVars, logVars, auxVars>>

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
              /\ role[i] = Voter \* new check because roles can change with reconfigurations
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
              /\ UNCHANGED <<servers, config, role, votedFor, pendingFetch, 
                             leaderVars, logVars, auxVars>>               

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
        /\ UNCHANGED <<servers, config, role, currentEpoch, votedFor, pendingFetch,
                       candidateVars, auxVars, logVars>>

\* ACTION: HandleBeginQuorumRequest -------------------------------------------
\* A server receives a BeginQuorumRequest and transitions to a follower
\* unless the message is stale.
\* Notes:
\* - a server can only accept a BeginQuorumRequest if it is in the current configuration
\*   else we open the door to it becoming leader even though it is not a member
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
                   /\ role[i] = Voter \* new check because roles can change with reconfigurations
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
        /\ UNCHANGED <<servers, config, role, votedFor, log, candidateVars,
                       leaderVars, highWatermark, auxVars>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
\* TODO: What if the leader is an observer because it got removed?
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
\* Follower i is either a Voter or an Observer.
\* Note that this server may have switched to a new configuration
\* where the leader is no longer a member, but this follower
\* will continue to send fetches to this leader in order for
\* that the leader to be able to commit the reconfig command.
\* Once the leader has committed the reconfig command it will resign
\* and reject further fetch requests.
SendFetchRequest ==
    \E i, j \in servers : 
        /\ i # j
        /\ \* either the follower (voter or observer) knows who the 
           \* leader is and can send a fetch request to the leader
           \/ /\ leader[i] = j
              /\ state[i] = Follower
           \* or we're an observer follower that doesn't know who the
           \* leader is and picks a random voter to fetch from, knowing
           \* that if it isn't the leader will include the leader id
           \* in its response if it knows.
           \/ /\ role[i] = Observer
              /\ state[i] = Unattached
              /\ j \in config[i].members 
        /\ pendingFetch[i] = Nil
        /\ LET lastLogOffset == Len(log[i])
               lastLogEpoch == IF lastLogOffset > 0 
                               THEN log[i][lastLogOffset].epoch
                               ELSE 0
               fetchMsg     == [mtype             |-> FetchRequest,
                                mepoch            |-> currentEpoch[i],
                                mfetchOffset      |-> lastLogOffset,
                                mlastFetchedEpoch |-> lastLogEpoch,
                                mobserver         |-> role[i] = Observer,
                                msource           |-> i,
                                mdest             |-> j]
           IN /\ pendingFetch' = [pendingFetch EXCEPT ![i] = fetchMsg]
              /\ Send(fetchMsg)
        /\ UNCHANGED <<servers, config, role, currentEpoch, state, 
                       votedFor, leader, candidateVars, leaderVars, 
                       logVars, auxVars>>

\* Fetch requests --------------------------------
\* Note that the server that receives a fetch request
\* can be the leader but not a voter. This can happen
\* when the leader has switched to being an observer
\* because it is an acting leader that is continuing until
\* it can commit a RemoveServerCommand which removes it from the
\* configuration.

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
                                        [] m.mobserver = FALSE /\ j \notin config[i].members -> UnknownMember
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
\* the epoch of the follower fetch position so it can truncate its
\* log and start fetching from a consistent offset.
DivergingFetchRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i                   == m.mdest
               j                   == m.msource
               validPosition       == ValidFetchPosition(i, m)
               validOffsetAndEpoch == EndOffsetForEpoch(i, m.mlastFetchedEpoch)
           IN  /\ state[i] = Leader
               /\ \/ m.mobserver = TRUE
                  \/ j \in config[i].members
               /\ ~validPosition 
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

\* ACTION: AcceptFetchRequestFromVoter ------------------
\* Leader i receives a FetchRequest from a voter at a valid 
\* position and responds with an entry if there is one or 
\* an empty response if not.
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
            THEN {i} \cup {k \in members : newEndOffset[k] >= offset }
            ELSE {k \in members : newEndOffset[k] >= offset }
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

AcceptFetchRequestFromVoter ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i             == m.mdest
               j             == m.msource
               validPosition == ValidFetchPosition(i, m)
               offset        == m.mfetchOffset + 1
               entries       == IF offset > Len(log[i])
                                THEN <<>>
                                ELSE <<log[i][offset]>>
           IN 
              /\ state[i] = Leader
              /\ m.mobserver = FALSE
              /\ j \in config[i].members
              /\ validPosition
              /\ LET newEndOffset  == [endOffset[i] EXCEPT ![j] = m.mfetchOffset]
                     newHwm        == NewHighwaterMark(i, newEndOffset)
                     leavesCluster == IsRemovedFromCluster(i, newHwm)
                     configEntry   == MostRecentReconfigEntry(log[i])
                 IN
                    /\ IF newHwm > highWatermark[i]
                       THEN /\ config' = [config EXCEPT ![i] = 
                                            \* may be update our cached config as committed
                                            ConfigFor(configEntry.offset, 
                                                      configEntry.entry, 
                                                      newHwm)]
                            /\ acked' = [v \in Value |-> 
                                            IF acked[v] = FALSE
                                            THEN v \in { log[i][ind].value : ind \in highWatermark[i]+1..newHwm }
                                            ELSE acked[v]]
                            /\ IF leavesCluster
                               THEN \* the server resigns and becomes an unattached observer
                                    /\ role'           = [role EXCEPT ![i] = Observer]
                                    /\ state'          = [state EXCEPT ![i] = Unattached]
                                    /\ leader'         = [leader EXCEPT ![i] = Nil]
                                    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                                    /\ endOffset'      = [endOffset EXCEPT ![i] = NoOffsetTracker]
                                    /\ highWatermark'  = [highWatermark EXCEPT ![i] = 0]
                               ELSE /\ endOffset'     = [endOffset EXCEPT ![i] = newEndOffset]
                                    /\ highWatermark' = [highWatermark EXCEPT ![i] = newHwm]
                                    /\ UNCHANGED <<role, state, leader, votesGranted>>
                       ELSE /\ endOffset' = [endOffset EXCEPT ![i] = newEndOffset]
                            /\ UNCHANGED <<role, config, state, leader, votesGranted, highWatermark, acked>>
                    /\ Reply([mtype       |-> FetchResponse,
                              mepoch      |-> currentEpoch[i],
                                              \* TODO: review this, should implement resignation in this spec?
                                              \* Strictly it is only needed for liveness.
                              mleader     |-> IF leavesCluster THEN Nil ELSE leader[i],
                              mresult     |-> Ok,
                              merror      |-> Nil,
                              mentries    |-> entries,
                              mhwm        |-> Min({newHwm, offset}),
                              msource     |-> i,
                              mdest       |-> j,
                              correlation |-> m], m)
                    /\ UNCHANGED <<servers, currentEpoch, log, 
                                   votedFor, pendingFetch, electionCtr, 
                                   restartCtr, addReconfigCtr, removeReconfigCtr, diskIdGen>>

\* ACTION: AcceptFetchRequestFromVoter ------------------
\* Leader i receives a FetchRequest from an observer at a valid 
\* position. It updates no local state but simply responds
\* with entries if there are any to return.
AcceptFetchRequestFromObserver ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchRequest, EqualEpoch)
        /\ LET i             == m.mdest
               j             == m.msource
               validPosition == ValidFetchPosition(i, m)
               offset        == m.mfetchOffset + 1
               entries       == IF offset > Len(log[i])
                                THEN <<>>
                                ELSE <<log[i][offset]>>
           IN 
              /\ state[i] = Leader
              /\ m.mobserver = TRUE
              /\ validPosition
              /\ Reply([mtype       |-> FetchResponse,
                        mepoch      |-> currentEpoch[i],
                        mleader     |-> leader[i],
                        mresult     |-> Ok,
                        merror      |-> Nil,
                        mentries    |-> entries,
                        mhwm        |-> Min({offset, highWatermark[i]}),
                        msource     |-> i,
                        mdest       |-> j,
                        correlation |-> m], m)
              /\ UNCHANGED <<servers, serverVars, candidateVars, leaderVars,
                             logVars, auxVars>>
       
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
           IN /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Ok
              \* The server could have received a reconfiguration command
              /\ MaybeSwitchConfigurations(i, currConfig)                    
              \* update log and hwm
              /\ highWatermark'  = [highWatermark  EXCEPT ![i] = m.mhwm]
              /\ log' = newLog
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil]
              /\ Discard(m)
              /\ UNCHANGED <<servers, currentEpoch, leader, votedFor, 
                             candidateVars, auxVars>>

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
              /\ newState.handled = FALSE
              /\ pendingFetch[i] = m.correlation
              /\ m.mresult = Diverging
              \* The server could have truncated the reconfig command
              \* of the current configuration, causing the server
              \* to revert to the prior configuration.
              /\ MaybeSwitchConfigurations(i, currConfig)
              \* update log
              /\ log' = newLog
              /\ pendingFetch' = [pendingFetch EXCEPT ![i] = Nil] 
              /\ Discard(m)
        /\ UNCHANGED <<servers, currentEpoch, leader, votedFor, 
                       candidateVars, highWatermark, auxVars>>
                       
\* ACTION: HandleErrorFetchResponse
\* Server i receives a FetchResponse with an error from server j with
\* Depending on the error, the follower may transition to being unattached
\* or being the follower of a new leader that it was not aware of.
\* If this is an observer and the error was NotLeader and the id of
\* the leader was included in the response, the observer can now send
\* fetches to that leader. 
HandleErrorFetchResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, FetchResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ newState.handled = TRUE
              /\ pendingFetch[i] = m.correlation
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              \* if the response is UnknownMember then it possible
              \* the current configuration got truncated after a leader election
              \* and so this server should switch to being an Observer
              \* If it gets made a member again it will discover that in its log.
              /\ IF m.merror = UnknownMember
                 THEN role' = [role EXCEPT ![i] = Observer]
                 ELSE UNCHANGED <<role>>
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
\* called diskId and in the observer role.
StartNewServer ==
    /\ Cardinality(servers) < MaxTotalServers
    /\ \E host \in Hosts, anyLeader \in servers :
        LET diskId    == diskIdGen + 1
            identity  == [host |-> host, diskId |-> diskId]
        IN /\ state[anyLeader] = Leader \* this is a shortcut, but a safe one.
           /\ diskIdGen'       = diskIdGen + 1
           /\ LET fetchMsg == [mtype             |-> FetchRequest,
                               mepoch            |-> 0,
                               mfetchOffset      |-> 0,
                               mlastFetchedEpoch |-> 0,
                               mobserver         |-> TRUE,
                               msource           |-> identity,
                               mdest             |-> anyLeader]
              IN /\ SetStateOfNewIdentity(identity, fetchMsg)
                 /\ Send(fetchMsg)
           /\ UNCHANGED << acked, electionCtr, restartCtr, addReconfigCtr, 
                           removeReconfigCtr >>

\* ACTION: SendJoinRequest
\* An observer can request to join the cluster as a voter
\* at any time in this specification. However, in the
\* implementation this should be restricted to when the
\* observer has caught up with the leader to avoid
\* liveness issues. How the observer knows it has caught up
\* is another question and simply receiving an empty fetch
\* response may not be enough as under heavy load, there may always be
\* more offsets to fetch!
SendJoinRequest ==
    /\ addReconfigCtr < MaxAddReconfigs
    /\ \E i, j \in servers :
        /\ role[i] = Observer
        /\ i \notin config[i].members
        /\ leader[i] = j
        /\ Send([mtype      |-> JoinRequest,
                 mepoch     |-> currentEpoch[i],
                 mdest      |-> j,
                 msource    |-> i])
        /\ UNCHANGED <<servers, serverVars, candidateVars, leaderVars, 
                       logVars, auxVars>>
              
\* ACTION: AcceptJoinRequest ----------------------------------
\* Leader i accepts a valid JoinRequest and appends an 
\* AddServerCommand with the new server identity 
\* to its log and assumes the new configuration immediately.
\* To be valid a JoinRequest the following conditions are required:
\* - request received by a leader
\* - the joining node cannot already be a member
\* - the leader have no in-progress reconfiguration
\* - the leader must have committed an offset in the current epoch.
JoinCheck(i, m) ==
    CASE state[i] # Leader -> NotLeader
      [] m.msource \in config[i].members -> AlreadyMember
      [] HasPendingConfigCommand(i) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(i) -> LeaderNotReady
      [] OTHER -> Ok

AcceptJoinRequest ==
    /\ \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, JoinRequest, AnyEpoch)
        /\ LET i     == m.mdest
               j     == m.msource
               check == JoinCheck(i, m)
           IN
              /\ Cardinality(config[i].members) < MaxClusterSize
              /\ check = Ok
              \* state changes
              /\ LET entry     == [command |-> AddServerCommand,
                                   epoch   |-> currentEpoch[i],
                                   value   |-> [id      |-> config[i].id + 1,
                                                new     |-> j,
                                                members |-> config[i].members \union {j}]]
                     newLog    == Append(log[i], entry)
                 IN  /\ log' = [log EXCEPT ![i] = newLog]
                     /\ config' = [config EXCEPT ![i] = 
                                        ConfigFor(Len(newLog),
                                                  entry, 
                                                  highWatermark[i])]
                     \* start tracking the end offset of this new member
                     /\ endOffset' = [endOffset EXCEPT ![i] = @ @@ (j :> 0)]
                     /\ Reply([mtype   |-> JoinResponse,
                               mepoch  |-> currentEpoch[i],
                               mleader |-> leader[i],
                               mresult |-> Ok,
                               merror  |-> Nil,
                               mdest   |-> j,
                               msource |-> i], m)
              /\ UNCHANGED <<servers, candidateVars, role, currentEpoch, state, leader, 
                             votedFor, pendingFetch, highWatermark, auxVars>>

\* ACTION: RejectJoinRequest ----------------------------------
\* Server i rejects an invalid JoinRequest.
\*
\* Model checking note:
\* Note in this specification we only send a rejection
\* for a check result that is NotLeader or AlreadyMember.
\* For the check results ReconfigInProgress and LeaderNotReady
\* we simply don't send a response at all until either
\* the request can be accepted or rejected. This avoids
\* the need for modeling retries which would increase the state
\* space and make liveness hard to check due to infinite retries.
\* The implementation would send rejections immediately.
RejectJoinRequest ==
    /\ \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, JoinRequest, AnyEpoch)
        /\ LET i == m.mdest
               j == m.msource
               check == JoinCheck(i, m)
           IN
              /\ check \in {NotLeader, AlreadyMember}
              \* state changes
              /\ Reply([mtype   |-> JoinResponse,
                        mepoch  |-> currentEpoch[i],
                        mleader |-> leader[i],
                        mresult |-> NotOk,
                        merror  |-> check,
                        mdest   |-> j,
                        msource |-> i], m)
              /\ UNCHANGED <<servers, serverVars, candidateVars,
                             leaderVars, logVars, auxVars>>                                 

\* ACTION: HandleJoinResponse ----------------------------------
\* Observer i receives a JoinResponse. If it was a rejection
\* then we may:
\* - transition to unattached if the source doesn't know who the leader is
\* - send a new JoinRequest if the error wasn't AlreadyMember and the source
\*   knows who the leader is
\* If it was a success response then the observer simply carries on being an observer
\* until it sees the AddServerCommand in our log.
HandleJoinResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, JoinResponse, AnyEpoch)
        /\ LET i        == m.mdest
               j        == m.msource
               newState == MaybeHandleCommonResponse(i, m.mleader, m.mepoch, m.merror)
           IN
              /\ role[i] = Observer
              /\ newState.handled = TRUE
              /\ state' = [state EXCEPT ![i] = newState.state]
              /\ leader' = [leader EXCEPT ![i] = newState.leader]
              /\ currentEpoch' = [currentEpoch EXCEPT ![i] = newState.epoch]
              /\ IF m.merror # AlreadyMember /\ newState.leader # Nil
                 THEN Reply([mtype      |-> JoinRequest,
                             mepoch     |-> newState.epoch,
                             mdest      |-> newState.leader,
                             msource    |-> i], m)
                 ELSE Discard(m)
        /\ UNCHANGED <<servers, role, config, votedFor, pendingFetch, candidateVars, leaderVars, 
                       logVars, auxVars>>   

\* ACTION: HandleRemoveRequest ----------------------------------
\* Leader i accepts a valid RemoveRequest from an Administrator and
\* appends a RemoveServerCommand, with the identity of the server to remove, 
\* to its log and assumes the new configuration immediately.
\*
\* To be valid a RemoveRequest the following conditions are required:
\* - request received by a leader
\* - the leaving node must be a member of the current configuration
\* - the leader have no in-progress reconfiguration
\* - the leader must have committed an offset in the current epoch.
\*
\* Note that this server may be the one being removed. In that case
\* it switches to being an observer but continues as leader. Once it 
\* has committed the command it will resign.
RemoveCheck(i, j) ==
    CASE state[i] # Leader -> NotLeader
      [] j \notin config[i].members -> UnknownMember
      [] HasPendingConfigCommand(i) -> ReconfigInProgress
      [] ~LeaderHasCommittedOffsetsInCurrentEpoch(i) -> LeaderNotReady
      [] OTHER -> Ok

HandleRemoveRequest ==
    \E i, removeServer \in servers :
        /\ removeReconfigCtr < MaxRemoveReconfigs
        /\ RemoveCheck(i, removeServer) = Ok
        /\ Cardinality(config[i].members) > MinClusterSize
        \* state changes
        /\ LET entry        == [command |-> RemoveServerCommand,
                                epoch   |-> currentEpoch[i],
                                value   |-> [id      |-> config[i].id + 1,
                                             old     |-> removeServer,
                                             members |-> config[i].members \ {removeServer}]]
               newLog    == Append(log[i], entry)
           IN  /\ log' = [log EXCEPT ![i] = newLog]
               /\ config' = [config EXCEPT ![i] = 
                                  ConfigFor(Len(newLog),
                                            entry, 
                                            highWatermark[i])]
               /\ IF i = removeServer
                  THEN role' = [role EXCEPT ![i] = Observer]
                  ELSE UNCHANGED role
               \* remove tracking of the end offset of this member
               /\ endOffset' = [endOffset EXCEPT ![i] = 
                                  [j \in entry.value.members |-> endOffset[i][j]]]
        /\ UNCHANGED <<servers, messages, candidateVars, 
                       currentEpoch, state, leader, votedFor, pendingFetch,
                       highWatermark, auxVars>>  

----
\* Defines how the variables may transition.
Next == 
        \/ RestartWithState
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
        \/ AcceptFetchRequestFromVoter
        \/ AcceptFetchRequestFromObserver
        \* follower actions
        \/ HandleBeginQuorumRequest
        \/ SendFetchRequest
        \/ HandleSuccessFetchResponse
        \/ HandleDivergingFetchResponse
        \/ HandleErrorFetchResponse
        \* reconfiguration actions
        \/ StartNewServer
        \/ SendJoinRequest
        \/ AcceptJoinRequest
        \/ RejectJoinRequest
        \/ HandleJoinResponse
        \/ HandleRemoveRequest

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

\* INV: StatesMatchRoles
\* Ensures that the combination of state and role remains consistent
StatesMatchRoles ==    
    ~\E i \in servers :
        \/ /\ role[i] = Observer
           /\ state[i] \notin ObserverStates
        \/ /\ state[i] = Unattached
           /\ leader[i] # Nil

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
\* Note: GUNMETAL is my (Jack here) beast workstation built for model checking specs. 
\* Modification History
\* Last modified Sat Jul 16 18:02:31 CEST 2022 by GUNMETAL
\* Last modified Sat Jul 16 11:14:02 CEST 2022 by jvanlightly
\* Created Wed Jun 29 17:56:38 CEST 2022 by jvanlightly