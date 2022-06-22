--------------------------------- MODULE RaftWithReconfigAddRemove ---------------------------------
(* NOTES 
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

This is a model checking optimized fork of original spec.

This specification specifically implements the simpler addServer/removeServer 
approach as described in the Raft thesis: 
https://web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf

- Summary of changes:
    - updated message helpers:
        - prevent some infinite cycles of message passing
        - can only receive a message that hasn't been delivered yet
    - optimized for model checking (reduction in state space)
        - removed history variables (using simple invariants instead).
        - decomposed "receive" into separate actions.
        - compressed multi-step append entries request processing into one.
        - compressed timeout and requestvote into single action.
        - server directly votes for itself in an election (it doesn't send itself a vote request).
        - various auxilliary variables for limiting the number of times certain actions
          can occur.
    - actions are organised into the enabling conditions and the state changes for better readability
    - fixed some bugs
        - adding the same value to the log over and over again
        - allowing actions to remain enabled producing odd results
    - reconfiguration (add and remove as per the thesis)
        - there are many ways to initialize a cluster, in this spec the cluster is already
          initialized with an InitClusterCommand log entry.
        - uses snapshots to bring new members up to date rather than the non-voting
          member strategy used in the Raft thesis. The effect is the same but
          with a much smaller state space.
        - reconfiguration is performed one operation at a time and one
          operation can only add or remove a single server
        - the constant IncludeThesisBug controls whether a bug in the original
          thesis is included or not. Setting this to true will result
          in invariant violations for some configurations.
    - invariants
        - no log divergence
        - acked values always present on current leader
        - no more than one reconfiguration at a time
    - liveness
        - ensure that once a leader starts a reconfiguration
          that eventually all members of the new configuration
          switch to it (as long as an election doesn't cut it short).
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

\* The initial cluster size (the size can change over time due to reconfigurations)
CONSTANTS InitClusterSize

\* The set of server IDs
CONSTANTS Server

\* The set of client values that can go into the log
CONSTANTS Value

\* Server states. NotMember is strictly not necessary as it
\* not included in the paper.
CONSTANTS Follower, Candidate, Leader, NotMember

\* Commands
CONSTANTS AppendCommand,        \* contains a client value
          InitClusterCommand,   \* contains the initial configuration
          AddServerCommand,     \* reconfiguration command to add a server
          RemoveServerCommand   \* reconfiguration command to remove a server

\* A reserved value.
CONSTANTS Nil

\* AppendEntries response codes
CONSTANTS Ok, StaleTerm, EntryMismatch, NeedSnapshot

\* Message types
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          SnapshotRequest, SnapshotResponse

\* Used for filtering messages under different circumstances
CONSTANTS EqualTerm, LessOrEqualTerm

\* Limiting state space by limiting the number of elections, restarts etc           
CONSTANTS MaxElections, MaxRestarts, MaxValuesPerTerm,
          MaxAddReconfigs, MaxRemoveReconfigs, MinClusterSize

\* When TRUE, implements reconfiguration according to the thesis.
\* When FALSE, uses the fix documented here: https://groups.google.com/g/raft-dev/c/t4xj6dJTP6E?spm=a2c65.11461447.0.0.72ff5798NIE11G
CONSTANTS IncludeThesisBug

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages
----
\* Auxilliary variables (used for state-space control, invariants etc)

\* The values that have been received from a client and whether
\* the value has been acked back to the client. Used in invariants to
\* detect data loss.
VARIABLE acked
\* Counter for elections, restarts, reconfigurations and values per term
\* (to control state space)
VARIABLE electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr, valueCtr
auxVars == <<acked, electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr, valueCtr>>
----
\* Per server variables (functions with domain Server).
\* The current configuration
VARIABLE config
\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, Leader or NotMember).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<config, currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry.
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

candidateVars == <<votesGranted>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
\* Tracks which peers a leader is waiting on a response for.
\* Used for one-at-a-time AppendEntries RPCs. Not really required but
\* permitting out of order requests explodes the state space.
VARIABLE pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>

\* End of per server variables.
----

ASSUME IncludeThesisBug \in BOOLEAN

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars,
          auxVars>>
view == <<messages, serverVars, candidateVars, leaderVars, logVars >>
symmServers == Permutations(Server)
symmValues == Permutations(Value)
----
\* ----------------------------------------------
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
\* Very inefficient for TLC - TODO replace.
Quorum(cluster) ==
    {i \in SUBSET(cluster) : Cardinality(i) * 2 > Cardinality(cluster)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Send the message whether it already exists or not.
_SendNoRestriction(m) ==
    IF m \in DOMAIN messages
    THEN messages' = [messages EXCEPT ![m] = @ + 1]
    ELSE messages' = messages @@ (m :> 1)
    
\* Will only send the message if it hasn't been sent before.
\* Basically disables the parent action once sent.    
_SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)    

\* Add a message to the bag of messages. 
\* Note 1: to prevent infinite cycles, empty 
\* AppendEntriesRequest messages can only be sent once.
\* Note 2: a message can only match an existing message
\* if it is identical (all fields).
Send(m) ==
    IF /\ m.mtype = AppendEntriesRequest
       /\ m.mentries = <<>>
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
Reply(response, request) ==
    /\ messages[request] > 0 \* request must exist
    /\ \/ /\ response \notin DOMAIN messages \* response does not exist, so add it
          /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)
       \/ /\ response \in DOMAIN messages \* response was sent previously, so increment delivery counter
          /\ messages' = [messages EXCEPT ![request] = @ - 1,
                                          ![response] = @ + 1]

\* TRUE when the messageis of the type and has a matching term.
\* Messages with a higher term are handled by the action UpdateTerm
ReceivableMessage(m, mtype, term_match) ==
    /\ messages[m] > 0
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* the index points to a reconfiguration command in the log
IsConfigCommand(serverLog, index) ==
    serverLog[index].command \in {InitClusterCommand,
                                  AddServerCommand, 
                                  RemoveServerCommand}

\* A leader only allows one uncommitted reconfiguration command
\* at a time.
HasPendingConfigCommand(i) ==
    config[i].committed = FALSE

\* Returns the most recent config command entry
MostRecentReconfigEntry(serverLog) ==
    LET index == CHOOSE index \in DOMAIN serverLog : 
                    /\ IsConfigCommand(serverLog, index)
                    /\ ~\E index2 \in DOMAIN serverLog : 
                        /\ IsConfigCommand(serverLog, index2)
                        /\ index2 > index
    IN [index |-> index, entry |-> serverLog[index]]

NoConfig == 
    [members   |-> {},
     committed |-> FALSE]
              
ConfigFor(index, reconfigEntry, ci) ==
    [members   |-> reconfigEntry.value.members,
     committed |-> ci >= index]

\* Used in nextIndex to indicate snapshots should/have been sent
PendingSnapshotRequest == -1
PendingSnapshotResponse == -2

\* Required for the thesis bug fix
LeaderHasCommittedEntriesInCurrentTerm(i) ==
    \E index \in DOMAIN log[i] :
        /\ log[i][index].term = currentTerm[i]
        /\ commitIndex[i] >= index

----
\* Define initial values for all variables

InitServerVars(leader, members) == 
    /\ currentTerm = [i \in Server |-> IF i \in members
                                       THEN 1 ELSE 0]
    /\ state       = [i \in Server |-> CASE i = leader -> Leader
                                         [] i \in members -> Follower
                                         [] OTHER -> NotMember]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ config      = [i \in Server |->
                            IF i \in members
                            THEN [members        |-> members,
                                  committed      |-> TRUE]
                            ELSE NoConfig]
    
InitCandidateVars == votesGranted   = [i \in Server |-> {}]

InitLeaderVars(leader, members) == 
    /\ nextIndex       = [i \in Server |-> [j \in Server |-> 
                            IF i = leader /\ j \in members
                            THEN 2 ELSE 1]]
    /\ matchIndex      = [i \in Server |-> [j \in Server |-> 
                            IF i = leader /\ j \in members
                            THEN 1 ELSE 0]]
    /\ pendingResponse = [i \in Server |-> [j \in Server |-> FALSE]]

InitLogVars(members, firstEntry) == 
    /\ log         = [i \in Server |-> 
                        IF i \in members
                        THEN << firstEntry >>
                        ELSE << >>]
    /\ commitIndex = [i \in Server |-> 
                        IF i \in members
                        THEN 1 ELSE 0]

InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ addReconfigCtr = 0
               /\ removeReconfigCtr = 0
               /\ acked = [v \in Value |-> Nil]
               /\ valueCtr = [v \in 1..MaxElections+1 |-> 0]

\* This specification installs a pre-made cluster.
Init == LET members    == CHOOSE s \in SUBSET Server :
                              Cardinality(s) = InitClusterSize
            leader     == CHOOSE i \in members : TRUE
            firstEntry == [command |-> InitClusterCommand,
                           term    |-> 1,
                           value   |-> [members |-> members]]
        IN
            /\ messages = [m \in {} |-> 0]
            /\ InitServerVars(leader, members)
            /\ InitCandidateVars
            /\ InitLeaderVars(leader, members)
            /\ InitLogVars(members, firstEntry)
            /\ InitAuxVars

----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    \* enabling conditions
    /\ restartCtr < MaxRestarts
    \* state changes
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr'      = restartCtr + 1
    /\ UNCHANGED <<messages, config, currentTerm, votedFor, log, 
                   acked, electionCtr, addReconfigCtr, removeReconfigCtr, valueCtr>>
                   
\* ACTION: ResetWithSameIdentity ----------------------------------
\* An administrator starts up a removed node with empty state but the same identity.
\* Reasons to do this might be starting up a server with a replaced disk
\* or simply wiping the state of a removed node in order to save disk space.
\* The administrator only does this if the current leader confirms that
\* the server is not in the current configuration.

IsCurrentLeader(i) ==
\* TRUE if i believes itself to be leader and doesn''t have a stale term
    /\ state[i] = Leader
    \* and which is the newest leader (aka not stale)
    /\ ~\E l \in Server : 
        /\ l # i
        /\ currentTerm[l] > currentTerm[i]
     
IsSafeToWipe(i) ==
\* TRUE if the current leader's current configuration
\* is committed and i is not a member of this configuration
    /\ \E s \in Server : IsCurrentLeader(s)
    /\ LET leader == CHOOSE s \in Server : IsCurrentLeader(s)
       IN 
          /\ leader # i
          /\ i \notin config[leader].members
          /\ config[leader].committed = TRUE

ResetWithSameIdentity(i) ==
    \* enabling conditions
    /\ IsSafeToWipe(i)    \* the server is not part of the current configuration
    /\ currentTerm[i] > 0 \* the server has state (i.e) it has been a cluster member
    \* state changes
    /\ state'           = [state EXCEPT ![i] = NotMember]
    /\ config'          = [config EXCEPT ![i] = NoConfig]
    /\ currentTerm'     = [currentTerm EXCEPT ![i] = 0]
    /\ votedFor'        = [votedFor    EXCEPT ![i] = Nil]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ log'             = [log EXCEPT ![i] = <<>>]
    /\ UNCHANGED <<messages, auxVars>>                   

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ m.mterm > currentTerm[m.mdest]
        \* state changes
        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
           \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<messages, config, candidateVars, leaderVars, logVars, auxVars>>
        
\* ----------------------------------------------
\* ELECTIONS ------------------------------------

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
\* Note that this spec has no timeout implementation, instead it 
\* simply allows an election to occur at any time.
RequestVote(i) ==
    \* enabling conditions
    /\ electionCtr < MaxElections
    /\ state[i] \in {Follower, Candidate}
    /\ i \in config[i].members
    \* state changes
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentTerm'  = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr'  = electionCtr + 1
    /\ SendMultipleOnce(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in config[i].members \ {i}})
    /\ UNCHANGED <<acked, config, leaderVars, logVars, restartCtr,
                   addReconfigCtr, removeReconfigCtr, valueCtr>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                        \/ /\ m.mlastLogTerm = LastTerm(log[i])
                           /\ m.mlastLogIndex >= Len(log[i])
               grant == /\ m.mterm = currentTerm[i]
                        /\ logOk
                        /\ votedFor[i] \in {Nil, j}
            IN /\ m.mterm <= currentTerm[i]
               \* state changes
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ Reply([mtype        |-> RequestVoteResponse,
                         mterm        |-> currentTerm[i],
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j],
                         m)
               /\ UNCHANGED <<config, state, currentTerm, candidateVars, leaderVars, 
                              logVars, auxVars>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ state[i] = Candidate \* if it already lost the election don't bother processing this
              \* state changes
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, 
                             auxVars>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
\* Note that this specification sets the nextIndex to be 1 entry past the end of
\* the leaders log (as per the Raft paper). However, an optimization is for 
\* voters to include their last log index and term in their vote and for the 
\* leader to use this to find the highest common index in both logs and set
\* nextIndex to that value + 1.
VotesGrantedInSet(i, memberSet) ==
    memberSet \intersect votesGranted[i]

BecomeLeader(i) ==
    \* enabling conditions
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum(config[i].members)
    \* state changes
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] =
                                [j \in Server |-> FALSE]]
    /\ UNCHANGED <<messages, config, currentTerm, votedFor, candidateVars, 
                   auxVars, logVars>>

\* ----------------------------------------------
\* REPLICATION ----------------------------------

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add value v to the log.
ClientRequest(i, v) ==
    \* enabling conditions
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ valueCtr[currentTerm[i]] < MaxValuesPerTerm
    \* state changes
    /\ LET entry == [command |-> AppendCommand,
                     term    |-> currentTerm[i],
                     value   |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
           /\ valueCtr' = [valueCtr EXCEPT ![currentTerm[i]] = @ + 1]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, electionCtr, 
                   restartCtr, addReconfigCtr, removeReconfigCtr>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    \* enabling conditions
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in config[i].members       \* j is a member
    /\ nextIndex[i][j] >= 0          \* not pending a snapshot
    /\ pendingResponse[i][j] = FALSE \* not already waiting for a response
    \* state changes
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm  == IF prevLogIndex > 0
                           THEN log[i][prevLogIndex].term
                           ELSE 0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry    == Min({Len(log[i]), nextIndex[i][j]})
           entries      == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN 
          /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = TRUE]
          /\ Send([mtype         |-> AppendEntriesRequest,
                  mterm          |-> currentTerm[i],
                  mprevLogIndex  |-> prevLogIndex,
                  mprevLogTerm   |-> prevLogTerm,
                  mentries       |-> entries,
                  mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                  msource        |-> i,
                  mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, 
                   nextIndex, matchIndex, logVars, auxVars>>

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\*
\* Note 1: we don't advance the commit index one at a time because
\* a new leader can only advance the commit index when it is able
\* to majority replicate an entry in the new term - so it may be 
\* forced to advance the commit index by multiple entries.
\*
\* Note 2: If the commit index reaches a RemoveServerCommand and the server
\* is no longer a member, it leaves by resetting its non-durable state.
MayBeAckClient(i, newCommitIndex) ==
    [v \in Value |-> 
        IF /\ acked[v] = FALSE 
           /\ \E ind \in DOMAIN log[i] :
                /\ ind > commitIndex[i]
                /\ ind <= newCommitIndex 
                /\ log[i][ind].command = AppendCommand
                /\ log[i][ind].value = v
        THEN TRUE
        ELSE acked[v]]
        
IsRemovedFromCluster(i, newCommitIndex) ==
    \E index \in DOMAIN log[i] :
        /\ index > commitIndex[i]
        /\ index <= newCommitIndex
        /\ log[i][index].command = RemoveServerCommand
        /\ i \notin log[i][index].value.members

AdvanceCommitIndex(i) ==
    \* enabling conditions
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           \* If the leader is not in the current member set due
           \* to an in-progress reconfiguration then it does not 
           \* include itself in the quorum
           Agree(index, memberSet) == 
                    IF i \in memberSet
                    THEN {i} \union {k \in memberSet : matchIndex[i][k] >= index }
                    ELSE {k \in memberSet : matchIndex[i][k] >= index }
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index, config[i].members) \in Quorum(config[i].members)}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           currConfig == MostRecentReconfigEntry(log[i]) 
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          \* state changes
          /\ acked' = MayBeAckClient(i, newCommitIndex)
          /\ config' = [config EXCEPT ![i] = ConfigFor(currConfig.index, currConfig.entry, newCommitIndex)]
          /\ IF IsRemovedFromCluster(i, newCommitIndex)
             THEN /\ state'          = [state EXCEPT ![i] = NotMember]
                  /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                  /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
                  /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
                  /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
             ELSE /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                  /\ UNCHANGED <<state, votesGranted, nextIndex, matchIndex>>
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, 
                   pendingResponse, electionCtr, restartCtr, addReconfigCtr, removeReconfigCtr, valueCtr>>

\* ACTION: RejectAppendEntriesRequest -------------------
\* A follower can reject if:
\* - the term of the message is stale
\* - or the message entry is too high (beyond the last log entry + 1)
\* - or the member is new and needs a snapshot instead

LogOk(i, m) ==
    \* note that in this spec, the log cannot be empty as it is seeded
    \* with an InitClusterCommand. So an empty AppendEntries does not
    \* mean the log is empty, only that the follower is caught up.
    
    \* an non-empty AppendEntries can be an append or a truncate scenario.
    \* It will append when m.mprevLogIndex = Len(log[i])
    \* It will truncate when m.mprevLogIndex < Len(log[i])
    IF m.mentries # <<>>
    THEN /\ m.mprevLogIndex > 0
         /\ m.mprevLogIndex <= Len(log[i])
         /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    ELSE
         \* if its an empty RPC then the mprevLogIndex should line-up
         \* perfectly with the end of the log.
         /\ m.mentries = <<>>
         /\ m.mprevLogIndex = Len(log[i])
         /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

RejectAppendEntriesRequest ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
           IN LET rc == CASE m.mterm < currentTerm[i] -> StaleTerm
                          [] i \notin config[i].members -> NeedSnapshot
                          [] /\ m.mterm = currentTerm[i]
                             /\ state[i] = Follower
                             /\ \lnot logOk -> EntryMismatch
                          [] OTHER -> Ok
              IN
                   /\ rc # Ok
                   \* state changes
                   /\ Reply([mtype       |-> AppendEntriesResponse,
                             mterm       |-> currentTerm[i],
                             mresult     |-> rc,
                             mmatchIndex |-> 0,
                             msource     |-> i,
                             mdest       |-> j],
                             m)
                   /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, 
                                  logVars, auxVars>>

\* ACTION: AcceptAppendEntriesRequest ------------------
\* The original spec had a 'receive' action with three sub actions, 
\* this version is compressed into a single action to reduce state space.
\* In one step it can:
\* - truncate the log
\* - append an entry to the log
\* - respond to the leader      
\* if there is a reconfiguration command in the entries then the
\* server assumes this new configuration immediately (even if it is not
\* a member of the new configuration).   
CanAppend(m, i) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    
NeedsTruncation(m, i, index) ==
   /\ m.mentries /= << >>
   /\ Len(log[i]) >= index
   /\ log[i][index].term /= m.mentries[1].term

TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequest ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN 
              /\ state[i] \in { Follower, Candidate }
              /\ logOk
              /\ i \in config[i].members \* must know its a member, else it needs a snapshot
              \* state changes
              /\ LET newLog      == IF CanAppend(m, i)
                                    THEN [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                                    ELSE IF NeedsTruncation(m, i , index)
                                         THEN [log EXCEPT ![i] = Append(TruncateLog(m, i), m.mentries[1])]
                                         ELSE log
                     configEntry == MostRecentReconfigEntry(newLog[i])
                     currConfig  == ConfigFor(configEntry.index,
                                              configEntry.entry,
                                              m.mcommitIndex)
                 IN
                    /\ config' = [config EXCEPT ![i] = currConfig]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                    /\ state' = [state EXCEPT ![i] = IF i \in currConfig.members
                                                     THEN Follower ELSE NotMember]
                    /\ log' = newLog
                    /\ Reply([mtype       |-> AppendEntriesResponse,
                              mterm       |-> currentTerm[i],
                              mresult     |-> Ok,
                              mmatchIndex |-> m.mprevLogIndex +
                                              Len(m.mentries),
                              msource     |-> i,
                              mdest       |-> j],
                              m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm, 
                                   auxVars>>
       
\* ACTION: HandleAppendEntriesResponse
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ state[i] = Leader
              \* state changes
              /\ \* Success! Advance the next and match indices
                 \/ /\ m.mresult = Ok
                    /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \* Entry was too far ahead, rewind the nextIndex
                 \/ /\ m.mresult = EntryMismatch 
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                         Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
                 \* The member is new, and needs a snapshot. This only happens if the
                 \* leader that initiated the reconfiguration lost leadership before it
                 \* could send the new member a snapshot.
                 \/ /\ m.mresult = NeedSnapshot 
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = PendingSnapshotRequest]
                    /\ UNCHANGED <<matchIndex>>
                 \* won't actually execute as UpdateTerm would be enabled
                 \* and the leader would abdicate.
                 \/ /\ m.mresult = StaleTerm  
                    /\ UNCHANGED <<nextIndex, matchIndex>>
              /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = FALSE]
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars, auxVars>>

\* ----------------------------------------------
\* RECONFIGURATION ------------------------------
                   
\* ACTION: AppendAddServerCommandToLog ----------------------------------
\* Leader i appends an AddServerCommand to the log.
AppendAddServerCommandToLog(i) ==
    \* enabling conditions
    /\ state[i] = Leader
    /\ addReconfigCtr < MaxAddReconfigs
    /\ ~HasPendingConfigCommand(i)
    /\ IF ~IncludeThesisBug
       THEN LeaderHasCommittedEntriesInCurrentTerm(i)
       ELSE TRUE
    /\ \E addMember \in Server :
        /\ addMember \notin config[i].members
        \* state changes
        /\ LET entry == [command |-> AddServerCommand,
                         term    |-> currentTerm[i],
                         value   |-> [new     |-> addMember,
                                      members |-> config[i].members \union {addMember}]]
               newLog == Append(log[i], entry)
           IN  /\ log' = [log EXCEPT ![i] = newLog]
               /\ config' = [config EXCEPT ![i] = ConfigFor(Len(newLog),
                                                            entry, 
                                                            commitIndex[i])]
               /\ addReconfigCtr' = addReconfigCtr + 1
               /\ nextIndex' = [nextIndex EXCEPT ![i] = 
                                    [s \in Server |-> IF s = entry.value.new
                                                      THEN PendingSnapshotRequest
                                                      ELSE @[s]]] 
        /\ UNCHANGED <<messages, currentTerm, votedFor, state, candidateVars,
                       matchIndex, pendingResponse, commitIndex, acked, electionCtr, 
                       restartCtr, valueCtr, removeReconfigCtr>>  

\* ACTION: AppendRemoveServerCommandToLog ----------------------------------
\* Leader i appends a RemoveServerCommand to its log.
AppendRemoveServerCommandToLog(i) ==
    \* enabling conditions
    /\ state[i] = Leader
    /\ removeReconfigCtr < MaxRemoveReconfigs
    /\ Cardinality(config[i].members) > MinClusterSize
    /\ IF ~IncludeThesisBug
       THEN LeaderHasCommittedEntriesInCurrentTerm(i)
       ELSE TRUE
    /\ ~HasPendingConfigCommand(i)
    /\ \E removeMember \in Server :
        /\ removeMember \in config[i].members
        \* state changes
        /\ LET entry == [command |-> RemoveServerCommand,
                         term    |-> currentTerm[i],
                         value   |-> [old     |-> removeMember,
                                      members |-> config[i].members \ {removeMember}]] 
               newLog == Append(log[i], entry)
           IN  /\ log' = [log EXCEPT ![i] = newLog]
               /\ config' = [config EXCEPT ![i] = ConfigFor(Len(newLog),
                                                            entry, 
                                                            commitIndex[i])]
               /\ removeReconfigCtr' = removeReconfigCtr + 1
        /\ UNCHANGED <<messages, currentTerm, votedFor, state, candidateVars,
                       nextIndex, matchIndex, pendingResponse, commitIndex, acked, electionCtr, 
                       restartCtr, valueCtr, addReconfigCtr>>  

\* ACTION: SendSnapshot ----------------------------------------
\* Leader i sends new member j a snapshot to bring them
\* up to date. Sending a snapshot makes catching up a new member
\* faster (smaller state space) - the Raft paper uses a non-voting
\* members strategy while the member is catching up.
\* Setting nextIndex to PendingSnapshotResponse disables this
\* action and prevents another snapshot from being sent.
SendSnapshot(i, j) ==
    \* enabling conditions
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in config[i].members
    /\ nextIndex[i][j] = PendingSnapshotRequest
    \* state changes
    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = PendingSnapshotResponse]
    /\ Send([mtype        |-> SnapshotRequest,
             mterm        |-> currentTerm[i],
             mlog         |-> log[i],
             mcommitIndex |-> commitIndex[i],
             mmembers     |-> config[i].members,
             msource      |-> i,
             mdest        |-> j])
    /\ UNCHANGED <<serverVars, matchIndex, pendingResponse,
                   candidateVars, matchIndex, logVars, auxVars>>

\* ACTION: AcceptSnapshot ----------------------------------------
\* A new member receives a snapshot
HandleSnapshotRequest ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, SnapshotRequest, EqualTerm)
        /\ LET i           == m.mdest
               j           == m.msource
               configEntry == MostRecentReconfigEntry(m.mlog)
           IN 
              /\ state[i] = Follower
              \* state changes
              /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
              /\ log'         = [log EXCEPT ![i] = m.mlog]
              /\ config' = [config EXCEPT ![i] = ConfigFor(configEntry.index,
                                                           configEntry.entry,
                                                           m.mcommitIndex)]
              /\ Reply([mtype       |-> SnapshotResponse,
                        mterm       |-> currentTerm[i],
                        msuccess    |-> TRUE,
                        mmatchIndex |-> Len(m.mlog),
                        msource     |-> i,
                        mdest       |-> j], m)
                /\ UNCHANGED <<candidateVars, leaderVars, state, votedFor, currentTerm, 
                               auxVars>>
                               
\* ACTION: HandleSnapshotResponse
\* Server i receives a Snapshot response from server j with
\* m.mterm = currentTerm[i].
HandleSnapshotResponse ==
    \* enabling conditions
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, SnapshotResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ nextIndex[i][j] = PendingSnapshotResponse
              \* state changes
              /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
              /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
              /\ Discard(m)
              /\ UNCHANGED <<pendingResponse, serverVars, candidateVars, logVars, auxVars>>                               

----
\* Network state transitions

\* The network duplicates a message
\* There is no state-space control for this action, it causes
\* infinite state space
DuplicateMessage(m) ==
    /\ Duplicate(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* The network drops a message
\* In reality is not required unless you use weak fairness of Next
\* as the specification would not force any server to receive a message, so we
\* would already get this for free.
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

----
\* Defines how the variables may transition.
Next == 
        \/ \E i \in Server : Restart(i)
        \/ UpdateTerm
        \* elections
        \/ \E i \in Server : RequestVote(i)
        \/ \E i \in Server : BecomeLeader(i)
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \* replication
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ RejectAppendEntriesRequest
        \/ AcceptAppendEntriesRequest
        \/ HandleAppendEntriesResponse
        \* reconfiguration
        \/ \E i \in Server : AppendAddServerCommandToLog(i)
        \/ \E i \in Server : AppendRemoveServerCommandToLog(i)
        \/ \E i,j \in Server : SendSnapshot(i, j)
        \/ HandleSnapshotRequest
        \/ HandleSnapshotResponse
        \* uncomment to see invariant violations during reconfigurations
\*        \/ \E i \in Server : ResetWithSameIdentity(i)
        
\*        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
NoStuttering ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars

LivenessSpec == Init /\ [][Next]_vars /\ NoStuttering

----
\* LIVENESS   -------------------------

\* Liveness ReconfigurationCompletes -----------
\* Ensure that once a leader appends a reconfig command
\* to its log and there are no subsequent elections, then
\* eventually all members of the new configuration will
\* switch to it.
\*
\* NOTE! Only use this temporal property with MaxElections = 0 as
\* an election can cause a reconfiguration to be abandoned
ReconfigurationCompletes ==
    \* given that a reconfig command has been added to the log
    \* of a leader
    (\E i \in Server :
         /\ state[i] = Leader
         /\ \E index \in DOMAIN log[i] :
            IsConfigCommand(log[i], index))
            ~>
    \* then all members of the new configuration eventually receive it
    (\E i \in Server :
         /\ state[i] = Leader
         /\ \E index \in DOMAIN log[i] :
            /\ IsConfigCommand(log[i], index)
            /\ \A j \in log[i][index].value.members :
                /\ index \in DOMAIN log[j]
                /\ log[i][index] = log[j][index])

\* INVARIANTS -------------------------

MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
    THEN commitIndex[s1]
    ELSE commitIndex[s2]

\* INV: NoLogDivergence
\* The log index is consistent across all servers (on those
\* servers whose commitIndex is equal or higher than the index).
NoLogDivergence ==
    \A s1, s2 \in Server :
        IF s1 = s2
        THEN TRUE
        ELSE
            LET lowestCommonCI == MinCommitIndex(s1, s2)
            IN IF lowestCommonCI > 0
               THEN \A index \in 1..lowestCommonCI : log[s1][index] = log[s2][index]
               ELSE TRUE

\* INV: MaxOneReconfigurationAtATime
\* The Raft reconfiguration algorithm is only
\* safe if there is one reconfiguration operation in-progress
\* at a time.
MaxOneReconfigurationAtATime ==
    ~\E i \in Server :
        /\ state[i] = Leader
        /\ \E ind1, ind2 \in DOMAIN log[i] :
            /\ ind1 # ind2
            /\ IsConfigCommand(log[i], ind1)
            /\ IsConfigCommand(log[i], ind2)
            /\ commitIndex[i] < ind1
            /\ commitIndex[i] < ind2

\* INV: Used in debugging
TestInv ==
    TRUE

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
                    /\ currentTerm[l] > currentTerm[i]
                \* and that is missing the value
                /\ ~\E index \in DOMAIN log[i] :
                    log[i][index].value = v
        ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET config[i].members :
               /\ Cardinality(quorum) = (Cardinality(config[i].members) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

===============================================================================

\* Changelog:
\*
