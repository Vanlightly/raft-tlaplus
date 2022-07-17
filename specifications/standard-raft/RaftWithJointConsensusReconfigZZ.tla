--------------------------------- MODULE RaftWithJointConsensusReconfig ---------------------------------
(* NOTES 
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

This is a model checking optimized fork of original spec.

- Summary of changes:
    - updated message helpers:
        - prevent resending the same message multiple times (unless explicity via the duplicate action)
        - can only receive a message that hasn't been delivered yet
    - optimized for model checking (reduction in state space)
        - removed history variables (using simple invariants instead)
        - decomposed "receive" into separate actions
        - compressed multi-step append entries request processing into one.
        - compressed timeout and requestvote into single action
        - server directly votes for itself in an election (it doesn't send itself a vote request)
    - fixed some bugs
        - adding the same value over and over again
        - allowing actions to remain enabled producing odd results
    - reconfiguration
        - adding nodes
        - removing nodes
    
Notes on action enablement.
 - Send is only enabled if the mesage has not been previously sent.
   This is leveraged to disable actions once executed, such as sending a specific 
   AppendEntrieRequest. It won't be sent again, so no need for extra variables to track that.

Notes on reconfiguration:
- fix issues of new member seeing all reconfigs by sending a snapshot first
*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

CONSTANTS InitClusterSize

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, NotMember

\* Commands
CONSTANTS AppendCommand,
          OldNewConfigCommand,
          NewConfigCommand

\* A reserved value.
CONSTANTS Nil

\* AppendEntries response codes
CONSTANTS Ok, StaleTerm, EntryMismatch, NeedSnapshot

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          SnapshotRequest, SnapshotResponse

\* Used for filtering messages under different circumstance
CONSTANTS EqualTerm, LessOrEqualTerm

\* Limiting state space by limiting the number of elections and restarts           
CONSTANTS MaxElections, MaxRestarts, MaxReconfigs, MaxValuesPerTerm
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
VARIABLE electionCtr, restartCtr, reconfigCtr, valueCtr
auxVars == <<acked, electionCtr, restartCtr, reconfigCtr, valueCtr>>
----
\* Per server variables (functions with domain Server).
\* The server's view of the cluster membership
VARIABLE members
\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
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
VARIABLE pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, members, serverVars, candidateVars, leaderVars, logVars,
          auxVars>>
view == <<messages, members, serverVars, candidateVars, leaderVars, logVars >>
symmServers == Permutations(Server)
symmValues == Permutations(Value)
----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(cluster) == {i \in SUBSET(cluster) : Cardinality(i) * 2 > Cardinality(cluster)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Add a message to the bag of messages.
Send(m) == 
    /\ m \notin DOMAIN messages
    /\ messages' = messages @@ (m :> 1)

SendMultiple(msgs) ==
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
    /\ response \notin DOMAIN messages \* response does not exist
    /\ messages' = [messages EXCEPT ![request] = @ - 1] @@ (response :> 1)

\* The message is of the type and has a matching term.
\* Messages with a higher term are handled by the
\* action UpdateTerm
ReceivableMessage(m, mtype, term_match) ==
    /\ messages[m] > 0
\*    /\ m.msource \in members[m.mdest]
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

IsConfigCommand(i, serverLog, index) ==
    serverLog[index].command \in {OldNewConfigCommand, 
                                  NewConfigCommand}

IsPendingNewConfig(i, index) ==
    /\ log[i][index].command = OldNewConfigCommand
    /\ commitIndex[i] >= index
    \* there isn't another more recent OldNewReconfigCommand
    /\ ~\E index2 \in DOMAIN log[i] :
        /\ log[i][index2].command = OldNewConfigCommand
        /\ index2 > index
    \* there isn't already a NewReconfigCommand
    /\ ~\E index2 \in DOMAIN log[i] :
        /\ log[i][index2].command = NewConfigCommand
        /\ index2 > index

\* A leader only allows one uncommitted reconfiguration command
\* at a time.
HasPendingConfigCommand(i) ==
    IF log[i] = <<>>
    THEN FALSE
    ELSE \E index \in DOMAIN log[i] :
        \* either there is an uncommitted OldNewConfigCommand
        \/ /\ log[i][index].command = OldNewConfigCommand
           /\ index > commitIndex[i]
        \* or there is a committed OldNewConfigCommand without a corresponding NewConfigCommand
        \/ /\ log[i][index].command = OldNewConfigCommand
           /\ index <= commitIndex[i]
           /\ IsPendingNewConfig(i, index)
        \* or there is an uncommitted NewConfigCommand
        \/ /\ log[i][index].command = NewConfigCommand
           /\ index > commitIndex[i]
        

\* If the updated log is empty then the members are included 
\* in the AppendEntries request (first entry includes members).
\* Else if there is a reconfiguration command then take the
\* most recent one and choose that member set.
\* Else keep the current member set.
UpdateMemberSet(i, m, newLog) ==
    IF Len(log[i]) = 0
    THEN m.mmembers
    ELSE 
        IF \E index \in DOMAIN newLog[i] : 
            IsConfigCommand(i, newLog[i], index)
        THEN LET index == CHOOSE index \in DOMAIN newLog[i] : 
                            /\ IsConfigCommand(i, newLog[i], index)
                            /\ ~\E index2 \in DOMAIN newLog[i] : 
                                /\ IsConfigCommand(i, newLog[i], index2)
                                /\ index2 > index
             IN newLog[i][index].value.members
        ELSE members[i]

PendingSnapshotRequest == -1
PendingSnapshotResponse == -2

----
\* Define initial values for all variables

InitServerVars(cluster) == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> IF i \in cluster
                                       THEN Follower
                                       ELSE NotMember]
    /\ votedFor    = [i \in Server |-> Nil]
    
InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex       = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex      = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingResponse = [i \in Server |-> [j \in Server |-> FALSE]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ reconfigCtr = 0
               /\ acked = [v \in Value |-> Nil]
               /\ valueCtr = [v \in 1..MaxElections+1 |-> 0]

Init == LET cluster == CHOOSE s \in SUBSET Server :
                            Cardinality(s) = InitClusterSize
        IN
            /\ messages = [m \in {} |-> 0]
            /\ members = [i \in Server |->
                            IF i \in cluster
                            THEN cluster
                            ELSE {}]
            /\ InitServerVars(cluster)
            /\ InitCandidateVars
            /\ InitLeaderVars
            /\ InitLogVars
            /\ InitAuxVars

----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    /\ restartCtr < MaxRestarts
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] = [j \in Server |-> FALSE]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr'      = restartCtr + 1
    /\ UNCHANGED <<messages, members, currentTerm, votedFor, log, 
                   acked, electionCtr, reconfigCtr, valueCtr>>

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ \/ state[m.mdest] = NotMember \* could be a newly added node
           \/ /\ state[m.mdest] # NotMember
              /\ m.msource \in members[m.mdest]
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
           \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<messages, members, candidateVars, leaderVars, logVars, auxVars>>
        
\* ----------------------------------------------
\* ELECTIONS ------------------------------------

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ electionCtr < MaxElections 
    /\ state[i] \in {Follower, Candidate}
    /\ i \in members[i]
    /\ state'        = [state EXCEPT ![i] = Candidate]
    /\ currentTerm'  = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor'     = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr'  = electionCtr + 1
    /\ SendMultiple(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in members[i] \ {i}})
    /\ UNCHANGED <<acked, members, leaderVars, logVars, restartCtr,
                   reconfigCtr, valueCtr>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest ==
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
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ Reply([mtype        |-> RequestVoteResponse,
                         mterm        |-> currentTerm[i],
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j],
                         m)
               /\ UNCHANGED <<members, state, currentTerm, candidateVars, leaderVars, 
                              logVars, auxVars>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        \* This tallies votes even when the current state is not Candidate, but
        \* they won't be looked at, so it doesn't matter.
        /\ ReceivableMessage(m, RequestVoteResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ \/ /\ m.mvoteGranted
                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted>>
              /\ Discard(m)
              /\ UNCHANGED <<members, serverVars, votedFor, leaderVars, logVars, 
                             auxVars>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum(members[i])
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] =
                                [j \in Server |-> FALSE]]
    /\ UNCHANGED <<messages, members, currentTerm, votedFor, candidateVars, 
                   auxVars, logVars>>

\* ----------------------------------------------
\* REPLICATION ----------------------------------

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ valueCtr[currentTerm[i]] < MaxValuesPerTerm
    /\ LET entry == [command |-> AppendCommand,
                     term    |-> currentTerm[i],
                     value   |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
           /\ valueCtr' = [valueCtr EXCEPT ![currentTerm[i]] = @ + 1]
    /\ UNCHANGED <<messages, members, serverVars, candidateVars,
                   leaderVars, commitIndex, electionCtr, 
                   restartCtr, reconfigCtr>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\*
\* For reconfiguration, we need to be able to tell new nodes who
\* the members of the cluster are
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in members[i]
    /\ nextIndex[i][j] >= 0 \* not pending a snapshot
    /\ pendingResponse[i][j] = FALSE
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
                  mmembers       |-> IF prevLogIndex = 0
                                     THEN members[i] ELSE Nil,
                  msource        |-> i,
                  mdest          |-> j])
    /\ UNCHANGED <<members, serverVars, candidateVars, 
                   nextIndex, matchIndex, logVars, auxVars>>

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* Note that we don't advance the commit index one at a time because
\* a new leader can only advance the commit index when it is able
\* to majority replicate an entry in the new term - so it may be 
\* forced to advance the commit index by multiple entries.
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
        /\ log[i][index].command = NewConfigCommand
        /\ i \notin log[i][index].value.members

AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           \* if the leader is not in the current membership due
           \* to an in-progress reconfiguration then it does not 
           \* include itself in the quorum
           Agree(index) == IF i \notin members[i]
                           THEN {k \in members[i] : matchIndex[i][k] >= index }
                           ELSE {i} \cup {k \in members[i] :
                                         /\ matchIndex[i][k] >= index }
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum(members[i])}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ acked' = MayBeAckClient(i, newCommitIndex)
          /\ IF IsRemovedFromCluster(i, newCommitIndex)
             THEN /\ state'          = [state EXCEPT ![i] = NotMember]
                  /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
                  /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
                  /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
                  /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
             ELSE /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                  /\ UNCHANGED <<state, votesGranted, nextIndex, matchIndex>>
    /\ UNCHANGED <<messages, currentTerm, members, votedFor, log, 
                   pendingResponse, electionCtr, restartCtr, reconfigCtr, valueCtr>>

\* ACTION: RejectAppendEntriesRequest -------------------
\* Either the term of the message is stale or the message
\* entry is too high (beyond the last log entry + 1)
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term

RejectAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
           IN LET rc == CASE m.mterm < currentTerm[i] -> StaleTerm
                          [] i \notin members[i] -> NeedSnapshot
                          [] /\ m.mterm = currentTerm[i]
                             /\ state[i] = Follower
                             /\ \lnot logOk -> EntryMismatch
                          [] OTHER -> Ok
              IN
                   /\ rc # Ok
                   /\ Reply([mtype       |-> AppendEntriesResponse,
                             mterm       |-> currentTerm[i],
                             mresult     |-> rc,
                             mmatchIndex |-> 0,
                             msource     |-> i,
                             mdest       |-> j],
                             m)
                   /\ UNCHANGED <<members, state, candidateVars, leaderVars, serverVars, 
                                  logVars, auxVars>>

\* ACTION: AcceptAppendEntriesRequest ------------------
\* The original spec had to three sub actions, this version is compressed.
\* In one step it can:
\* - truncate the log
\* - append an entry to the log
\* - respond to the leader         
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
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               logOk == LogOk(i, m)
               index == m.mprevLogIndex + 1
           IN 
              /\ state[i] \in { Follower, Candidate }
              /\ logOk
              /\ i \in members[i] \* must know its a member, else it needs a snapshot
              /\ LET newLog      == IF CanAppend(m, i)
                                    THEN [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                                    ELSE IF NeedsTruncation(m, i , index)
                                         THEN [log EXCEPT ![i] = Append(TruncateLog(m, i), m.mentries[1])]
                                         ELSE log
                     currMembers == UpdateMemberSet(i, m, newLog)
                 IN
                    /\ members' = [members EXCEPT ![i] = currMembers]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                    /\ state' = [state EXCEPT ![i] = IF i \in currMembers
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
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ state[i] = Leader
              /\ \/ /\ m.mresult = Ok
                    /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                 \/ /\ m.mresult = EntryMismatch
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                         Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED <<matchIndex>>
                 \/ /\ m.mresult = NeedSnapshot
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = PendingSnapshotRequest]
                    /\ UNCHANGED <<matchIndex>>
                 \/ /\ m.mresult = StaleTerm
                    /\ UNCHANGED <<nextIndex, matchIndex>>
              /\ pendingResponse' = [pendingResponse EXCEPT ![i][j] = FALSE]
              /\ Discard(m)
              /\ UNCHANGED <<members, serverVars, candidateVars, logVars, auxVars>>

\* ----------------------------------------------
\* RECONFIGURATION ------------------------------
                   
\* ACTION: AppendOldNewReconfigToLog ----------------------------------
\* Leader i appends an OldNewConfigCommand to the log.
\* This reconfiguration is a simple 1-for-1 server replacement
\* reconfiguration.
\* TODO: make an arbitrary reconfiguration
\* If the reconfiguration includes a new member, then nextIndex
\* is updated to indicate that it must be sent a snapshot.
AppendOldNewConfigToLog(i, j, k) ==
    /\ state[i] = Leader
    /\ reconfigCtr < MaxReconfigs
    /\ j \notin members[i]
    /\ k \in members[i]
    /\ ~HasPendingConfigCommand(i)
    /\ LET entry == [command |-> OldNewConfigCommand,
                     term    |-> currentTerm[i],
                     value   |-> [id      |-> reconfigCtr,
                                  old     |-> members[i],
                                  new     |-> (members[i] \ {k}) \union {j},
                                  members |-> members[i] \union {j}]]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ members' = [members EXCEPT ![i] = entry.value.members]         
           /\ reconfigCtr' = reconfigCtr + 1
           /\ nextIndex' = [nextIndex EXCEPT ![i] = 
                                [s \in Server |-> IF /\ s \in entry.value.new
                                                     /\ s \notin entry.value.old
                                                  THEN PendingSnapshotRequest
                                                  ELSE @[s]]] 
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   matchIndex, pendingResponse, commitIndex, acked, electionCtr, 
                   restartCtr, valueCtr>>  

\* ACTION: AppendNewConfigToLog ----------------------------------
\* Leader i appends a NewConfigCommand to its log now that
\* the OldNewConfigCommand has been committed
AppendNewConfigToLog(i) ==
    /\ state[i] = Leader
    /\ \E index \in DOMAIN log[i] :
        /\ IsPendingNewConfig(i, index)
        /\ LET oldNewComm == log[i][index]
               entry      == [id      |-> oldNewComm.value.id,
                              command |-> NewConfigCommand,
                              term    |-> currentTerm[i],
                              value   |-> [members |-> oldNewComm.value.new]]
               newLog     == Append(log[i], entry)
           IN  /\ log'     = [log EXCEPT ![i] = newLog]
               /\ members' = [members EXCEPT ![i] = entry.value.members]         
        /\ UNCHANGED <<messages, serverVars, candidateVars,
                       leaderVars, commitIndex, auxVars>>

\* ACTION: SendSnapshot ----------------------------------------
\* Leader i sends new member j a snapshot to bring them
\* up to date. Sending a snapshot avoids the issue of a
\* new member applying all prior reconfigurations as it
\* would if it just received log entries via AppendEntries
\* requests.
\* Setting nextIndex to PendingSnapshotResponse disables this
\* action and prevents another snapshot from being sent.
SendSnapshot(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ j \in members[i]
    /\ nextIndex[i][j] = PendingSnapshotRequest
    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = PendingSnapshotResponse]
    /\ Send([mtype        |-> SnapshotRequest,
             mterm        |-> currentTerm[i],
             mlog         |-> log[i],
             mcommitIndex |-> commitIndex[i],
             mmembers     |-> members[i],
             msource      |-> i,
             mdest        |-> j])
    /\ UNCHANGED <<members, serverVars, matchIndex, pendingResponse,
                   candidateVars, matchIndex, logVars, auxVars>>

\* ACTION: AcceptSnapshot ----------------------------------------
\* A new member receives a snapshot
HandleSnapshotRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, SnapshotRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN 
              /\ state[i] = Follower
              /\ members'     = [members EXCEPT ![i] = m.mmembers]
              /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
              /\ log'         = [log EXCEPT ![i] = m.mlog]
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
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, SnapshotResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ nextIndex[i][j] = PendingSnapshotResponse
              /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
              /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
              /\ Discard(m)
              /\ UNCHANGED <<members, pendingResponse, serverVars, candidateVars, logVars, auxVars>>                               

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
        \/ \E i,j,k \in Server : AppendOldNewConfigToLog(i, j, k)
        \/ \E i \in Server : AppendNewConfigToLog(i)
        \/ \E i,j \in Server : SendSnapshot(i, j)
        \/ HandleSnapshotRequest
        \/ HandleSnapshotResponse
        
\*        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
NoStuttering ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ NoStuttering

----
\* LIVENESS   -------------------------
ReconfigurationCompletes ==
    (\E i \in Server :
        \E index \in DOMAIN log[i] :
            /\ log[i][index].command = OldNewConfigCommand
            /\ log[i][index].term = 1
            /\ commitIndex[i] >= index)
        ~>
    (\E i \in Server :
        \E index \in DOMAIN log[i] :
            /\ log[i][index].command = OldNewConfigCommand
            /\ log[i][index].term = 1
            /\ commitIndex[i] >= index
            /\ \A s \in log[i][index].value.new :
                /\ s \in members[s]
                /\ state[s] \in {Leader, Follower, Candidate})
\*            /\ \A s \in log[i][index].value.members \ log[i][index].value.new :
\*                /\ s \notin members[s]
\*                /\ state[s] = NotMember)
    
\*    (\E i \in Server :
\*        \E index \in DOMAIN log[i] :
\*            /\ log[i][index].command = NewConfigCommand
\*            /\ commitIndex[i] >= index
\*            /\ \E ind \in DOMAIN log[i] :
\*                /\ log[i][ind].command = OldNewConfigCommand
\*                /\ log[i][index].value.id = log[i][ind].value.id
\*                /\ commitIndex[i] >= index)
    

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

\* INV: Used in debugging
MaxOneReconfigurationAtATime ==
    \A command \in {OldNewConfigCommand, NewConfigCommand} :
        \A i \in Server :
            \/ Len(log[i]) <= 1
            \* there is at least 2 entries in the log
            \/ /\ Len(log[i]) > 1
               \* there are not two entries that are both the same reconfig command type
               /\ ~\E ind1, ind2 \in DOMAIN log[i] :
                    /\ ind1 < ind2
                    /\ log[i][ind1].command = command
                    /\ log[i][ind2].command = command
                       \* and that are adjacent (illegal state)
                    /\ \/ ind2 - ind1 = 1
                       \* or are not adjacent and don't have a NewConfigCommand 
                       \* in between them (illegal state) 
                       \/ /\ ind2 - ind1 > 1 
                          /\ ~\E ind3 \in DOMAIN log[i] :
                                /\ ind3 > ind1
                                /\ ind3 < ind2
                                /\ log[i][ind3].command = 
                                    IF command = OldNewConfigCommand
                                    THEN NewConfigCommand ELSE OldNewConfigCommand

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
           /\ \E quorum \in SUBSET members[i] :
               /\ Cardinality(quorum) = (Cardinality(members[i]) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

===============================================================================

\* Changelog:
\*