--------------------------------- MODULE Raft ---------------------------------
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
        - compressed multi-step append_entries_req processing into one.
        - compressed timeout and requestvote into single action
        - server directly votes for itself in an election (it doesn't send itself a vote request)
    - fixed some bugs
        - adding the same value over and over again
        - allowing actions to remain enabled producing odd results
    
Notes on action enablement.
 - Send is only enabled if the mesage has not been previously sent.
   This is leveraged to disable actions once executed, such as sending a specific 
   AppendEntrieRequest. It won't be sent again, so no need for extra variables to track that. 
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* Used for filtering messages under different circumstance
CONSTANTS EqualTerm, LessOrEqualTerm, AnyTerm

\* Limiting state space by limiting the number of elections and restarts           
CONSTANTS MaxElections, MaxRestarts
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
VARIABLE electionCtr, restartCtr
auxVars == <<acked, electionCtr, restartCtr>>
----
\* Per server variables (functions with domain Server).

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
\* Tracks which peers a leader is waiting on a response for.
\* Used for one-at-a-time AppendEntries RPCs. Not really required but
\* permitting out of order requests explodes the state space.
VARIABLE pendingResponse
leaderVars == <<nextIndex, matchIndex, pendingResponse>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars,
          auxVars>>
view == <<messages, serverVars, candidateVars, leaderVars, logVars >>
symmServers == Permutations(Server)
symmValues == Permutations(Value)
----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

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

\* The message is of the type and has a matching term.
\* Messages with a higher term are handled by the
\* action UpdateTerm
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

CurrentStateVars(i) ==
    [term      |-> currentTerm[i],
     state     |-> state[i],
     votedFor  |-> votedFor[i],
     isNewTerm |-> FALSE]

MayBeUpdateTerm(i, m) ==
    IF m.mterm > currentTerm[m.mdest]
    THEN [term      |-> m.mterm,
          state     |-> Follower,
          votedFor  |-> Nil,
          isNewTerm |-> TRUE]
    ELSE CurrentStateVars(i)

MaybeUpdateServerState(i, state0) ==
    IF state0.term # currentTerm[i]
    THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = state0.term]
         /\ state'       = [state       EXCEPT ![i] = state0.state]
         /\ votedFor'    = [votedFor    EXCEPT ![i] = state0.votedFor]
    ELSE UNCHANGED << currentTerm, state, votedFor >>
    
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
MaybeAdvanceCommitIndex(i, state0, iMatchIndex, iLog) ==
    /\ state0.state = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         /\ iMatchIndex[k] >= index }
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(iLog) : 
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ iLog[Max(agreeIndexes)].term = state0.term
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN 
          IF commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          THEN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
               /\ acked' = [v \in Value |-> 
                                IF acked[v] = FALSE
                                THEN v \in { iLog[index].value : index \in commitIndex[i]+1..newCommitIndex }
                                ELSE acked[v]]
          ELSE UNCHANGED << commitIndex, acked >>
                            
----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingResponse = [i \in Server |-> [j \in Server |-> FALSE]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitAuxVars == /\ electionCtr = 0
               /\ restartCtr = 0
               /\ acked = [v \in Value |-> Nil]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitServerVars
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
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, acked, electionCtr>>

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ electionCtr < MaxElections 
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ electionCtr' = electionCtr + 1
    /\ SendMultipleOnce(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<acked, leaderVars, logVars, restartCtr>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN 
          /\ MaybeAdvanceCommitIndex(i, CurrentStateVars(i), 
                                     matchIndex[i], log[i])
          /\ Send([mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                   mprevLogIndex  |-> prevLogIndex,
                   mprevLogTerm   |-> prevLogTerm,
                   mentries       |-> entries,
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ pendingResponse' = [pendingResponse EXCEPT ![i] =
                                [j \in Server |-> FALSE]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, 
                   auxVars, logVars>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ acked[v] = Nil \* prevent submitting the same value repeatedly
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
           /\ acked' = [acked EXCEPT ![v] = FALSE]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, electionCtr, restartCtr>>

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
\*UpdateTerm ==
\*    \E m \in DOMAIN messages :
\*        /\ m.mterm > currentTerm[m.mdest]
\*        /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
\*        /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
\*        /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
\*           \* messages is unchanged so m can be processed further.
\*        /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, RequestVoteRequest, AnyTerm)
        /\ LET i      == m.mdest
               j      == m.msource
               state0 == MayBeUpdateTerm(i, m)
               logOk  == \/ m.mlastLogTerm > LastTerm(log[i])
                         \/ /\ m.mlastLogTerm = LastTerm(log[i])
                            /\ m.mlastLogIndex >= Len(log[i])
               grant  == /\ m.mterm = state0.term
                         /\ logOk
                         /\ votedFor[i] \in {Nil, j}
            IN /\ m.mterm <= state0.term
               /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ MaybeUpdateServerState(i, state0)
               /\ Reply([mtype        |-> RequestVoteResponse,
                         mterm        |-> state0.term,
                         mvoteGranted |-> grant,
                         msource      |-> i,
                         mdest        |-> j],
                         m)
               /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                              logVars, auxVars>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse ==
    \E m \in DOMAIN messages :
        \* This tallies votes even when the current state is not Candidate, but
        \* they won't be looked at, so it doesn't matter.
        /\ ReceivableMessage(m, RequestVoteResponse, AnyTerm)
        /\ LET i      == m.mdest
               j      == m.msource
               state0 == MayBeUpdateTerm(i, m)
           IN
              /\ IF /\ state0.isNewTerm = FALSE
                    /\ m.mvoteGranted
                 THEN /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                              votesGranted[i] \cup {j}]
                 ELSE /\ ~m.mvoteGranted
                      /\ UNCHANGED <<votesGranted>>
              /\ MaybeUpdateServerState(i, state0)
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, 
                             auxVars>>

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
        /\ LET i      == m.mdest
               j      == m.msource
               state0 == MayBeUpdateTerm(i, m)
               logOk  == LogOk(i, m)
           IN  /\ \/ m.mterm < state0.term
                  \/ /\ m.mterm = state0.term
                     /\ state0.state = Follower
                     /\ \lnot logOk
               /\ MaybeUpdateServerState(i, state0)
               /\ Reply([mtype           |-> AppendEntriesResponse,
                         mterm           |-> state0.term,
                         msuccess        |-> FALSE,
                         mmatchIndex     |-> 0,
                         msource         |-> i,
                         mdest           |-> j],
                         m)
               /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, 
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

TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesRequest, EqualTerm)
        /\ LET i      == m.mdest
               j      == m.msource
               state0 == MayBeUpdateTerm(i, m)
               logOk  == LogOk(i, m)
               index  == m.mprevLogIndex + 1
           IN 
              /\ state0.state \in { Follower, Candidate }
              /\ logOk
              /\ LET new_log == IF CanAppend(m, i)
                                THEN [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                                ELSE IF NeedsTruncation(m, i , index)
                                     THEN [log EXCEPT ![i] = Append(TruncateLog(m, i), m.mentries[1])]
                                     ELSE log 
                 IN
                    /\ state' = [state EXCEPT ![i] = Follower]
                    /\ IF state0.isNewTerm
                       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = state0.term]
                            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                       ELSE UNCHANGED << currentTerm, votedFor >>
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                    /\ log' = new_log
                    /\ Reply([mtype           |-> AppendEntriesResponse,
                              mterm           |-> currentTerm[i],
                              msuccess        |-> TRUE,
                              mmatchIndex     |-> m.mprevLogIndex +
                                                    Len(m.mentries),
                              msource         |-> i,
                              mdest           |-> j],
                              m)
                    /\ UNCHANGED <<candidateVars, leaderVars, votedFor, currentTerm, 
                                   auxVars>>
       
\* ACTION: HandleAppendEntriesResponse
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, AppendEntriesResponse, EqualTerm)
        /\ LET i      == m.mdest
               j      == m.msource
               state0 == MayBeUpdateTerm(i, m)
           IN
              /\ IF state0.isNewTerm = FALSE
                 THEN \/ /\ m.msuccess \* successful
                         /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                         /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                         /\ MaybeAdvanceCommitIndex(i, state0,  
                                     matchIndex'[i], log[i])
                      \/ /\ \lnot m.msuccess \* not successful
                         /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                            Max({nextIndex[i][j] - 1, 1})]
                         /\ UNCHANGED <<matchIndex>>
                 ELSE UNCHANGED << nextIndex, matchIndex >>
              /\ MaybeUpdateServerState(i, state0)
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, logVars, auxVars>>

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
        \/ \E i \in Server : RequestVote(i)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
\*        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
\*        \/ UpdateTerm
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \/ RejectAppendEntriesRequest
        \/ AcceptAppendEntriesRequest
        \/ HandleAppendEntriesResponse
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

\* Liveness: AllEntriesReplicated
\* Only use this when MaxElections = 1 and in odd-sized clusters
\* given that the one permitted election may not succeed
AllEntriesReplicated ==
    []<>(\A v \in Value : 
            \A s \in Server : 
                \E index \in DOMAIN log[s] :
                    log[s][index].value = v) 


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
            LET lowest_common_ci == MinCommitIndex(s1, s2)
            IN IF lowest_common_ci > 0
               THEN \A index \in 1..lowest_common_ci : log[s1][index] = log[s2][index]
               ELSE TRUE

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
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET Server :
               /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation