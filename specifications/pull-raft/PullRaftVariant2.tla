--------------------------------- MODULE PullRaftVariant2 ---------------------------------
(* NOTES 
Author: Jack Vanlightly
This specification is based on (with heavy modification) the original Raft specification 
by Diego Ongaro which can be found here: https://github.com/ongardie/raft.tla 

This is a model checking optimized fork of original spec.

This variant differs in that the leader does not push changes
to followers, but that followers pull changes from the leader.

The difference between this variant and PullRaft is that followers
don't immediately start trying to pull from the server they voted for.
In this version the servers wait for a LeaderNotify request to confirm
who the leader is. If the follower voted for the leader then the
leader knows the last log entry of the follower and whether the follower
has a divergent log that must be truncated - so the leader includes
the last common entry in the LeaderNotify request. 

For those followers that did not vote for the leader, it does not know
their last log entry and so passes a Nil last common entry. For these
followers, they may have a divergent log and when they make their
first PullEntries request the leader will reject it, and include
the last common entry its its response, which allows the follower to
truncate its log and resume pulling from a valid entry.

*)

EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

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
          PullEntriesRequest, PullEntriesResponse,
          LeaderNotifyRequest

\* Used for filtering messages under different circumstance
CONSTANTS EqualTerm, LessOrEqualTerm

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
\* The server's belief of who the leader is
VARIABLE leader
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, leader, votedFor>>

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
\* The last log entry of each server that has voted for the candidate.
VARIABLE votesLastEntry

candidateVars == <<votesGranted, votesLastEntry>>

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex

leaderVars == <<matchIndex>>

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
    /\ m.mtype = mtype
    /\ \/ /\ term_match = EqualTerm
          /\ m.mterm = currentTerm[m.mdest]
       \/ /\ term_match = LessOrEqualTerm
          /\ m.mterm <= currentTerm[m.mdest]

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* TRUE if the log of a server is beyond the last common entry 
NeedsTruncation(i, m) ==
   /\ m.mlastCommonEntry # Nil
   /\ Len(log[i]) >= m.mlastCommonEntry.index

\* truncates a server log to the last common entry index
TruncateLog(i, m) ==
    IF m.mlastCommonEntry.index = 0
    THEN <<>>
    ELSE [index \in 1..m.mlastCommonEntry.index |-> log[i][index]]

\* TRUE if the last entry of the follower is consistent
\* with the log of the leader
ValidPullPosition(i, m) ==
    \/ m.mlastLogIndex = 0
    \/ /\ m.mlastLogIndex > 0
       /\ m.mlastLogIndex <= Len(log[i])
       /\ m.mlastLogTerm = log[i][m.mlastLogIndex].term

\* Compares two entries, with term taking precedence. 
\* Index only matters when both have the same term.
\* When entry1 > entry2 then 1
\* When entry1 = entry2 then 0
\* When entry1 < entry2 then 1
CompareEntries(index1, term1, index2, term2) ==
    CASE term1 > term2 -> 1
      [] term1 = term2 /\ index1 > index2 -> 1
      [] term1 = term2 /\ index1 = index2 -> 0
      [] OTHER -> -1

\* the highest entry in the leader's log that is at or
\* below the last entry of the follower.
LastCommonEntry(i, lastIndex, lastTerm) ==
    CASE log[i] = <<>> -> 
            [index |-> 0, term |-> 0]
      [] ~\E index \in DOMAIN log[i] :
            CompareEntries(index, log[i][index].term, 
                           lastIndex, lastTerm) <= 0 -> 
            [index |-> 0, term |-> 0]
      [] OTHER ->
            LET index == CHOOSE index \in DOMAIN log[i] :
                            /\ CompareEntries(index, log[i][index].term, 
                                              lastIndex, lastTerm) <= 0
                            /\ ~\E index2 \in DOMAIN log[i] :
                                /\ CompareEntries(index2, log[i][index2].term, 
                                                  lastIndex, lastTerm) <= 0
                                /\ index2 > index
            IN [index |-> index, term |-> log[i][index].term]

----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
                  /\ leader      = [i \in Server |-> Nil]
InitCandidateVars == /\ votesGranted   = [i \in Server |-> {}]
                     /\ votesLastEntry = [i \in Server |-> [j \in Server |-> Nil]]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
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
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ leader'         = [leader EXCEPT ![i] = Nil]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ votesLastEntry' = [votesLastEntry EXCEPT ![i] = [j \in Server |-> Nil]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ restartCtr'     = restartCtr + 1
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, acked, electionCtr>>

\* ACTION: UpdateTerm
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm ==
    \E m \in DOMAIN messages :
        /\ m.mterm > currentTerm[m.mdest]
        /\ currentTerm' = [currentTerm EXCEPT ![m.mdest] = m.mterm]
        /\ state'       = [state       EXCEPT ![m.mdest] = Follower]
        /\ votedFor'    = [votedFor    EXCEPT ![m.mdest] = Nil]
        /\ leader'      = [leader EXCEPT ![m.mdest] = Nil]
        \* messages is unchanged so m can be processed further.
        /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>    

\* ACTION: RequestVote -----------------------------------------------
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
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ leader' = [leader EXCEPT ![i] = Nil]
    /\ electionCtr' = electionCtr + 1
    /\ SendMultiple(
           {[mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i] + 1,
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<acked, leaderVars, votesLastEntry, logVars, restartCtr>>

\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* If the last entry of i is <= to the last entry of j and
\* i has not already voted for a different server then i will grant
\* its vote to j. Server i includes the last log entry in its vote.
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
               /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ ~grant /\ UNCHANGED votedFor
               /\ Reply([mtype         |-> RequestVoteResponse,
                         mterm         |-> currentTerm[i],
                         mvoteGranted  |-> grant,
                         mlastLogIndex |-> Len(log[i]),
                         mlastLogTerm  |-> LastTerm(log[i]),
                         msource       |-> i,
                         mdest         |-> j],
                         m)
               /\ UNCHANGED <<state, currentTerm, leader, candidateVars, leaderVars, 
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
                    /\ votesLastEntry' = [votesLastEntry EXCEPT ![i][j] = 
                                                [index |-> m.mlastLogIndex,
                                                 term  |-> m.mlastLogTerm]]
                 \/ /\ ~m.mvoteGranted
                    /\ UNCHANGED <<votesGranted, votesLastEntry>>
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, 
                             auxVars>>               

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
\* Sends out a notification to the whole cluster, except itself,
\* that it is the leader and for those servers for which
\* it knows the last entry, it includes the last common
\* entry that they share so the follower can truncate its log if needed.
\* For any servers that it hasn't received a vote from, it sets the
\* last common entry to Nil - the last common entry will be shared 
\* upon the first pull by that follower.

BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'  = [state EXCEPT ![i] = Leader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                        [j \in Server |-> 0]]
    /\ SendMultiple(
          {[mtype            |-> LeaderNotifyRequest,
            mterm            |-> currentTerm[i],
            mlastCommonEntry |-> IF votesLastEntry[i][j] = Nil
                                 THEN Nil
                                 ELSE LastCommonEntry(i, 
                                            votesLastEntry[i][j].index,
                                            votesLastEntry[i][j].term),
            msource          |-> i,
            mdest            |-> j] : j \in Server \ {i}})
    /\ UNCHANGED <<currentTerm, votedFor, 
                   candidateVars, auxVars, logVars>>

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

\* ACTION: LearnOfLeader -------------------------------------------
\* A follower learns of a new leader and if the leader shared the 
\* last common entry, the follower may truncate its log to that point.
\* The follower can now start sending PullENtries requests to the leader.
LearnOfLeader ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, LeaderNotifyRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               index == m.mlastLogIndex
           IN /\ IF NeedsTruncation(i, m)
                 THEN log' = [log EXCEPT ![i] = TruncateLog(i, m)]
                 ELSE UNCHANGED log
              /\ leader' = [leader EXCEPT ![i] = j]
              /\ Discard(m)
        /\ UNCHANGED <<currentTerm, state, votedFor, candidateVars,
                       leaderVars, commitIndex, auxVars>>

\* ACTION: SendPullEntriesRequest ----------------------------------------
\* Follower i sends leader j a PullEntries request.
SendPullEntriesRequest(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ leader[i] = j
    /\ LET lastLogIndex == Len(log[i])
           lastLogTerm  == IF lastLogIndex > 0 
                           THEN log[i][lastLogIndex].term
                           ELSE 0
       IN 
          Send([mtype          |-> PullEntriesRequest,
                mterm          |-> currentTerm[i],
                mlastLogIndex  |-> lastLogIndex,
                mlastLogTerm   |-> lastLogTerm,
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, auxVars>>

\* ACTION: RejectPullEntriesRequest -------------------
\* The last entry of the follower is divergent from the 
\* log of the leader. The leader discovers the last common entry
\* they share and returns that in the response.
\* Note, this spec doesn't reject stale requests, it just drops them.
RejectPullEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PullEntriesRequest, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
               valid == ValidPullPosition(i, m)
           IN  /\ state[i] = Leader
               /\ \lnot valid
               /\ Reply([mtype            |-> PullEntriesResponse,
                         mterm            |-> currentTerm[i],
                         msuccess         |-> FALSE,
                         mlastCommonEntry |-> LastCommonEntry(i,
                                                    m.mlastLogIndex, 
                                                    m.mlastLogTerm),
                         msource          |-> i,
                         mdest            |-> j],
                         m)
               /\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, 
                              logVars, auxVars>>

\* ACTION: AcceptPullEntriesRequest ------------------
\* A leader only accepts a pull entries request once there 
\* are entries to respond with. In reality there is no such
\* restriction, it could respond with empty entries if the follower
\* is caught up - but it is inconvenient in this spec
\* as a follower can't send an identical PullEntries request again
\* (due to how the state space is constrained in this spec).
NewCommitIndex(i, iMatchIndex) ==
    LET Agree(index) == {i} \cup {k \in Server :
                            /\ iMatchIndex[k] >= index }
        \* The maximum indexes for which a quorum agrees
        agreeIndexes == {index \in 1..Len(log[i]) : 
                            Agree(index) \in Quorum}
    IN 
        IF /\ agreeIndexes # {}
           /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
        THEN
            Max(agreeIndexes)
        ELSE
            commitIndex[i]

AcceptPullEntriesRequest ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PullEntriesRequest, EqualTerm)
        /\ LET i       == m.mdest
               j       == m.msource
               valid   == ValidPullPosition(i, m)
               index   == m.mlastLogIndex + 1
           IN 
              /\ state[i] = Leader
              /\ valid
              /\ index <= Len(log[i])
              /\ LET newMatchIndex == [matchIndex[i] EXCEPT ![j] = m.mlastLogIndex]
                     newCommitIndex == NewCommitIndex(i, newMatchIndex)
                 IN
                    /\ matchIndex' = [matchIndex EXCEPT ![i] = newMatchIndex]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                    /\ acked' = [v \in Value |-> 
                                    IF acked[v] = FALSE
                                    THEN v \in { log[i][ind].value : ind \in commitIndex[i]+1..newCommitIndex }
                                    ELSE acked[v]]
                    /\ Reply([mtype           |-> PullEntriesResponse,
                              mterm           |-> currentTerm[i],
                              msuccess        |-> TRUE,
                              mentries        |-> << log[i][index] >>,
                              mcommitIndex    |-> Min({newCommitIndex, index}),
                              msource         |-> i,
                              mdest           |-> j], m)
                    /\ UNCHANGED <<candidateVars, votedFor, currentTerm, 
                                   log, state, leader, electionCtr, restartCtr>>
       
\* ACTION: HandleSuccessPullEntriesResponse
\* Server i receives an PullEntries response from server j with
\* m.mterm = currentTerm[i].
HandleSuccessPullEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PullEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ m.msuccess \* successful
              /\ commitIndex'  = [commitIndex  EXCEPT ![i] = m.mcommitIndex]
              /\ log' = [log EXCEPT ![i] = Append(@, m.mentries[1])]      
              /\ Discard(m)
              /\ UNCHANGED <<serverVars, candidateVars, matchIndex, auxVars>>

\* ACTION: HandleFailPullEntriesResponse
\* Server i receives an PullEntries response from server j with
\* m.mterm = currentTerm[i] that has failed. It truncates its log
\* to the last common entry so that it can send another request
\* to the leader from a valid pull position.

HandleFailPullEntriesResponse ==
    \E m \in DOMAIN messages :
        /\ ReceivableMessage(m, PullEntriesResponse, EqualTerm)
        /\ LET i     == m.mdest
               j     == m.msource
           IN
              /\ ~m.msuccess \* failed
              /\ log' = [log EXCEPT ![i] = TruncateLog(i, m)]      
              /\ Discard(m)
        /\ UNCHANGED <<serverVars, candidateVars, leaderVars, 
                       commitIndex, auxVars>>

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
        \/ HandleRequestVoteRequest
        \/ HandleRequestVoteResponse
        \/ \E i \in Server : BecomeLeader(i)
        \* leader actions
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ RejectPullEntriesRequest
        \/ AcceptPullEntriesRequest
        \* follower actions
        \/ LearnOfLeader
        \/ \E i,j \in Server : SendPullEntriesRequest(i, j)
        \/ HandleSuccessPullEntriesResponse
        \/ HandleFailPullEntriesResponse
        
\*        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
\*        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

----
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
