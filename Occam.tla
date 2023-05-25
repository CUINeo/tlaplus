------------------------------- MODULE Occam --------------------------------
(***************************************************************************)
(* This module specifies the commit protocol in geo-distributed databases, *)
(* which is a combination of Two-Phase Commit and Paxos.                   *)
(* In this specification, we ignore the prepare messages sent by the       *)
(* coordinator, shard leaders spontaneously choose to prepare or abort.    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANT
    DS,             \* The set of data servers
    Shards,         \* The set of shards
    Leaders,        \* The set of leaders
    numShards,      \* The number of shards
    Coordinator     \* The ID of the coordinator

(***************************************************************************)
(* We assume the following properties of the declared constants.           *)
(***************************************************************************)
ASSUME
    /\ Coordinator \in DS
    /\ Coordinator \in {Leaders[l] : l \in 1..numShards}    \* Only leaders can act as the coordinator
    /\ numShards = Len(Shards)
    /\ numShards = Len(Leaders)
    /\ DS = UNION {Shards[i] : i \in 1..numShards}          \* Union of all shards is the full set
    /\ \A s \in 1..numShards : Leaders[s] \in Shards[s]     \* Leaders are in corresponding shards

Messages ==
    (***********************************************************************)
    (* The set of all possible messages                                    *)
    (***********************************************************************)
    [type : {"prepared", "aborted", "ack"}, src : 1..numShards] \cup
    [type : {"prepareAccepted"}, src : DS] \cup [type : {"commit", "abort"}] \cup
    [type : {"phase2b"}, src : DS, dst : DS, desc : {"leaderDecision", "coordDecision"}] \cup
    [type : {"phase2a"}, src : DS, desc : {"leaderPrepared", "leaderAborted", "committed", "aborted"}]
-----------------------------------------------------------------------------
VARIABLES
    dsState,                    \* dsState[ds] is the state of data server ds
    coordState,                 \* The state of the coordinator
    coordPrepared,              \* The set of shards that are prepared
    coordDecisionReplicated,    \* The set of replicas to which the coordinator has replicated its decision
    msgs                        \* The message pool
    
vars == <<dsState, coordState, coordPrepared, coordDecisionReplicated, msgs>>

TypeOK ==
    /\ dsState \in [DS -> [Shard : 1..numShards,
                           Role : {"Coordinator", "Leader", "Follower"},
                           LeaderDecisionReplicated : SUBSET DS,
                           CoordDecisionReplicated : SUBSET DS,
                           Accepted : SUBSET DS,
                                    \* The set of followers that have accepted leaders' prepare decision
                           State : {"working", "prepared", "committed", "aborted"}]]
    /\ coordState \in {"init", "commit", "abort"}
    /\ coordPrepared \subseteq {i : i \in 1..numShards}
    /\ coordDecisionReplicated \subseteq DS
    /\ msgs \subseteq Messages

Init ==
    /\ dsState = [ds \in DS |-> [Shard |-> CHOOSE s \in 1..numShards : ds \in Shards[s],
                  Role |-> CASE ds = Coordinator                       -> "Coordinator"
                           [] ds \in {Leaders[l] : l \in 1..numShards} -> "Leader"
                           [] OTHER                                    -> "Follower",
                  LeaderDecisionReplicated |-> {},
                  CoordDecisionReplicated |-> {},
                  Accepted |-> {},
                  State |-> "working"]]
    /\ coordState              = "init"
    /\ coordPrepared           = {}
    /\ coordDecisionReplicated = {}
    /\ msgs                    = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                THE ACTIONS                              *)
(***************************************************************************)
send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            COORDINATOR ACTIONS                          *)
(***************************************************************************)
CoordRcvLeaderPrepare(s) ==
    /\ coordState = "init"
    /\ [type |-> "prepared", src |-> s] \in msgs
    /\ coordPrepared' = coordPrepared \cup {s}
    /\ UNCHANGED <<dsState, coordState, coordDecisionReplicated, msgs>>

CoordRcvLeaderAbort(s) ==
    /\ coordState = "init"
    /\ [type |-> "aborted", src |-> s] \in msgs
    /\ coordState' = "abort"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "aborted"]
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated, msgs>>

CoordRcvFollowerAccept(ds) ==
    /\ coordState = "init"
    /\ [type |-> "prepareAccepted", src |-> ds] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![Coordinator].Accepted = dsState[Coordinator].Accepted \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

CoordCommit ==
    /\ coordState = "init"
    /\ \/ coordPrepared = {i : i \in 1..numShards} \ {dsState[Coordinator].Shard}
          \* All shards excluding the one coordinator resides in are prepared
       \/ \A s \in {i : i \in 1..numShards} :
          Cardinality({ds \in dsState[Coordinator].Accepted : dsState[ds].Shard = s})
          \geq Cardinality(Shards[s]) \div 2
          \* prepareAccepted message from a follower indicates the leader is prepared as well
          \* According to shortcut messages, all shards are prepared with fault-tolerance
    /\ coordState' = "commit"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "committed"]
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated, msgs>>

CoordAbort ==
    /\ coordState = "init"
    /\ coordState' = "abort"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "aborted"]
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated, msgs>>

CoordSendPhase2a ==
    /\ \/ coordState = "commit"
       \/ coordState = "abort"
    /\ send([type |-> "phase2a", src |-> Coordinator,
             desc |-> IF coordState = "commit" THEN "committed" ELSE "aborted"])
    /\ coordDecisionReplicated' = coordDecisionReplicated \cup {Coordinator}
    /\ UNCHANGED <<dsState, coordState, coordPrepared>>

CoordRcvPhase2b(ds) ==
    /\ ds \in Shards[dsState[Coordinator].Shard]   \* ds is in the same shard as the coordinator
    /\ [type |-> "phase2b", src |-> ds, dst |-> Coordinator, desc |-> "coordDecision"] \in msgs
    /\ coordDecisionReplicated' = coordDecisionReplicated \cup {ds}
    /\ UNCHANGED <<dsState, coordState, coordPrepared, msgs>>

CoordBroadcastDecision ==
    /\ \/ coordState = "commit"
       \/ coordState = "abort"
    /\ Cardinality(coordDecisionReplicated) \geq Cardinality(Shards[dsState[Coordinator].Shard]) \div 2 + 1
    /\ send([type |-> IF coordState = "commit" THEN "commit" ELSE "abort"])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                              LEADER ACTIONS                             *)
(***************************************************************************)
LeaderPrepare(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ dsState[ds].State = "working"
    /\ dsState' = [dsState EXCEPT ![ds].State = "prepared"]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderAbort(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ dsState[ds].State = "working"
    /\ dsState' = [dsState EXCEPT ![ds].State = "aborted"]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderSendPhase2aLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ send([type |-> "phase2a", src |-> ds,
             desc |-> IF dsState[ds].State = "prepared" THEN "leaderPrepared" ELSE "leaderAborted"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].LeaderDecisionReplicated = dsState[ds].LeaderDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase2bLeaderDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase2b", src |-> src, dst |-> dst, desc |-> "leaderDecision"] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![dst].LeaderDecisionReplicated = dsState[dst].LeaderDecisionReplicated \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderRcvFollowerAccept(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ [type |-> "prepareAccepted", src |-> src] \in msgs
    /\ dsState' = [dsState EXCEPT ![dst].Accepted = dsState[dst].Accepted \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderSendDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ Cardinality(dsState[ds].LeaderDecisionReplicated) \geq Cardinality(Shards[dsState[ds].Shard]) \div 2 + 1
    /\ send([type |-> IF dsState[ds].State = "prepared" THEN "prepared" ELSE "aborted",
             src |-> dsState[ds].Shard])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>

LeaderSendPhase2aCoordDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ [type |-> "commit"] \in msgs
       \/ [type |-> "abort"] \in msgs   \* Decision from the coordinator
       \/ \A s \in {i : i \in 1..numShards} :
          Cardinality({x \in dsState[ds].Accepted : dsState[x].Shard = s}) \geq Cardinality(Shards[s]) \div 2
          \* prepareAccepted message from a follower indicates the leader is prepared as well
          \* According to shortcut messages, all shards are prepared with fault-tolerance
    /\ send([type |-> "phase2a",
             src |-> ds, desc |-> IF [type |-> "abort"] \in msgs THEN "aborted" ELSE "committed"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].State = IF [type |-> "abort"] \in msgs THEN "aborted" ELSE "committed",
                   ![ds].CoordDecisionReplicated = dsState[ds].CoordDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase2bCoordDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase2b", src |-> src, dst |-> dst, desc |-> "coordDecision"] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![dst].CoordDecisionReplicated = dsState[dst].CoordDecisionReplicated \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderAck(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ Cardinality(dsState[ds].CoordDecisionReplicated) \geq Cardinality(Shards[dsState[ds].Shard]) \div 2 + 1
    /\ send([type |-> "ack", src |-> dsState[ds].Shard])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                             FOLLOWER ACTIONS                            *)
(***************************************************************************)
FollowerSendPhase2bLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
       \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderAborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State = 
                   IF [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
                   THEN "prepared" ELSE "aborted"]
    /\ msgs' = msgs \cup {[type |-> "prepareAccepted", src |-> ds],     \* Occam's shortcut messages
                [type |-> "phase2b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "leaderDecision"]}
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

FollowerSendPhase2bCoordDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
       \/ [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "aborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State =
                   IF [type |-> "phase2a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
                   THEN "committed" ELSE "aborted"]
    /\ send([type |-> "phase2b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "coordDecision"])
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            NEXT STATE ACTION                            *)
(***************************************************************************)
Next ==
    \/ CoordCommit
    \/ CoordAbort
    \/ CoordSendPhase2a
    \/ CoordBroadcastDecision
    \/ \E ds \in DS : \/ CoordRcvFollowerAccept(ds)
                      \/ CoordRcvPhase2b(ds)
                      \/ LeaderPrepare(ds)
                      \/ LeaderAbort(ds)
                      \/ LeaderSendPhase2aLeaderDecision(ds)
                      \/ LeaderSendDecision(ds)
                      \/ LeaderSendPhase2aCoordDecision(ds)
                      \/ LeaderAck(ds)
                      \/ FollowerSendPhase2bLeaderDecision(ds)
                      \/ FollowerSendPhase2bCoordDecision(ds)
    \/ \E src, dst \in DS : \/ LeaderRcvPhase2bLeaderDecision(src, dst)
                            \/ LeaderRcvFollowerAccept(src, dst)
                            \/ LeaderRcvPhase2bCoordDecision(src, dst)
    \/ \E s \in {i : i \in 1..numShards} : \/ CoordRcvLeaderPrepare(s)
                                           \/ CoordRcvLeaderAbort(s)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               CONSTRAINTS                               *)
(***************************************************************************)
AllCommit == \A ds \in DS : dsState[ds].State = "committed"

AllAbort == \A ds \in DS : dsState[ds].State = "aborted"
    
Liveness == <>(AllCommit \/ AllAbort)

Safety ==
    \A ds1, ds2 \in DS : ~ /\ dsState[ds1].State = "aborted"
                           /\ dsState[ds2].State = "committed"

Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec
            /\ WF_vars(CoordCommit)
            /\ WF_vars(CoordSendPhase2a)
            /\ WF_vars(CoordBroadcastDecision)
            /\ \A ds \in DS : /\ WF_vars(CoordRcvFollowerAccept(ds))
                              /\ WF_vars(CoordRcvPhase2b(ds))
                              /\ WF_vars(LeaderPrepare(ds))
                              /\ WF_vars(LeaderSendPhase2aLeaderDecision(ds))
                              /\ WF_vars(LeaderSendDecision(ds))
                              /\ WF_vars(LeaderSendPhase2aCoordDecision(ds))
                              /\ WF_vars(LeaderAck(ds))
                              /\ WF_vars(FollowerSendPhase2bLeaderDecision(ds))
                              /\ WF_vars(FollowerSendPhase2bCoordDecision(ds))
            /\ \A src, dst \in DS : /\ WF_vars(LeaderRcvPhase2bLeaderDecision(src, dst))
                                    /\ WF_vars(LeaderRcvFollowerAccept(src, dst))
                                    /\ WF_vars(LeaderRcvPhase2bCoordDecision(src, dst))
            /\ \A s \in {i : i \in 1..numShards} : /\ WF_vars(CoordRcvLeaderPrepare(s))
                                                   /\ WF_vars(CoordRcvLeaderAbort(s))
=============================================================================
\* Modification History
\* Last modified Thu May 25 11:30:41 HKT 2023 by fcui22
\* Created Thu May 25 11:29:16 HKT 2023 by fcui22