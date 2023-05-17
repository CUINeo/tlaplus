----------------------------- MODULE TwoPCPaxos -----------------------------
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
    [type : {"commit", "abort"}] \cup [type : {"prepared", "aborted", "ack"}, src : 1..numShards] \cup
    [type : {"phase1a"}, src : DS, desc : {"leaderPrepared", "leaderAborted", "committed", "aborted"}] \cup
    [type : {"phase1b"}, src : DS, dst : DS, desc : {"leaderDecision", "coordDecision"}]

-----------------------------------------------------------------------------
VARIABLES
    dsState,                    \* dsState[ds] is the state of data server ds
    coordState,                 \* The state of the coordinator
    coordPrepared,              \* The set of shards that are prepared
    coordDecisionReplicated,    \* The set of replicas to which the coordinator has replicated its decision
    msgs                        \* The message pool

TypeOK ==
    /\ dsState \in [DS -> [Shard : 1..numShards,
                           Role : {"Coordinator", "Leader", "Follower"},
                           LeaderDecisionReplicated : SUBSET DS,
                           CoordDecisionReplicated : SUBSET DS,
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

CoordCommit ==
    /\ coordState = "init"
    /\ coordPrepared = {i : i \in 1..numShards} \ {dsState[Coordinator].Shard}
                       \* All shards excluding the one coordinator resides in are prepared
    /\ coordState' = "commit"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "committed"]
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated, msgs>>

CoordAbort ==
    /\ coordState = "init"
    /\ coordState' = "abort"
    /\ dsState' = [dsState EXCEPT ![Coordinator].State = "aborted"]
    /\ UNCHANGED <<coordPrepared, coordDecisionReplicated, msgs>>

CoordSendPhase1a ==
    /\ \/ coordState = "commit"
       \/ coordState = "abort"
    /\ send([type |-> "phase1a", src |-> Coordinator,
             desc |-> IF coordState = "commit" THEN "committed" ELSE "aborted"])
    /\ coordDecisionReplicated' = coordDecisionReplicated \cup {Coordinator}
    /\ UNCHANGED <<dsState, coordState, coordPrepared>>

CoordRcvPhase1b(ds) ==
    /\ ds \in Shards[dsState[Coordinator].Shard]   \* ds is in the same shard as the coordinator
    /\ [type |-> "phase1b", src |-> ds, dst |-> Coordinator, desc |-> "coordDecision"] \in msgs
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

LeaderSendPhase1aLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ send([type |-> "phase1a", src |-> ds,
             desc |-> IF dsState[ds].State = "prepared" THEN "leaderPrepared" ELSE "leaderAborted"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].LeaderDecisionReplicated = dsState[ds].LeaderDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase1bLeaderDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase1b", src |-> src, dst |-> dst, desc |-> "leaderDecision"] \in msgs
    /\ dsState' = [dsState EXCEPT
                   ![dst].LeaderDecisionReplicated = dsState[dst].LeaderDecisionReplicated \cup {src}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated, msgs>>

LeaderSendDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ dsState[ds].State = "prepared"
       \/ dsState[ds].State = "aborted"
    /\ Cardinality(dsState[ds].LeaderDecisionReplicated) \geq Cardinality(Shards[dsState[ds].Shard]) \div 2 + 1
    /\ send([type |-> IF dsState[ds].State = "prepared" THEN "prepared" ELSE "aborted",
             src |-> dsState[ds].Shard])
    /\ UNCHANGED <<dsState, coordState, coordPrepared, coordDecisionReplicated>>

LeaderSendPhase1aCoordDecision(ds) ==
    /\ dsState[ds].Role = "Leader"
    /\ \/ [type |-> "commit"] \in msgs
       \/ [type |-> "abort"] \in msgs   \* Decision from the coordinator
    /\ send([type |-> "phase1a",
             src |-> ds, desc |-> IF [type |-> "commit"] \in msgs THEN "committed" ELSE "aborted"])
    /\ dsState' = [dsState EXCEPT 
                   ![ds].State = IF [type |-> "commit"] \in msgs THEN "committed" ELSE "aborted",
                   ![ds].CoordDecisionReplicated = dsState[ds].CoordDecisionReplicated \cup {ds}]
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

LeaderRcvPhase1bCoordDecision(src, dst) ==
    /\ dsState[dst].Role = "Leader"
    /\ dsState[src].Shard = dsState[dst].Shard      \* Source and destination reside in the same shard
    /\ [type |-> "phase1b", src |-> src, dst |-> dst, desc |-> "coordDecision"] \in msgs
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
FollowerSendPhase1bLeaderDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ \/ [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
       \/ [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderAborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State = 
                   IF [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "leaderPrepared"] \in msgs
                   THEN "prepared" ELSE "aborted"]
    /\ send([type |-> "phase1b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "leaderDecision"])
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

FollowerSendPhase1bCoordDecision(ds) ==
    /\ dsState[ds].Role = "Follower"
    /\ \/ [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
       \/ [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "aborted"] \in msgs
    /\ dsState' = [dsState EXCEPT ![ds].State =
                   IF [type |-> "phase1a", src |-> Leaders[dsState[ds].Shard], desc |-> "committed"] \in msgs
                   THEN "committed" ELSE "aborted"]
    /\ send([type |-> "phase1b", src |-> ds, dst |-> Leaders[dsState[ds].Shard], desc |-> "coordDecision"])
    /\ UNCHANGED <<coordState, coordPrepared, coordDecisionReplicated>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                            NEXT STATE ACTION                            *)
(***************************************************************************)
Next ==
    \/ CoordCommit
    \/ CoordAbort
    \/ CoordSendPhase1a
    \/ CoordBroadcastDecision
    \/ \E ds \in DS : \/ CoordRcvPhase1b(ds)
                      \/ LeaderPrepare(ds)
                      \/ LeaderAbort(ds)
                      \/ LeaderSendPhase1aLeaderDecision(ds)
                      \/ LeaderSendDecision(ds)
                      \/ LeaderSendPhase1aCoordDecision(ds)
                      \/ LeaderAck(ds)
                      \/ FollowerSendPhase1bLeaderDecision(ds)
                      \/ FollowerSendPhase1bCoordDecision(ds)
    \/ \E src, dst \in DS : \/ LeaderRcvPhase1bLeaderDecision(src, dst)
                            \/ LeaderRcvPhase1bCoordDecision(src, dst)
    \/ \E s \in {i : i \in 1..numShards} : \/ CoordRcvLeaderPrepare(s)
                                           \/ CoordRcvLeaderAbort(s)

-----------------------------------------------------------------------------
(***************************************************************************)
(*                           CONSISTENT CONSTRAINT                         *)
(***************************************************************************)
Consistent ==
    \A ds1, ds2 \in DS : ~ /\ dsState[ds1].State = "aborted"
                           /\ dsState[ds2].State = "committed"
                           
AllCommit ==
    ~ \A ds \in DS : dsState[ds].State = "committed"

=============================================================================
\* Modification History
\* Last modified Wed May 17 16:12:51 HKT 2023 by cuifan
\* Last modified Wed May 17 14:47:51 HKT 2023 by cuifan
\* Last modified Wed May 17 12:02:36 HKT 2023 by fcui22
\* Created Tue May 16 15:55:05 HKT 2023 by fcui22
