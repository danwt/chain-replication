---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

(*

@typeAlias: PID = Int;

@typeAlias: MSG = [
    nature : Str,
    value : Int
];

*)

NullInt == 0
NullStr == "NullStr"

SERVERS == 1..3
CLIENT == 0

TARGET_VALUE == 42

_sync == "sync"
_updateHist == "updateHist"

sync(value) ==       [nature |-> _sync,       value |-> value]
updateHist(value) == [nature |-> _updateHist, value |-> value]

VARIABLES
(*Meta*)
    \* @type: Str;
    action,
(*Global*)
    \* @type: PID -> Bool;
    crashed,
    \* @type: <<PID, PID>> -> Seq(MSG);
    fifo,
(*Local*)
    \* @type: PID -> Set(PID);
    servers,
    \* @type: Int; 
    response,
    \* @type: PID -> Int;
    value

Max(S) == CHOOSE e \in S : \A other \in S : other <= e
Min(S) == CHOOSE e \in S : \A other \in S : e <= other
Succ(servers_, p) == LET LT == {e \in servers_ : e < p} IN IF LT = {} THEN p ELSE Max(LT)
Pred(servers_, p) == LET GT == {e \in servers_ : p < e} IN IF GT = {} THEN p ELSE Min(GT)

Init == 
    /\ action = "init"
    /\ crashed = [p \in SERVERS |-> FALSE]
    /\ fifo = [p \in ((SERVERS \cup {CLIENT}) \X (SERVERS \cup {CLIENT})) |-> <<>>]
    /\ servers = [p \in (SERVERS \cup {CLIENT}) |-> SERVERS]
    /\ response = NullInt
    /\ value = [p \in (SERVERS \cup {CLIENT}) |-> NullInt]

Fail ==
    \E p, pCorrect \in SERVERS: 
    /\ p # pCorrect
    (*Always leave at least 1 correct process remaining*)
    /\ ~crashed[pCorrect]
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED response
    /\ UNCHANGED value

NotifyFail ==
    \E p \in SERVERS \cup {CLIENT}, pCrashed \in SERVERS:
    /\ p # CLIENT => ~crashed[p]
    /\ p # pCrashed
    /\ crashed[pCrashed]
    /\ pCrashed \in servers[p]
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ servers' = [servers EXCEPT ![p] = @ \ {pCrashed}]
    /\ UNCHANGED response
    /\ UNCHANGED value

ReceiveSync ==
    \E p, prev \in SERVERS:
    /\ ~crashed[p]
    /\ p # prev
    /\ 0 < Len(fifo[prev, p])
    /\ LET 
        m == Head(fifo[prev, p])
        IN
        /\ m.nature = _sync
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT 
                ![prev, p] = Tail(@),
                ![p, Succ(servers', p)] = IF prev = Pred(servers', p) /\ p # Succ(servers', p) THEN @ \o <<sync(m.value)>> ELSE @
            ]
        /\ servers' = [servers EXCEPT ![p] = {e \in @ : e <= p \/ prev <= e}]
        /\ response' = IF prev = Pred(servers', p) /\ p = Succ(servers', p) THEN m.value ELSE response
        /\ value' = [value EXCEPT ![p] = IF prev = Pred(servers', p) THEN m.value ELSE @]


ReceiveUpdateHist ==
    \E p \in SERVERS:
    /\ ~crashed[p]
    /\ 0 < Len(fifo[CLIENT, p])
    /\ LET
        m == Head(fifo[CLIENT, p])
        IN
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT 
                ![CLIENT, p] = Tail(@),
                ![p, Succ(servers', p)] = IF Succ(servers', p) = p THEN @ ELSE @ \o <<sync(m.value)>>
            ]
        /\ servers' = [servers EXCEPT ![p] = {e \in @ : e <= p}]
        /\ response' = IF Succ(servers', p) = p THEN m.value ELSE response
        /\ value' = [value EXCEPT ![p] = m.value]

ClientSend == 
    (*There's no need to explicitly model timeout and retry*)
    LET head == CHOOSE e \in servers[CLIENT] : (\A x \in servers[CLIENT] : x <= e) IN
    /\ UNCHANGED crashed
    /\ fifo' = [fifo EXCEPT ![CLIENT, head] = @ \o <<updateHist(TARGET_VALUE)>>]
    /\ UNCHANGED servers
    /\ UNCHANGED response
    /\ UNCHANGED value

ClientSucceed == 
    /\ response # NullInt
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED response
    /\ value' = [value EXCEPT ![CLIENT] = response]

Next ==
    \/ /\ Fail
       /\ action' = "fail"
    \/ /\ NotifyFail
       /\ action' = "notifyFail"
    \/ /\ ReceiveSync
       /\ action' = "receiveSync"
    \/ /\ ReceiveUpdateHist
       /\ action' = "receiveUpdateHist"
    \/ /\ ClientSend
       /\ action' = "clientSend"
    \/ /\ ClientSucceed
       /\ action' = "clientSucceed"


(*It _should_ be possible to find counterexamples for these.*)
Sanity0  == response = NullInt
Sanity1  == action # "fail"
Sanity2  == action # "notifyFail"
Sanity4  == action # "receiveSync"
Sanity5  == action # "receiveUpdateHist"
Sanity6  == action # "clientSend"
Sanity7 == action # "clientSucceed"

Agreement ==
    value[CLIENT] # NullInt => 
        /\ \A p \in SERVERS: crashed[p] \/ value[p] = TARGET_VALUE
        /\ value[CLIENT] = TARGET_VALUE

Inv == Sanity0


====