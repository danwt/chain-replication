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
    value,
    \* @type: Int; Bound retries for model checking tractability
    retries

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
    /\ retries = 0

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
    /\ UNCHANGED retries

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
    /\ UNCHANGED retries

ReceiveSync ==
    \E p, prev \in SERVERS:
    /\ ~crashed[p]
    /\ p # prev
    /\ 0 < Len(fifo[prev, p])
    /\ LET 
        m == Head(fifo[prev, p])
        servers_ == [servers EXCEPT ![p] = {e \in @ : e <= p \/ prev <= e}]
        IN LET
        succ == Succ(servers_[p], p)
        pred == Pred(servers_[p], p)
        IN
        /\ m.nature = _sync
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT 
                ![prev, p] = Tail(@),
                ![p, succ] = IF prev = pred /\ p # succ THEN @ \o <<sync(m.value)>> ELSE @
            ]
        /\ servers' = servers_
        /\ response' = IF prev = pred /\ p = succ THEN m.value ELSE response
        /\ value' = [value EXCEPT ![p] = IF prev = pred THEN m.value ELSE @]
        /\ UNCHANGED retries

ReceiveUpdateHist ==
    \E p \in SERVERS:
    /\ ~crashed[p]
    /\ 0 < Len(fifo[CLIENT, p])
    /\ LET
        m == Head(fifo[CLIENT, p])
        servers_ == [servers EXCEPT ![p] = {e \in @ : e <= p}]
        IN LET
        succ == Succ(servers_[p], p)
        IN
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT 
                ![CLIENT, p] = Tail(@),
                ![p, succ] = IF succ = p THEN @ ELSE @ \o <<sync(m.value)>>
            ]
        /\ servers' = servers_
        /\ response' = IF succ = p THEN m.value ELSE response
        /\ value' = [value EXCEPT ![p] = m.value]
        /\ UNCHANGED retries

ClientSend == 
    LET head == CHOOSE e \in servers[CLIENT] : (\A x \in servers[CLIENT] : x <= e) IN
    /\ retries < Cardinality(SERVERS)
    /\ UNCHANGED crashed
    /\ fifo' = [fifo EXCEPT ![CLIENT, head] = @ \o <<updateHist(TARGET_VALUE)>>]
    /\ UNCHANGED servers
    /\ UNCHANGED response
    /\ UNCHANGED value
    /\ retries' = retries + 1

ClientSucceed == 
    /\ response # NullInt
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED response
    /\ value' = [value EXCEPT ![CLIENT] = response]
    /\ UNCHANGED retries

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
Sanity1  == value[CLIENT] = NullInt
Sanity2  == \E p \in SERVERS \cup {CLIENT}: value[p] # TARGET_VALUE
Sanity3  == action # "fail"
Sanity4  == action # "notifyFail"
Sanity5  == action # "receiveSync"
Sanity6  == action # "receiveUpdateHist"
Sanity7  == action # "clientSend"
Sanity8 == action # "clientSucceed"

Agreement ==
    value[CLIENT] # NullInt => 
        /\ \A p \in SERVERS: crashed[p] \/ value[p] = TARGET_VALUE
        /\ value[CLIENT] = TARGET_VALUE

Inv == Agreement

====