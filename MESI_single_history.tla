Following info (enclosed in <<<...>>>) about the protocol is copied its from
Wikipedia page: https://en.wikipedia.org/wiki/MESI_protocol

<<<
The MESI protocol is an Invalidate-based cache coherence protocol, and is one
of the most common protocols which support write-back cache. It is also known
as the Illinois protocol (due to its development at the University of Illinois
at Urbana-Champaign).

The letters in the acronym MESI represent four exclusive states that a cache
line can be marked with (encoded using two additional bits):

1) Modified (M)
The cache line is present only in the current cache, and is dirty - it has been
modified (M state) from the value in main memory. The cache is required to write
the data back to main memory at some time in the future, before permitting any
other read of the (no longer valid) main memory state. The write-back changes
the line to the Shared state(S).

2) Exclusive (E)
The cache line is present only in the current cache, but is clean - it matches
main memory. It may be changed to the Shared state at any time, in response to a
read request. Alternatively, it may be changed to the Modified state when
writing to it.

3) Shared (S)
Indicates that this cache line may be stored in other cache of the machine and
is clean - it matches the main memory. The line may be discarded (changed to the
Invalid state) at any time.

4) Invalid (I)
Indicates that this cache line is invalid (unused).
>>>


---- MODULE MESI_single_history ----
EXTENDS Integers, TLAPS
CONSTANTS
  NUMPROCS,     \* Number of processors 
  TLC_NUMREQS   \* Number of requests. This is only for TLC. See `Requests`

VARIABLES
  cache,        \* Set of cache in the system
  sent          \* Set of messages sent on the system bus
vars == <<cache, sent>>

\* States of a cache line
MODIFIED == 0
EXCLUSIVE == 1
SHARED == 2
INVALID == 3
STATES == {MODIFIED, EXCLUSIVE, SHARED, INVALID}

\* Set of processors. Each processor is uniquely identified by an integer in 1..NUMPROCS
Processors == 1..NUMPROCS

\* Set of requests to be issued by the system.
\* For TLAPS, this is `Nat`
\* For TLC, this is   `1..TLC_NUMREQS`
Requests == Nat    

\* Sends `m` on system bus
Send(m) == sent' = sent \cup {m}

\* Does a ghost Send. That is, in the real implementation, do not send this message.
\* It is only for the proof and invariants.
GhostSend(m) == Send(m)

\*Reqnum == CHOOSE reqnum \in Requests: \A m \in sent: m.type \in {"RdReq", "RdXReq", "UpgrReq"} => reqnum > m.reqnum
Reqnum == CHOOSE reqnum \in Requests: \A m \in sent: reqnum > m.reqnum
PendingReq(p, reqnum) ==
  ~\E m \in sent: m.type \in {"RdDone", "RdXDone", "UpgrDone"} /\ m.from = p /\ m.reqnum = reqnum
UnrespedReq(p, reqnum) ==
  ~\E m \in sent: m.type \in {"RdResp", "RdXResp", "UpgrResp"} /\ m.from = p /\ m.reqnum = reqnum
ThisRequestsTurn(reqnum) ==
  \A m \in sent:
    m.reqnum < reqnum
    =>
    \E m2 \in sent:
      /\ m2.reqnum = m.reqnum
      /\ m2.type \in {"RdDone", "RdXDone", "UpgrDone"}

Maxmsg(S) == CHOOSE m \in S: \A m2 \in S: m.reqnum >= m2.reqnum
Mainmemory ==
  Maxmsg({m \in sent: m.type \in {"RdResp", "RdXResp"} /\ m.line.state = MODIFIED} \cup
    {[reqnum |-> -1, line |-> [data |-> 0]]}
  ).line.data

Cache(p) ==
  Maxmsg({m \in sent: m.from = p} \cup 
    {[reqnum |-> -1, line |-> [state |-> INVALID, data |-> 0]]}
  ).line

Init ==
  /\ cache = [p \in Processors |-> [state |-> INVALID, data |-> 0]]
  /\ sent = {}

Lines == [state: STATES, data: Nat]
Messages ==
  [type: {"RdReq", "RdXReq", "UpgrReq"}, from: Processors, reqnum: Requests] \cup
  [type: {"RdResp", "RdXResp"}, from: Processors, to: Processors, reqnum: Requests, line: Lines] \cup
  [type: {"RdDone", "RdXDone", "UpgrDone"}, from: Processors, reqnum: Requests] \cup
  [type: {"UpgrResp"}, from: Processors, to: Processors, reqnum: Requests]

(*
From Table 1.1 in Wiki page:
Operation: PrRd

  Initial State: Invalid(I)
  Response:
    - Issue BusRd to the bus

  Initial State: Non-invalid
  Response:
    - No bus transactions generated
    - State remains the same.
    - Read to the block is a Cache Hit
  
*)
PrRd(p) ==
  /\ ~\E reqnum \in Requests: PendingReq(p, reqnum)
  /\ CASE cache[p].state = INVALID -> 
        /\ Send([type |-> "RdReq", from |-> p, reqnum |-> Reqnum])
        /\ UNCHANGED <<cache>>
    [] OTHER ->
        UNCHANGED vars

PrRdHist(p) ==
  /\ ~\E reqnum \in Requests: PendingReq(p, reqnum)
  /\ Cache(p).state = INVALID
  /\ Send([type |-> "RdReq", from |-> p, reqnum |-> Reqnum])

MsgInvRdReq ==
  \A m \in sent:
    m.type = "RdReq"
    => /\ \A m2 \in sent: m2.reqnum < m.reqnum => ~PendingReq(m.from, m2.reqnum)
       /\ \/ ~\E m2 \in sent: m2.from = m.from
          \/ \E m2 \in sent:
                /\ m2.from = m.from
                /\ \A r \in m2.reqnum+1..m.reqnum-1: ~\E m3 \in sent: m3.from = m.from
                /\ m2.line.state = INVALID

(*
From Table 1.2 in Wiki page:
Bus Operation: BusRd (RdReq)

  Initial State: Invalid(I)
  Response:
    - No State change. Signal Ignored.

  Initial State: Exclusive(E)/Shared(S)
  Response:
    - Transition to Shared (Since it implies a read taking place in other cache)
    - Put FlushOpt on bus together with contents of block.

  Initial State: Modified(M)
  Response:
    - Transition to Shared(S)
    - Put FlushOpt (RdResp) on Bus with data. Received by sender of BusRd and Memory
      Controller, which writes to Main memory.
*)
PrRdResp(p2) ==
  \E m \in sent:
    /\ m.type = "RdReq"
    /\ UnrespedReq(p2, m.reqnum)
    /\ ThisRequestsTurn(m.reqnum)
    /\   CASE cache[p2].state = INVALID ->
                UNCHANGED <<cache>>
           [] OTHER ->
                cache' = [cache EXCEPT ![p2] = [state |-> SHARED, data |-> @.data]]
    /\ Send([type |-> "RdResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> cache[p2]])

PrRdRespHist(p2) ==
  \E m \in sent:
    /\ m.type = "RdReq"
    /\ UnrespedReq(p2, m.reqnum)
    /\ ThisRequestsTurn(m.reqnum)
    /\   CASE Cache(p2).state = INVALID ->
                Send([type |-> "RdResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> Cache(p2)])
           [] OTHER ->
                Send([type |-> "RdResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> [state |-> SHARED, data |-> Cache(p2).data]])

MsgInvRdResp ==
  \A m \in sent:
    m.type = "RdResp"
    => /\ \E m2 \in sent: m2.type = "RdReq" /\ m2.reqnum = m.reqnum
       \*/\ ThisRequestsTurn(m.reqnum)
       /\ \/ ~\E m2 \in sent: m2.from = m.from
          \/ \E m2 \in sent:
                /\ m2.from = m.from
                /\ \A r \in m2.reqnum+1..m.reqnum-1: ~\E m3 \in sent: m3.from = m.from
                /\ m.line.data = m2.line.data
                /\ \/ /\ m2.line.state = INVALID
                      /\ m.line.state = INVALID
                   \/ /\ m2.line.state # INVALID
                      /\ m.line.state = SHARED

(* TODO
From Table 1.1 in Wiki page:

Initial State: Invalid(I)
Operation: PrRd
Response:
  - State transition to (S)Shared, if other cache have non-invalid copy.
  - State transition to (E)Exclusive, if none (must ensure all others have
  reported)
  - If other cache have copy, one of them sends value, else fetch from Main
  Memory
*)
PrRdDone_S(p) ==
  \E m2 \in sent:
    /\ m2.type = "RdResp" /\ m2.to = p
    /\ PendingReq(p, m2.reqnum)
    /\ ThisRequestsTurn(m2.reqnum)
    /\ m2.line.state # INVALID
    /\ cache' = [cache EXCEPT ![p] = [state |-> SHARED, data |-> m2.line.data]]
    /\ GhostSend([type |-> "RdDone", reqnum |-> m2.reqnum, from |-> p])

PrRdDone_S_Hist(p) ==
  \E m2 \in sent:
    /\ m2.type = "RdResp" /\ m2.to = p
    /\ PendingReq(p, m2.reqnum)
    /\ ThisRequestsTurn(m2.reqnum)
    /\ m2.line.state # INVALID
    /\ GhostSend([type |-> "RdDone", reqnum |-> m2.reqnum, from |-> p, line |-> [state |-> SHARED, data |-> m2.line.data]])

PrRdDone_E(p) ==
  \E S \in SUBSET sent, reqnum \in Requests:
    /\ \A m2 \in S: m2.reqnum = reqnum
    /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
    /\ PendingReq(p, reqnum)
    /\ ThisRequestsTurn(reqnum)
    /\ \A m2 \in S: m2.type = "RdResp" /\ m2.to = p /\ m2.line.state = INVALID
    /\ cache' = [cache EXCEPT ![p] = [state |-> EXCLUSIVE, data |-> Mainmemory]]
    /\ GhostSend([type |-> "RdDone", reqnum |-> reqnum, from |-> p])

PrRdDone_E_Hist(p) ==
  \E S \in SUBSET sent, reqnum \in Requests:
    /\ \A m2 \in S: m2.reqnum = reqnum
    /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
    /\ PendingReq(p, reqnum)
    /\ ThisRequestsTurn(reqnum)
    /\ \A m2 \in S: m2.type = "RdResp" /\ m2.to = p /\ m2.line.state = INVALID
    /\ GhostSend([type |-> "RdDone", reqnum |-> reqnum, from |-> p, line |-> [state |-> EXCLUSIVE, data |-> Mainmemory]])

MsgInvRdDoneInv ==
  \A m \in sent:
  m.type = "RdDone"
  => \/ \E m2 \in sent:
          /\ m2.type = "RdResp" /\ m2.to = m.from /\ m2.reqnum = m.reqnum
          \*/\ ThisRequestsTurn(m2.reqnum)
          /\ m2.line.state # INVALID
          /\ m.line.data = m2.line.data
          /\ m.line.state = SHARED
     \/ \E S \in SUBSET sent:
          /\ \A m2 \in S: m2.reqnum = m.reqnum
          /\ \A p2 \in Processors \ {m.from}: \E m2 \in S: m2.from = p2
          \*/\ ThisRequestsTurn(reqnum)
          /\ \A m2 \in S: m2.type = "RdResp" /\ m2.to = m.from /\ m2.line.state = INVALID
          /\ m.line.state = EXCLUSIVE
          /\ m.line.data = Mainmemory

(*
From Table 1.1 in Wiki page:
Operation: PrWr

  Initial State: Invalid(I)
  Response:
    - Issue BusRdX signal on the bus
    - State transition to (M)Modified in the requestor Cache.

  Initial State: Exclusive(E)
  Response:
    - No bus transaction generated
    - State transition from Exclusive to (M)Modified

  Initial State: Shared(S)
  Response:
    - Issues BusUpgr signal on the bus.
    - State transition to (M)Modified.
    - other Caches see BusUpgr and mark their copies of the block as (I)Invalid.
    
  Initial State: Modified(M)
  Response:
    - No bus transaction generated
    - State remains the same
*)
PrWr(p) ==
  /\ ~\E reqnum \in Requests: PendingReq(p, reqnum)
  /\ CASE cache[p].state = INVALID ->
        /\ Send([type |-> "RdXReq", from |-> p, reqnum |-> Reqnum])
        /\ UNCHANGED <<cache>>
    [] cache[p].state = EXCLUSIVE ->
        /\ cache' = [cache EXCEPT ![p] = [state |-> MODIFIED, data |-> @.data]]
        /\ UNCHANGED <<sent>>
    [] cache[p].state = SHARED ->
        /\ Send([type |-> "UpgrReq", from |-> p, reqnum |-> Reqnum])
        /\ cache' = [cache EXCEPT ![p] = [state |-> MODIFIED, data |-> @.data]]
    [] OTHER -> UNCHANGED vars

PrWr_Hist(p) ==
  /\ ~\E reqnum \in Requests: PendingReq(p, reqnum)
  /\ CASE Cache(p).state = INVALID ->
        Send([type |-> "RdXReq", from |-> p, reqnum |-> Reqnum, line |-> Cache(p)])
    [] cache[p].state = EXCLUSIVE ->
        Send([type |-> "RdXGhost", from |-> p, reqnum |-> Reqnum, line |-> [state |-> MODIFIED, data |-> @.data]])
        /\ cache' = [cache EXCEPT ![p] = ]
        /\ UNCHANGED <<sent>>
    [] cache[p].state = SHARED ->
        /\ Send([type |-> "UpgrReq", from |-> p, reqnum |-> Reqnum])
        /\ cache' = [cache EXCEPT ![p] = [state |-> MODIFIED, data |-> @.data]]
    [] OTHER -> UNCHANGED vars

MsgRdXReqInv ==
  
(*
From Table 1.1 in Wiki page:
Bus Operation: BusRdX (RdXReq)

  Initial State: Invalid(I)
  Response:
    - No State change. Signal Ignored.

  Initial State: Exclusive(E)/Shared(S)
  Response:
    - Transition to Invalid(I).
    - Put FlushOpt on Bus, together with the data from now-invalidated block.

  Initial State: Modified(M)
  Response:
    - Transition to Invalid(I)
    - Put FlushOpt (RdResp) on Bus with data. Received by sender of BusRd and Memory
      Controller, which writes to Main memory.
*)
PrWrResp(p2) ==
  \E m \in sent:
    /\ m.type = "RdXReq"
    /\ UnrespedReq(p2, m.reqnum)
    /\ ThisRequestsTurn(m.reqnum)
    /\ CASE cache[p2].state = INVALID ->
              UNCHANGED <<cache>>
         [] OTHER ->
              cache' = [cache EXCEPT ![p2] = [state |-> INVALID, data |-> @.data]]
    /\ Send([type |-> "RdXResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> cache[p2]])

(*
From Table 1.1 in Wiki page:
Operation: PrWr

  Initial State: Invalid(I)
  Response:
    - State transition to (M)Modified in the requestor Cache.
    - If other Caches have copy, they send value, otherwise fetch from Main Memory
*)
PrWrDone_S(p) ==
  \E m2 \in sent:
    /\ m2.type = "RdXResp" /\ m2.to = p
    /\ PendingReq(p, m2.reqnum)
    /\ ThisRequestsTurn(m2.reqnum)
    /\ m2.line.state # INVALID
    /\ cache' = [cache EXCEPT ![p] = [state |-> MODIFIED, data |-> m2.line.data]]
    /\ GhostSend([type |-> "RdXDone", reqnum |-> m2.reqnum, from |-> p])

PrWrDone_E(p) ==
  \E S \in SUBSET sent, reqnum \in Requests:
    /\ \A m2 \in S: m2.reqnum = reqnum
    /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
    /\ PendingReq(p, reqnum)
    /\ ThisRequestsTurn(reqnum)
    /\ \A m2 \in S: m2.type = "RdXResp" /\ m2.to = p /\ m2.line.state = INVALID
    /\ cache' = [cache EXCEPT ![p] = [state |-> MODIFIED, data |-> Mainmemory]]
    /\ GhostSend([type |-> "RdXDone", reqnum |-> reqnum, from |-> p])

(*
From Table 1.1 in Wiki page:
Bus Operation: BusUpgr (UpgrReq)

  Initial State: *
  Response:
    - other Caches see BusUpgr and mark their copies of the block as (I)Invalid.
*)
PrUpgrResp(p2) ==
  \E m \in sent:
    /\ m.type = "UpgrReq"
    /\ PendingReq(p2, m.reqnum)
    /\ ThisRequestsTurn(m.reqnum)
    /\ cache' = [cache EXCEPT ![p2] = [state |-> INVALID, data |-> @.data]]
    /\ GhostSend([type |-> "UpgrResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum])

PrUpgrDone(p) ==
  \E S \in SUBSET sent, reqnum \in Requests:
    /\ \A m2 \in S: m2.reqnum = reqnum
    /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
    /\ PendingReq(p, reqnum)
    /\ ThisRequestsTurn(reqnum)
    /\ \A m2 \in S: m2.type = "UpgrResp" /\ m2.to = p
    /\ GhostSend([type |-> "UpgrDone", reqnum |-> reqnum, from |-> p])
    /\ UNCHANGED <<cache>>

Next == \E p \in Processors: \/ PrRd(p) \/ PrWr(p)
                             \/ PrRdResp(p) \/ PrRdDone_S(p) \/ PrRdDone_E(p) \/ PrWrResp(p) \/ PrWrDone_E(p) \/ PrWrDone_S(p) \/ PrUpgrResp(p) \/ PrUpgrDone(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ sent \in SUBSET Messages
  /\ cache \in [Processors -> Lines]

Safe ==
  \A p1, p2 \in Processors:
    /\ cache[p1].state = MODIFIED => cache[p2].state = INVALID
    /\ cache[p1].state = EXCLUSIVE => cache[p2].state = INVALID
    /\ cache[p1].state = SHARED => cache[p2].state \in {SHARED, INVALID}

THEOREM Safety == Spec => []Safe

LEMMA ReqnumType == TypeOK => Reqnum \in Nat BY DEF Reqnum, TypeOK, Messages, Requests

(*
THEOREM TypeInv == Spec => []TypeOK
  <1> USE DEF TypeOK, STATES
  <1>1. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE Next
      <3> SUFFICES ASSUME NEW p \in Processors,
                          \/ PrRd(p) \/ PrWr(p)
                          \/ PrRdResp(p) \/ PrRdDone_S(p) \/ PrRdDone_E(p) \/ PrWrResp(p) \/ PrWrDone_E(p) \/ PrWrDone_S(p) \/ PrUpgrResp(p) \/ PrUpgrDone(p)
                   PROVE  TypeOK'
        BY <2>1 DEF Next
      <3>1. CASE PrRd(p) \/ PrWr(p)
        <4> SUFFICES ASSUME PrRd(p) \/ PrWr(p)
                     PROVE  TypeOK'
          BY <3>1 
        <4>1. CASE PrRd(p) BY <4>1, ReqnumType DEF PrRd, Send, Messages, vars, Requests
        <4>2. CASE PrWr(p) BY <4>2, ReqnumType DEF PrWr, Send, Messages, vars, Requests, Lines
        <4>3. QED
          BY <3>1, <4>1, <4>2
      <3>2. CASE PrRdResp(p) \/ PrRdDone_S(p) \/ PrRdDone_E(p) \/ PrWrResp(p) \/ PrWrDone_E(p) \/ PrWrDone_S(p) \/ PrUpgrResp(p) \/ PrUpgrDone(p)
        <4>1. CASE PrRdResp(p)
          <5>1. PICK m \in sent: PrRdResp(p)!(m) BY <4>1 DEF PrRdResp
          <5>2. mainmemory' \in Nat BY <5>1, mainmemory' = mainmemory \/ mainmemory' = cache[p].data DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = cache \/ cache' = [cache EXCEPT
                         ![p] = [state |-> SHARED, data |-> @.data]] DEF Lines
          <5>4a. DEFINE mm == [type |-> "RdResp", from |-> p, to |-> m.from,
                   reqnum |-> m.reqnum, line |-> cache[p]]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c
          <5> QED BY <5>2, <5>3, <5>4
        <4>2a. CASE PrRdDone_S(p)
          <5>1. PICK m \in sent: PrRdDone_S(p)!(m) BY <4>2a DEF PrRdDone_S
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = [cache EXCEPT
                         ![p] = [state |-> SHARED, data |-> m.line.data]] DEF Lines, Messages
          <5>4a. DEFINE mm == [type |-> "RdDone", from |-> p, reqnum |-> m.reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF GhostSend, Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c 
          <5> QED BY <5>2, <5>3, <5>4
        <4>2b. CASE PrRdDone_E(p)
          <5>1. PICK S \in SUBSET sent, reqnum \in Requests: PrRdDone_E(p)!(S, reqnum) BY <4>2b DEF PrRdDone_E
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = [cache EXCEPT
                         ![p] = [state |-> EXCLUSIVE, data |-> mainmemory]] DEF Lines, Messages
          <5>4a. DEFINE mm == [type |-> "RdDone", from |-> p, reqnum |-> reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF GhostSend, Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c 
          <5> QED BY <5>2, <5>3, <5>4
        <4>3. CASE PrWrResp(p)
          <5>1. PICK m \in sent: PrWrResp(p)!(m) BY <4>3 DEF PrWrResp
          <5>2. mainmemory' \in Nat BY <5>1, mainmemory' = mainmemory \/ mainmemory' = cache[p].data DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = cache \/ cache' = [cache EXCEPT
                         ![p] = [state |-> INVALID, data |-> cache[p].data]] DEF Lines
          <5>4a. DEFINE mm == [type |-> "RdXResp", from |-> p, to |-> m.from,
                   reqnum |-> m.reqnum, line |-> cache[p]]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c
          <5> QED BY <5>2, <5>3, <5>4
        <4>4a. CASE PrWrDone_S(p)
          <5>1. PICK m \in sent: PrWrDone_S(p)!(m) BY <4>4a DEF PrWrDone_S
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = [cache EXCEPT
                         ![p] = [state |-> MODIFIED, data |-> m.line.data]] DEF Lines, Messages
          <5>4a. DEFINE mm == [type |-> "RdXDone", from |-> p, reqnum |-> m.reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF GhostSend, Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c 
          <5> QED BY <5>2, <5>3, <5>4
        <4>4b. CASE PrWrDone_E(p)
          <5>1. PICK S \in SUBSET sent, reqnum \in Requests: PrWrDone_E(p)!(S, reqnum) BY <4>4b DEF PrWrDone_E
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = [cache EXCEPT
                         ![p] = [state |-> MODIFIED, data |-> mainmemory]] DEF Lines, Messages
          <5>4a. DEFINE mm == [type |-> "RdXDone", from |-> p, reqnum |-> reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF GhostSend, Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c 
          <5> QED BY <5>2, <5>3, <5>4
        <4>5. CASE PrUpgrResp(p)
          <5>1. PICK m \in sent: PrUpgrResp(p)!(m) BY <4>5 DEF PrUpgrResp
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1, cache' = cache \/ cache' = [cache EXCEPT
                         ![p] = [state |-> INVALID, data |-> cache[p].data]] DEF Lines
          <5>4a. DEFINE mm == [type |-> "UpgrResp", from |-> p, to |-> m.from, reqnum |-> m.reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF Send, GhostSend
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c
          <5> QED BY <5>2, <5>3, <5>4
        <4>6. CASE PrUpgrDone(p)
          <5>1. PICK S \in SUBSET sent, reqnum \in Requests: PrUpgrDone(p)!(S, reqnum) BY <4>6 DEF PrUpgrDone
          <5>2. mainmemory' \in Nat BY <5>1 DEF Lines
          <5>3. cache' \in [Processors -> Lines] BY <5>1\* DEF Lines, Messages
          <5>4a. DEFINE mm == [type |-> "UpgrDone", from |-> p, reqnum |-> reqnum]
          <5>4b. mm \in Messages BY <5>1 DEF Messages
          <5>4c. sent' = sent \cup {mm} BY <5>1 DEF GhostSend, Send
          <5> HIDE DEF mm
          <5>4. sent' \in SUBSET Messages BY <5>1, <5>4b, <5>4c 
          <5> QED BY <5>2, <5>3, <5>4
        <4>7. QED
          BY <3>2, <4>1, <4>2a, <4>2b, <4>3, <4>4a, <4>4b, <4>5, <4>6
      <3>3. QED
        BY <2>1, <3>1, <3>2
    <2>2. CASE UNCHANGED vars BY <2>2 DEF vars
    <2>3. QED
      BY <2>1, <2>2
  <1>2. Init => TypeOK BY DEF Init, Messages, Lines
  <1> QED BY <1>1, <1>2, PTL DEF Init, Spec
*)

=====================