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


---- MODULE MESI ----
EXTENDS Integers, TLAPS
CONSTANTS
  NUMPROCS,    \* Number of processors 
  NUMCLINES,   \* Number of lines per cache
  NUMMLINES,   \* Number of lines in main memory
  NUMREQS

VARIABLES
  cache,   \* Set of cache in the system. Each cache is a function from
           \* cache line number to state
  mainmemory,
  sent
vars == <<cache, mainmemory, sent>>

\* States of a cache line
MODIFIED == 0
EXCLUSIVE == 1
SHARED == 2
INVALID == 3
STATES == {MODIFIED, EXCLUSIVE, SHARED, INVALID}

Processors == 1..NUMPROCS
CLines == 1..NUMCLINES
MLines == 1..NUMMLINES
Requests == 1..NUMREQS
Lines == [linenum : MLines, state : STATES, data: Nat]
\*NoneLine == CHOOSE l: l \notin Lines

Send(m) == sent' = sent \cup {m}
GhostSend(m) == Send(m)
Reqnum == CHOOSE reqnum \in Nat: \A m \in sent: m.type \in {"RdReq", "RdXReq", "UpgrReq"} => reqnum > m.reqnum
UnservedReq(p, reqnum) == ~\E m \in sent: m.type = "RdDone" /\ m.from = p /\ m.reqnum = reqnum
UnrespedReq(p, reqnum) == ~\E m \in sent: m.type = "RdResp" /\ m.from = p /\ m.reqnum = reqnum

Init ==
  /\ cache = [p \in Processors |-> [linenum \in MLines |-> [state |-> INVALID, data |-> 0]]]
  /\ mainmemory = [line \in MLines |-> 0]
  /\ sent = {}

Messages ==
  [type: {"RdReq", "RdXReq", "UpgrReq"}, from: Processors, linenum: MLines, reqnum: Requests] \cup
  [type: {"RdResp", "RdXResp"}, from: Processors, to: Processors, reqnum: Requests, line: Lines] \cup
  [type: {"RdDone", "RdXDone"}, from: Processors, reqnum: Requests] \cup
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
PrRd(p, l) ==
  CASE cache[p][l].state = INVALID -> 
        /\ Send([type |-> "RdReq", from |-> p, linenum |-> l, reqnum |-> Reqnum])
        /\ UNCHANGED <<cache, mainmemory>>
    [] OTHER ->
        UNCHANGED vars

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
    /\   CASE cache[p2][m.linenum].state = INVALID ->
                UNCHANGED <<cache, mainmemory>>
           [] cache[p2][m.linenum].state \in {EXCLUSIVE, SHARED} ->
                /\ cache' = [cache EXCEPT ![p2][m.linenum] = [state |-> SHARED, data |-> @.data]]
                /\ UNCHANGED mainmemory
           [] cache[p2][m.linenum].state = MODIFIED ->
                /\ cache' = [cache EXCEPT ![p2][m.linenum] = [state |-> SHARED, data |-> @.data]]
                /\ mainmemory' = [mainmemory EXCEPT![m.linenum] = cache[p2][m.linenum].data]
    /\ Send([type |-> "RdResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> cache[p2][m.linenum]])

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
PrRdDone(p) ==
  \/ \E m2 \in sent:
      /\ m2.type = "RdResp" /\ m2.to = p
      /\ UnservedReq(p, m2.reqnum)
      /\ m2.line.state # INVALID
      /\ cache' = [cache EXCEPT ![p][m2.line.linenum] =
          [state |-> SHARED, data |-> m2.line.data]]
      /\ GhostSend([type |-> "RdDone", reqnum |-> m2.num, from |-> p])
      /\ UNCHANGED mainmemory
  \/ \E S \in SUBSET sent, reqnum \in Requests:
      /\ \A m2 \in S: m2.reqnum = reqnum
      /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
      /\ UnservedReq(p, reqnum)
      /\ \A m2 \in S:
          /\ m2.type = "RdResp" /\ m2.to = p
          /\ m2.line.state = INVALID
          /\ cache' = [cache EXCEPT ![p][m2.line.linenum] =
              [state |-> EXCLUSIVE, data |-> mainmemory[m2.line.linenum]]]
      /\ GhostSend([type |-> "RdDone", reqnum |-> reqnum, from |-> p])
      /\ UNCHANGED mainmemory

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
PrWr(p, l) ==
  CASE cache[p][l].state = INVALID ->
        /\ Send([type |-> "RdXReq", from |-> p, linenum |-> l, reqnum |-> Reqnum])
        /\ UNCHANGED <<mainmemory, cache>>
    [] cache[p][l].state = EXCLUSIVE ->
        /\ cache' = [cache EXCEPT ![p][l] = [state |-> MODIFIED, data |-> @.data]]
        /\ UNCHANGED <<mainmemory, sent>>
    [] cache[p][l].state = SHARED ->
        /\ Send([type |-> "UpgrReq", from |-> p, linenum |-> l, reqnum |-> Reqnum])
        /\ cache' = [cache EXCEPT ![p][l] = [state |-> MODIFIED, data |-> @.data]]
        /\ UNCHANGED mainmemory
    [] OTHER -> UNCHANGED vars

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
    /\ CASE cache[p2][m.linenum].state = INVALID ->
              UNCHANGED <<mainmemory, cache>>
         [] cache[p2][m.linenum].state \in {EXCLUSIVE, SHARED} ->
              /\ cache' = [cache EXCEPT ![p2][m.linenum] = [state |-> INVALID, data |-> @.data]]
              /\ UNCHANGED mainmemory
         [] cache[p2][m.linenum].state = MODIFIED ->
              /\ cache' = [cache EXCEPT ![p2][m.linenum] = [state |-> INVALID, data |-> @.data]]
              /\ mainmemory' = [mainmemory EXCEPT![m.linenum] = cache[p2][m.linenum].data]
    /\ Send([type |-> "RdXResp", from |-> p2, to |-> m.from, reqnum |-> m.reqnum, line |-> cache[p2][m.linenum]])

(*
From Table 1.1 in Wiki page:
Operation: PrWr

  Initial State: Invalid(I)
  Response:
    - State transition to (M)Modified in the requestor Cache.
    - If other Caches have copy, they send value, otherwise fetch from Main Memory
*)
PrWrDone(p) ==
  \/ \E m2 \in sent:
      /\ m2.type = "RdXResp" /\ m2.to = p
      /\ UnservedReq(p, m2.reqnum)
      /\ m2.line.state # INVALID
      /\ cache' = [cache EXCEPT ![p][m2.line.linenum] = [state |-> MODIFIED, data |-> m2.line.data]]
      /\ GhostSend([type |-> "RdXDone", reqnum |-> m2.num, from |-> p])
      /\ UNCHANGED mainmemory
  \/   \E S \in SUBSET sent, reqnum \in Requests:
        /\ \A m2 \in S: m2.reqnum = reqnum
        /\ \A p2 \in Processors \ {p}: \E m2 \in S: m2.from = p2
        /\ UnservedReq(p, reqnum)
        /\ \A m2 \in S:
            /\ m2.type = "RdXResp" /\ m2.to = p
            /\ m2.line.state = INVALID
            /\ cache' = [cache EXCEPT ![p][m2.line.linenum] = [state |-> MODIFIED, data |-> mainmemory[m2.line.linenum]]]
        /\ GhostSend([type |-> "RdXDone", reqnum |-> reqnum, from |-> p])
        /\ UNCHANGED mainmemory

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
    /\ UnservedReq(p2, m.reqnum)
    /\ cache' = [cache EXCEPT ![p2][m.linenum] = [state |-> INVALID, data |-> @.data]]
    /\ GhostSend([type |-> "UpgrResp", from |-> p2, to |-> m.from, reqnum |-> m.num])
    /\ UNCHANGED mainmemory

Next == \E p \in Processors: \/ \E l \in MLines: PrRd(p, l) \/ PrWr(p, l)
                             \/ PrRdResp(p) \/ PrRdDone(p) \/ PrWrResp(p) \/ PrWrDone(p) \/ PrUpgrResp(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ sent \in SUBSET Messages
  /\ cache \in [Processors -> [MLines -> [state: STATES, data: Nat]]]
  /\ mainmemory \in [MLines -> Nat]

THEOREM TypeInv == Spec => []TypeOK
  <1> USE DEF TypeOK, STATES
  <1>1. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE Next
      <3> SUFFICES ASSUME NEW p \in Processors,
                          \/ \E l \in MLines: PrRd(p, l) \/ PrWr(p, l)
                          \/ PrRdResp(p) \/ PrRdDone(p) \/ PrWrResp(p) \/ PrWrDone(p) \/ PrUpgrResp(p)
                   PROVE  TypeOK'
        BY <2>1 DEF Next
      <3>1. CASE \E l \in MLines: PrRd(p, l) \/ PrWr(p, l)
        <4> SUFFICES ASSUME NEW l \in MLines,
                            PrRd(p, l) \/ PrWr(p, l)
                     PROVE  TypeOK'
          BY <3>1 
        <4>1. CASE PrRd(p, l) BY <4>1 DEF PrRd, Send, Messages, Reqnum, Requests
        <4>2. CASE PrWr(p, l)
        <4>3. QED
          BY <3>1, <4>1, <4>2
      <3>2. CASE PrRdResp(p) \/ PrRdDone(p) \/ PrWrResp(p) \/ PrWrDone(p) \/ PrUpgrResp(p)
        <4>1. CASE PrRdResp(p)
        <4>2. CASE PrRdDone(p)
        <4>3. CASE PrWrResp(p)
        <4>4. CASE PrWrDone(p)
        <4>5. CASE PrUpgrResp(p)
        <4>6. QED
          BY <3>2, <4>1, <4>2, <4>3, <4>4, <4>5
      <3>3. QED
        BY <2>1, <3>1, <3>2
    <2>2. CASE UNCHANGED vars
    <2>3. QED
      BY <2>1, <2>2
  <1>2. Init => TypeOK BY DEF Init
  <1> QED BY <1>1, <1>2, PTL DEF Init, Spec
=====================