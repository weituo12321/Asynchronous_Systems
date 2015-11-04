------------------------------ MODULE Lamport ------------------------------
EXTENDS Naturals, Sequences
CONSTANTS Proc, NumOfNats
(*ASSUME \A p \in Proc:
           /\ ~(p < p)
           /\ \A q \in Proc \ {p}: (p < q) \/ (q < p)
           /\ \A q, r \in Proc: (p < q) /\ (q < r) => (p < r)
       *)
a \prec b == \/ a.TS < b.TS
             \/ (a.TS = b.TS) /\ (a.proc < b.proc)
MC_Nat == 0..NumOfNats
--------------------------------------------------------------------------
VARIABLES state, msgQ, reqSet, clock, lastTSent, lastTRcvd
(*MC_Nat == 0..NumOfNats*)
vars == << state, msgQ, reqSet, clock, lastTSent, lastTRcvd >>
Init == /\ state = [p \in Proc |-> "idle"]
        /\ msgQ  = [p \in Proc |-> [q \in Proc \ {p} |-> <<>>] ]
        /\ reqSet = [p \in Proc |-> {}]
        /\ clock \in [Proc -> Nat]
        /\ lastTSent = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
        /\ lastTRcvd = [p \in Proc |-> [q \in Proc \ {p} |-> 0]] 
---------------------------------------------------------------------------
Request(p) == /\ state[p] = "idle"
              /\ state' = [state EXCEPT![p] = "waiting"]
              /\ \E n \in Nat:
                  /\ clock' = [clock EXCEPT![p] = n]
                  /\ n > clock[p]
                  /\ LET msg == [TS |-> n, proc |-> p, cmd |-> "acquire"]
                      IN /\ msgQ' = [msgQ EXCEPT![p] = [q \in Proc \ {p} |-> Append(@[q], msg)]] 
                         /\ reqSet' = [reqSet EXCEPT![p] = @ \cup {msg}]
                  /\ lastTSent' = [lastTSent EXCEPT![p] = [q \in Proc \ {p} |-> n]]
              /\ UNCHANGED lastTRcvd
              
Acquire(p) == 
             LET pReq == CHOOSE req \in reqSet[p]:req.proc = p 
             IN  /\ state[p] = "waiting"
                 /\ \A req \in reqSet[p] \ {pReq} : pReq \prec req
                 /\ \A q \in Proc \ {p} : pReq \prec [TS |-> lastTRcvd[p][q] + 1, proc |-> q]
                 /\ state' = [state EXCEPT![p] = "owner"]
                 /\ reqSet' = [reqSet EXCEPT![p] = @ \ {pReq}]
                 /\ UNCHANGED <<msgQ, clock, lastTSent, lastTRcvd>>
 
Release(p) == 
            /\ state[p] = "owner"
            /\ state' = [state EXCEPT![p] = "idle"]
            /\ LET msg == [TS |-> clock[p], proc |-> p, cmd |-> "release"]
               IN  msgQ' = [msgQ EXCEPT![p] = [q \in Proc \ {p} |-> Append(@[q], msg)]]
            /\  lastTSent' = [lastTSent EXCEPT![p] = [q \in Proc \ {p} |-> clock[p]]]
            /\ UNCHANGED <<clock, lastTRcvd, reqSet>>

RcvMsg(p, q) ==
            LET msg == Head(msgQ[q][p])
                msgQTail == [msgQ EXCEPT![q][p] = Tail(@)]
                ack == [TS |-> clock'[p], proc |-> p , cmd |-> "ack"]
            IN  /\ msgQ[q][p] /= <<>>
                /\ clock' = [clock EXCEPT![p] = IF msg.TS > @ THEN msg.TS ELSE @]
                /\ IF /\ msg.cmd = "acquire"
                      /\ [TS |-> lastTSent[p][q] + 1, proc |-> p] \prec msg
                      THEN /\ msgQ' = [msgQTail EXCEPT![p][q] = Append(@, ack)]
                           /\ lastTSent' = [lastTSent EXCEPT![p][q] = clock'[p]]
                      ELSE /\ msgQ' = msgQTail
                           /\ UNCHANGED lastTSent
                /\ lastTRcvd' = [lastTRcvd EXCEPT![p][q] = msg.TS]
                /\ reqSet' = [reqSet EXCEPT![p] = 
                                              CASE msg.cmd = "acquire" -> @ \cup {msg}
                                                 []msg.cmd = "release" -> {m \in @: m.proc /= q}
                                                 []msg.cmd = "ack" -> @]
                /\ UNCHANGED state
Tick(p) == /\ \E n \in Nat: /\ n > clock[p]
                            /\ clock' = [clock EXCEPT![p] = n]
           /\ UNCHANGED <<state, msgQ, reqSet, lastTSent, lastTRcvd>>

-------------------------------------------------------------------------------
Next == \E p \in Proc: \/ Request(p) \/ Acquire(p) \/ Release(p)
                       \/ \E q \in Proc \ {p}: RcvMsg(p, q)
                       \/ Tick(p)
Liveness == \A p \in Proc: /\ WF_vars(Acquire(p))
                           /\ \A q \in Proc \ {p}: WF_vars(RcvMsg(p, q))
                           
Constraint == \A p \in Proc: clock[p] < NumOfNats
Spec == Init /\ [][Next]_vars /\ Liveness 
                 

=============================================================================
\* Modification History
\* Last modified Mon Oct 05 19:00:24 EDT 2015 by Victor_Hao
\* Created Sun Oct 04 16:18:14 EDT 2015 by Victor_Hao
