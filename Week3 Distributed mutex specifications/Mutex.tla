---------------------- MODULE Mutex ---------------------
CONSTANT Proc
VARIABLE state
---------------------------------------------------------
Init == state = [p \in Proc |-> "idle"]
Request(p) == /\ state[p] = "idle"
              /\ state' = [state EXCEPT ![p] = "waiting"]

Acquire(p) == /\ state[p] = "waiting"
              /\ \A q \in Proc : state[q] # "owner"
              /\ state' = [state EXCEPT ![p] = "owner"]
Release(p) == /\ state[p] = "owner"
              /\ state' = [state EXCEPT ![p] = "idle"]

Next == \E p \in Proc : Request(p) \/ Acquire(p) \/ Release(p)

----------------------------------------------------
StarvationFree == \A p \in Proc : SF_state(Acquire(p))
Spec == Init /\ [][Next]_state /\ StarvationFree
=======================================================