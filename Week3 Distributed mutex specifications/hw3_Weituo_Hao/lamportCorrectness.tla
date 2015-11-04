-----------MODULE lamportCorrectness ----------
EXTENDS Lamport,TLC


CONSTANTS NumOfNats, NumOfProcs

Constraint ==  \A p \in Proc: clock[p] < NumOfNats
MC_Nat == 0..NumOfNats
MC_Proc == 1..NumOfProcs
===========================================
