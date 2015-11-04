------------------------------- MODULE sample -------------------------------

EXTENDS Naturals, TLC, Sequences, Integers
CONSTANT M,N

ValueX == 1 .. M
ValueY == 1 .. N
(*--algorithm Euclid
    variables
        x \in ValueX;
        y \in ValueY;
        x0 = x;
        y0 = y;
    
    begin    
    while x # y
    do 
        if x < y then
            y := y - x;
        else
            x := x - y;
        end if;
        
        (*assert x = GCD(x0, y0) /\ y = GCD(x0, y0);*)
        
    end while;
    end algorithm
 *)   
\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in ValueX
        /\ y \in ValueY
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Fri Nov 08 13:48:05 EST 2013 by Jayashree
\* Created Thu Nov 07 21:12:56 EST 2013 by Jayashree


