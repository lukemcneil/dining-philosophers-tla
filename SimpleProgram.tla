--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"

Add1 == \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"

Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Fri Apr 22 00:49:43 EDT 2022 by luke
\* Created Fri Apr 22 00:31:51 EDT 2022 by luke
