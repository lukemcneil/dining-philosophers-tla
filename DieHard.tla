------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers

VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ small = 0
        /\ big = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

SmallToBig == IF big + small \leq 5
                THEN /\ big' = big + small
                     /\ small' = 0
                ELSE /\ big' = 5
                     /\ small' = big + small - 5

BigToSmall == IF big + small \leq 3
                THEN /\ big' = 0
                     /\ small' = big + small
                ELSE /\ big' = big + small - 3
                     /\ small' = 3

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

=============================================================================
\* Modification History
\* Last modified Fri Apr 22 01:17:41 EDT 2022 by luke
\* Created Fri Apr 22 00:55:33 EDT 2022 by luke
