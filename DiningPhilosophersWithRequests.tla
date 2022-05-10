------------------- MODULE DiningPhilosophersWithRequests -------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

VARIABLES states, rightChopsticks, leftChopsticks, messages

TypeOK == /\ (\A n \in 1..N:
              /\ states[n] \in {"thinking", "waitingForRight", "waitingForLeft", "eating"}
              /\ rightChopsticks[n] \in {"notHolding", "holding"}
              /\ leftChopsticks[n] \in {"notHolding", "holding"})
          /\ (\A m \in messages:
                 /\ m.to \in 1..N
                 /\ m.from \in 1..N
                 /\ m.type \in {"rightChopstickRequest", "leftChopstickRequest", "rightChopstickReplyAccept", "leftChopstickReplyAccept", "rightChopstickReplyDeny", "leftChopstickReplyDeny"})

Init == /\ states = [n \in 1..N |-> "thinking"]
        /\ rightChopsticks = [n \in 1..N |-> "notHolding"]
        /\ leftChopsticks = [n \in 1..N |-> "notHolding"]
        /\ messages = {}

rightIndex(n) == IF n = N THEN 1 ELSE n+1
leftIndex(n) == IF n = 1 THEN N ELSE n-1

tryToEat(n) == /\ states[n] = "thinking"
               /\ messages' = messages \union { [ from |-> n, to |-> leftIndex(n), type |-> "leftChopstickRequest" ] }
               /\ states' = [states EXCEPT ![n] = "waitingForLeft"]
               /\ UNCHANGED << rightChopsticks, leftChopsticks >>

handleRightChopstickRequest(n) == /\ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "rightChopstickRequest")
                                  /\ (IF (/\ leftChopsticks[n] = "notHolding"
                                         /\ states[n] /= "waitingForLeft")
                                     THEN messages' = (messages \union { [ from |-> n, to |-> leftIndex(n), type |-> "rightChopstickReplyAccept" ] }) \ { [ from |-> leftIndex(n), to |-> n, type |-> "rightChopstickRequest" ] }
                                     ELSE messages' = (messages \union { [ from |-> n, to |-> leftIndex(n), type |-> "rightChopstickReplyDeny" ] }) \ { [ from |-> leftIndex(n), to |-> n, type |-> "rightChopstickRequest" ] })
                                  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>

handleLeftChopstickRequest(n) == /\ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "leftChopstickRequest")
                                 /\ (IF (/\ rightChopsticks[n] = "notHolding"
                                         /\ states[n] /= "waitingForRight")
                                     THEN messages' = (messages \union { [ from |-> n, to |-> rightIndex(n), type |-> "leftChopstickReplyAccept" ] }) \ { [ from |-> rightIndex(n), to |-> n, type |-> "leftChopstickRequest" ] }
                                     ELSE messages' = (messages \union { [ from |-> n, to |-> rightIndex(n), type |-> "leftChopstickReplyDeny" ] }) \ { [ from |-> rightIndex(n), to |-> n, type |-> "leftChopstickRequest" ] })
                                 /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>

handleRightChopstickReply(n) == states[n] = "waitingForRight" /\
                                \/ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "rightChopstickReplyAccept")
                                        /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "holding"]
                                        /\ states' = [states EXCEPT ![n] = "eating"]
                                        /\ messages' = messages \ { [ from |-> rightIndex(n), to |-> n, type |-> "rightChopstickReplyAccept" ] }
                                        /\ UNCHANGED leftChopsticks
                                \/ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "rightChopstickReplyDeny"
                                        /\ states' = [states EXCEPT ![n] = "thinking"]
                                        /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
                                        /\ messages' = messages \ { [ from |-> rightIndex(n), to |-> n, type |-> "rightChopstickReplyDeny" ] }
                                        /\ UNCHANGED rightChopsticks)

handleLeftChopstickReply(n) == states[n] = "waitingForLeft" /\
                               \/ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "leftChopstickReplyAccept")
                                        /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "holding"]
                                        /\ states' = [states EXCEPT ![n] = "waitingForRight"]
                                        /\ messages' = (messages \union { [ from |-> n, to |-> rightIndex(n), type |-> "rightChopstickRequest" ] }) \ { [ from |-> leftIndex(n), to |-> n, type |-> "leftChopstickReplyAccept" ] }
                                        /\ UNCHANGED rightChopsticks
                               \/ (\E m \in messages:
                                        /\ m.to = n
                                        /\ m.type = "leftChopstickReplyDeny"
                                        /\ states' = [states EXCEPT ![n] = "thinking"]
                                        /\ messages' = messages \ { [ from |-> leftIndex(n), to |-> n, type |-> "leftChopstickReplyDeny" ] }
                                        /\ UNCHANGED << rightChopsticks, leftChopsticks >>)

stopEating(n) == 
\*                 /\ states[n] = "eating"
                 /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "notHolding"]
                 /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
                 /\ states' = [states EXCEPT ![n] = "thinking"]
                 /\ UNCHANGED messages

Next == \/ \E n \in 1..N:
            \/ tryToEat(n)
            \/ handleRightChopstickRequest(n)
            \/ handleLeftChopstickRequest(n)
            \/ handleRightChopstickReply(n)
            \/ handleLeftChopstickReply(n)
            \/ stopEating(n)

Stop == Len(SelectSeq(states, LAMBDA x: x = "eating")) = 3

AdjacentPeopleEating == \E n \in 1..N:
                            /\ states[n] = "eating"
                            /\ states[rightIndex(n)] = "eating"

TwoPeopleHoldingChopstick == \E n \in 1..N:
                                /\ rightChopsticks[n] = "holding"
                                /\ leftChopsticks[rightIndex(n)] = "holding"

=============================================================================
\* Modification History
\* Last modified Thu May 05 00:54:24 EDT 2022 by luke
\* Created Wed May 04 10:44:57 EDT 2022 by luke
