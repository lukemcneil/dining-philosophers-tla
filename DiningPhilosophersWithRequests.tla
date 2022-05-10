------------------- MODULE DiningPhilosophersWithRequests -------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

VARIABLES states, rightChopsticks, leftChopsticks, messages

TypeOK ==/\ (\A n \in 1..N:
           /\ states[n] \in {"thinking", "waitingForRight", "waitingForLeft", "eating"}
           /\ rightChopsticks[n] \in {"notHolding", "holding"}
           /\ leftChopsticks[n] \in {"notHolding", "holding"})
         /\ (\A m \in messages:
           /\ m.to \in 1..N
           /\ m.from \in 1..N
           /\ m.type \in {"rightChopstickRequest", "leftChopstickRequest", "rightChopstickReplyAccept",
                      "leftChopstickReplyAccept", "rightChopstickReplyDeny", "leftChopstickReplyDeny"})

Init == /\ states = [n \in 1..N |-> "thinking"]
        /\ rightChopsticks = [n \in 1..N |-> "notHolding"]
        /\ leftChopsticks = [n \in 1..N |-> "notHolding"]
        /\ messages = {}

rightIndex(n) == IF n = N THEN 1 ELSE n+1
leftIndex(n) == IF n = 1 THEN N ELSE n-1

tryToEat(n) == LET m == [ from |-> n, to |-> leftIndex(n), type |-> "leftChopstickRequest" ] IN
               /\ states[n] = "thinking"
               /\ messages' = messages \union {m}
               /\ states' = [states EXCEPT ![n] = "waitingForLeft"]
               /\ UNCHANGED << rightChopsticks, leftChopsticks >>

acceptRightChopstickRequest(n) == 
  LET req == [ from |-> leftIndex(n), to |-> n, type |-> "rightChopstickRequest" ] 
      resp == [ from |-> n, to |-> leftIndex(n), type |-> "rightChopstickReplyAccept" ] IN
  /\ req \in messages
  /\ leftChopsticks[n] = "notHolding"
  /\ states[n] /= "waitingForLeft"
  /\ messages' = (messages \union {resp}) \ {req}
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>
                                  
denyRightChopstickRequest(n) == 
  LET req == [ from |-> leftIndex(n), to |-> n, type |-> "rightChopstickRequest" ] 
      resp == [ from |-> n, to |-> leftIndex(n), type |-> "rightChopstickReplyDeny" ] IN
  /\ req \in messages
  /\ (leftChopsticks[n] = "holding" \/ states[n] = "waitingForLeft")
  /\ messages' = (messages \union {resp}) \ {req}
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>
       
acceptLeftChopstickRequest(n) == 
  LET req == [ from |-> rightIndex(n), to |-> n, type |-> "leftChopstickRequest" ] 
      resp == [ from |-> n, to |-> rightIndex(n), type |-> "leftChopstickReplyAccept" ] IN
  /\ req \in messages
  /\ rightChopsticks[n] = "notHolding"
  /\ states[n] /= "waitingForRight"
  /\ messages' = (messages \union {resp}) \ {req}
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>
                                  
denyLeftChopstickRequest(n) == 
  LET req == [ from |-> rightIndex(n), to |-> n, type |-> "leftChopstickRequest" ] 
      resp == [ from |-> n, to |-> rightIndex(n), type |-> "leftChopstickReplyDeny" ] IN
  /\ req \in messages
  /\ (rightChopsticks[n] = "holding" \/ states[n] = "waitingForRight")
  /\ messages' = (messages \union {resp}) \ {req}
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>

handleRightChopstickAccept(n) ==
  LET reply ==  [ from |-> rightIndex(n), to |-> n, type |-> "rightChopstickReplyAccept" ] IN
  /\ reply \in messages
  /\ states[n] = "waitingForRight"
  /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "holding"]
  /\ states' = [states EXCEPT ![n] = "eating"]
  /\ messages' = messages \ {reply}
  /\ UNCHANGED leftChopsticks

handleRightChopstickDeny(n) ==
  LET reply ==  [ from |-> rightIndex(n), to |-> n, type |-> "rightChopstickReplyDeny" ] IN
  /\ reply \in messages
  /\ states[n] = "waitingForRight"
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
  /\ messages' = messages \ {reply}
  /\ UNCHANGED rightChopsticks

handleLeftChopstickAccept(n) ==
  LET reply ==  [ from |-> leftIndex(n), to |-> n, type |-> "leftChopstickReplyAccept" ]
      req == [ from |-> n, to |-> rightIndex(n), type |-> "rightChopstickRequest" ] IN
  /\ reply \in messages
  /\ states[n] = "waitingForLeft"
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "holding"]
  /\ states' = [states EXCEPT ![n] = "waitingForRight"]
  /\ messages' = (messages \union {req}) \ {reply}
  /\ UNCHANGED rightChopsticks

handleLeftChopstickDeny(n) ==
  LET reply ==  [ from |-> leftIndex(n), to |-> n, type |-> "leftChopstickReplyDeny" ] IN
  /\ reply \in messages
  /\ states[n] = "waitingForLeft"
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ messages' = messages \ {reply}
  /\ UNCHANGED << rightChopsticks, leftChopsticks >>

stopEating(n) == 
\*  /\ states[n] = "eating"
  /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "notHolding"]
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ UNCHANGED messages

Next == \/ \E n \in 1..N:
            \/ tryToEat(n)
            \/ acceptRightChopstickRequest(n)
            \/ denyRightChopstickRequest(n)
            \/ acceptLeftChopstickRequest(n)
            \/ denyLeftChopstickRequest(n)
            \/ handleRightChopstickAccept(n)
            \/ handleRightChopstickDeny(n)
            \/ handleLeftChopstickAccept(n)
            \/ handleLeftChopstickDeny(n)
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
\* Last modified Tue May 10 12:42:02 EDT 2022 by luke
\* Created Wed May 04 10:44:57 EDT 2022 by luke
