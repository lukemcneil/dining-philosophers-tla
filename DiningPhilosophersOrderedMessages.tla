----------------- MODULE DiningPhilosophersOrderedMessages -----------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

VARIABLES states, rightChopsticks, leftChopsticks, messagesGoingLeft, messagesGoingRight

vars == << states, rightChopsticks, leftChopsticks, messagesGoingLeft, messagesGoingRight >>

SeqToSet(seq) == {seq[i]: i \in DOMAIN seq}

IsInSeq(seq, e) == e \in SeqToSet(seq)

TypeOK ==/\ (\A n \in 1..N:
           /\ states[n] \in {"thinking", "waitingForRight", "waitingForLeft", "eating"}
           /\ rightChopsticks[n] \in {"notHolding", "holding"}
           /\ leftChopsticks[n] \in {"notHolding", "holding"})
           /\ (\A n \in 1..N:
             LET asSet == SeqToSet(messagesGoingLeft[n]) IN
               \A m \in asSet:
                m \in {"leftChopstickRequest", "rightChopstickReplyAccept", "rightChopstickReplyDeny"})
           /\ (\A n \in 1..N:
             LET asSet == SeqToSet(messagesGoingRight[n]) IN
               \A m \in asSet:
                m \in {"rightChopstickRequest", "leftChopstickReplyAccept", "leftChopstickReplyDeny"})

Init == /\ states = [n \in 1..N |-> "thinking"]
        /\ rightChopsticks = [n \in 1..N |-> "notHolding"]
        /\ leftChopsticks = [n \in 1..N |-> "notHolding"]
        /\ messagesGoingLeft = [n \in 1..N |-> << >>]
        /\ messagesGoingRight = [n \in 1..N |-> << >>]

rightIndex(n) == IF n = N THEN 1 ELSE n+1
leftIndex(n) == IF n = 1 THEN N ELSE n-1

tryToEat(n) == 
  /\ ~IsInSeq(messagesGoingLeft[leftIndex(n)], "leftChopstickRequest")
  /\ states[n] = "thinking"
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![leftIndex(n)] = Append(messagesGoingLeft[leftIndex(n)], "leftChopstickRequest")]
  /\ states' = [states EXCEPT ![n] = "waitingForLeft"]
  /\ UNCHANGED << rightChopsticks, leftChopsticks, messagesGoingRight >>

IsFirst(seq, e) ==
  /\ Len(seq) > 0
  /\ Head(seq) = e

acceptRightChopstickRequest(n) == 
  /\ ~IsInSeq(messagesGoingLeft[leftIndex(n)], "rightChopstickReplyAccept")
  /\ IsFirst(messagesGoingRight[n], "rightChopstickRequest")
  /\ leftChopsticks[n] = "notHolding"
  /\ states[n] /= "waitingForLeft"
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![n] = Tail(messagesGoingRight[n])]
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![leftIndex(n)] = Append(messagesGoingLeft[leftIndex(n)], "rightChopstickReplyAccept")]
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>
                                  
denyRightChopstickRequest(n) == 
  LET req == [ from |-> leftIndex(n), to |-> n, type |-> "rightChopstickRequest" ] 
      resp == [ from |-> n, to |-> leftIndex(n), type |-> "rightChopstickReplyDeny" ] IN
  /\ ~IsInSeq(messagesGoingLeft[leftIndex(n)], "rightChopstickReplyDeny")
  /\ IsFirst(messagesGoingRight[n], "rightChopstickRequest")
  /\ (leftChopsticks[n] = "holding" \/ states[n] = "waitingForLeft")
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![n] = Tail(messagesGoingRight[n])]
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![leftIndex(n)] = Append(messagesGoingLeft[leftIndex(n)], "rightChopstickReplyDeny")]
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>

acceptLeftChopstickRequest(n) ==
  /\ ~IsInSeq(messagesGoingRight[rightIndex(n)], "leftChopstickReplyAccept")
  /\ IsFirst(messagesGoingLeft[n], "leftChopstickRequest")
  /\ rightChopsticks[n] = "notHolding"
  /\ states[n] /= "waitingForRight"
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![n] = Tail(messagesGoingLeft[n])]
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![rightIndex(n)] = Append(messagesGoingRight[rightIndex(n)], "leftChopstickReplyAccept")]
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>
                                  
denyLeftChopstickRequest(n) ==
  /\ ~IsInSeq(messagesGoingRight[rightIndex(n)], "leftChopstickReplyDeny") 
  /\ IsFirst(messagesGoingLeft[n], "leftChopstickRequest")
  /\ (rightChopsticks[n] = "holding" \/ states[n] = "waitingForRight")
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![n] = Tail(messagesGoingLeft[n])]
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![rightIndex(n)] = Append(messagesGoingRight[rightIndex(n)], "leftChopstickReplyDeny")]
  /\ UNCHANGED << states, rightChopsticks, leftChopsticks >>

handleRightChopstickAccept(n) ==
  /\ IsFirst(messagesGoingLeft[n], "rightChopstickReplyAccept")
  /\ states[n] = "waitingForRight"
  /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "holding"]
  /\ states' = [states EXCEPT ![n] = "eating"]
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![n] = Tail(messagesGoingLeft[n])]
  /\ UNCHANGED << leftChopsticks, messagesGoingRight >>

handleRightChopstickDeny(n) ==
  /\ IsFirst(messagesGoingLeft[n], "rightChopstickReplyDeny")
  /\ states[n] = "waitingForRight"
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![n] = Tail(messagesGoingLeft[n])]
  /\ UNCHANGED << rightChopsticks, messagesGoingRight >>

ignoreRightChopstickReply(n) ==
  /\ (IsFirst(messagesGoingLeft[n], "rightChopstickReplyAccept") \/ IsFirst(messagesGoingLeft[n], "rightChopstickReplyDeny"))
  /\ states[n] /= "waitingForRight"
  /\ messagesGoingLeft' = [messagesGoingLeft EXCEPT ![n] = Tail(messagesGoingLeft[n])]
  /\ UNCHANGED << rightChopsticks, leftChopsticks, messagesGoingRight, states >>

handleLeftChopstickAccept(n) ==
  /\ IsFirst(messagesGoingRight[n], "leftChopstickReplyAccept")
  /\ ~IsInSeq(messagesGoingRight[rightIndex(n)], "rightChopstickRequest")
  /\ states[n] = "waitingForLeft"
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "holding"]
  /\ states' = [states EXCEPT ![n] = "waitingForRight"]
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![n] = Tail(messagesGoingRight[n]),
                                                      ![rightIndex(n)] = Append(messagesGoingRight[rightIndex(n)], "rightChopstickRequest")]
  /\ UNCHANGED << rightChopsticks, messagesGoingLeft >>

handleLeftChopstickDeny(n) ==
  /\ IsFirst(messagesGoingRight[n], "leftChopstickReplyDeny")
  /\ states[n] = "waitingForLeft"
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![n] = Tail(messagesGoingRight[n])]
  /\ UNCHANGED << rightChopsticks, leftChopsticks, messagesGoingLeft >>

ignoreLeftChopstickReply(n) ==
  /\ (IsFirst(messagesGoingRight[n], "leftChopstickReplyAccept") \/ IsFirst(messagesGoingRight[n], "leftChopstickReplyDeny"))
  /\ states[n] /= "waitingForLeft"
  /\ messagesGoingRight' = [messagesGoingRight EXCEPT ![n] = Tail(messagesGoingRight[n])]
  /\ UNCHANGED << rightChopsticks, leftChopsticks, messagesGoingLeft, states >>

stopEating(n) == 
\*  /\ states[n] = "eating"
  /\ rightChopsticks' = [rightChopsticks EXCEPT ![n] = "notHolding"]
  /\ leftChopsticks' = [leftChopsticks EXCEPT ![n] = "notHolding"]
  /\ states' = [states EXCEPT ![n] = "thinking"]
  /\ UNCHANGED << messagesGoingLeft, messagesGoingRight >>

Next == \/ \E n \in 1..N:
            \/ tryToEat(n)
            \/ acceptRightChopstickRequest(n)
            \/ denyRightChopstickRequest(n)
            \/ acceptLeftChopstickRequest(n)
            \/ denyLeftChopstickRequest(n)
            \/ handleRightChopstickAccept(n)
            \/ handleRightChopstickDeny(n)
            \/ ignoreRightChopstickReply(n)
            \/ handleLeftChopstickAccept(n)
            \/ handleLeftChopstickDeny(n)
            \/ ignoreLeftChopstickReply(n)
            \/ stopEating(n)

Stop == 
\*\E n \in 1..N:
\*            Len(messagesGoingRight[n]) = 4
Len(SelectSeq(states, LAMBDA x: x = "eating")) = 3

EveryoneEventuallyEats ==
  \A n \in 1..N:
    states[n] = "eating" ~> states[rightIndex(n)] = "eating"

AdjacentPeopleEating == \E n \in 1..N:
                            /\ states[n] = "eating"
                            /\ states[rightIndex(n)] = "eating"

TwoPeopleHoldingChopstick == \E n \in 1..N:
                                /\ rightChopsticks[n] = "holding"
                                /\ leftChopsticks[rightIndex(n)] = "holding"

Spec == /\ Init 
        /\ [][Next]_vars
        /\ (\A n \in 1..N:
           /\ WF_vars(tryToEat(n))
           /\ SF_vars(acceptRightChopstickRequest(n))
           /\ WF_vars(denyRightChopstickRequest(n))
           /\ WF_vars(acceptLeftChopstickRequest(n))
           /\ WF_vars(denyLeftChopstickRequest(n))
           /\ WF_vars(handleRightChopstickAccept(n))
           /\ WF_vars(handleRightChopstickDeny(n))
           /\ WF_vars(ignoreRightChopstickReply(n))
           /\ WF_vars(handleLeftChopstickAccept(n))
           /\ WF_vars(handleLeftChopstickDeny(n))
           /\ WF_vars(ignoreLeftChopstickReply(n))
           /\ WF_vars(stopEating(n)))

=============================================================================
\* Modification History
\* Last modified Fri May 13 12:54:22 EDT 2022 by luke
\* Created Thu May 12 22:41:30 EDT 2022 by luke
