------------------------- MODULE DiningPhilosophers -------------------------

EXTENDS Integers

CONSTANT N

VARIABLES states, chopsticks

TypeOK == \A n \in 0..N-1:
            /\ states[n] \in {"thinking", "hungry", "eating"}
            /\ chopsticks[n] \in {"available", "heldByLeft", "heldByRight"}

Init == /\ states = [n \in 0..N-1 |-> "thinking"]
        /\ chopsticks = [n \in 0..N-1 |-> "available"]

rightIndex(n) == n
leftIndex(n) == (n-1) % N

hunger(n) == /\ states[n] = "thinking"
             /\ states' = [states EXCEPT ![n] = "hungry"]
             /\ chopsticks' = chopsticks

think(n) == /\ states[n] = "hungry"
            /\ chopsticks[rightIndex(n)] /= "heldByLeft"
            /\ chopsticks[leftIndex(n)] /= "heldByRight"
            /\ states' = [states EXCEPT ![n] = "thinking"]
            /\ chopsticks' = chopsticks

pickUpRightChopstick(n) == /\ chopsticks[rightIndex(n)] = "available"
                           /\ states[n] = "hungry"
                           /\ states' = states
                           /\ chopsticks' = [chopsticks EXCEPT ![rightIndex(n)] = "heldByLeft"]

pickUpLeftChopstick(n) == /\ chopsticks[leftIndex(n)] = "available"
                          /\ states[n] = "hungry"
                          /\ states' = states
                          /\ chopsticks' = [chopsticks EXCEPT ![leftIndex(n)] = "heldByRight"]

putDownRightChopstick(n) == /\ chopsticks[rightIndex(n)] = "heldByLeft"
                            /\ states[n] = "hungry"
                            /\ states' = states
                            /\ chopsticks' = [chopsticks EXCEPT ![rightIndex(n)] = "available"]

putDownLeftChopstick(n) == /\ chopsticks[leftIndex(n)] = "heldByRight"
                           /\ states[n] = "hungry"
                           /\ states' = states
                           /\ chopsticks' = [chopsticks EXCEPT ![leftIndex(n)] = "available"]

eat(n) == /\ states[n] = "hungry"
          /\ chopsticks[rightIndex(n)] = "heldByLeft"
          /\ chopsticks[leftIndex(n)] = "heldByRight"
          /\ states' = [states EXCEPT ![n] = "eating"]
          /\ chopsticks' = chopsticks

stopEating(n) == /\ states[n] = "eating"
                 /\ states' = [states EXCEPT ![n] = "hungry"]
                 /\ chopsticks' = chopsticks

Next == \/ \E n \in 0..N-1:
            \/ hunger(n)
            \/ think(n)
            \/ pickUpRightChopstick(n)
            \/ pickUpLeftChopstick(n)
            \/ putDownRightChopstick(n)
            \/ putDownLeftChopstick(n)
            \/ eat(n)
            \/ stopEating(n)

AdjacentPeopleEating == \E n \in 0..N-1:
                            /\ states[rightIndex(n)] = "eating"
                            /\ states[leftIndex(n)] = "eating" 

=============================================================================
