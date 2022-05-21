Included are three TLA+ specs to model the dining philosophers
problem. It would be rather difficult to run these, as you would need
to get the TLA+ toolbox set up locally. The three specs are as follows

1. DiningPhilosophers - most basic, does not model the message passing at
all, philosophers can just see the state of adjacent philosophers

2. DiningPhilosophersWithRequests - add chopstick request and response
messages to make this model more realistic

3. DiningPhilosophersOrderedMessages - enforce the property that
messages sent from a process to another are received in the order they
are sent

The last of these, DiningPhilosophersOrderedMessages, is the most
complete spec.
