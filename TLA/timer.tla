------------------------------- MODULE timer -------------------------------
EXTENDS Naturals, RealTime
VARIABLES time, running, limit

TTypeInv == /\ time \in Nat
            /\ limit \in Nat 
            /\ running \in {"yes", "no"}

sv == <<limit, time, running>>
av == <<limit, time, running, now>>

-----------------------------------------------------------------------------
TInit == limit = 0 /\ running = "no" /\ now = 0 /\ time = now

Set(l) == /\ l > 0
          /\ running = "no"
          /\ limit' = l
          /\ UNCHANGED <<time, now, running>>

Start == /\ running = "no"
         /\ limit > 0
         /\ time' = now
         /\ running' = "yes"
         /\ UNCHANGED <<now, limit>>
         
Timeout == /\ running = "yes"
           /\ now - time \geq limit
           /\ running' = "no"
           /\ UNCHANGED <<now, time, limit>>

Stop == /\ running = "yes"
        /\ running' = "no"
        /\ UNCHANGED <<now, time, limit>>

TNext == Start \/ Stop \/ Timeout \/ \E t \in Nat : Set(t)
TSpec == TInit /\ [][TNext]_sv /\ RTBound(Timeout, av, 0, 1) /\ RTSpec
-----------------------------------------------------------------------------
THEOREM TSpec => []TTypeInv

=============================================================================
\* Modification History
\* Last modified Mon May 09 20:19:08 ART 2022 by sebapc
\* Created Sun Feb 27 20:21:57 ART 2022 by sebapc
