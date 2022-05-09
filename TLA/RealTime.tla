----------------------------- MODULE RealTime -------------------------------
EXTENDS Reals, Naturals
VARIABLE now

(* DK_RealTime. *)
RTTypeInv == now \in Nat
RTInit == now = 0
Tick == now' = now + 1
RTSpec == RTInit /\ [][Tick]_now /\ WF_now(Tick)
(* DK_RealTime. *)

RTBound(A, v, D, E) == 
  LET TNext(t)  ==  t' = IF <<A>>_v \/ ~(ENABLED <<A>>_v)'
                           THEN 0 
                           ELSE t + (now'-now)

      Timer(t) == (t=0)  /\  [][TNext(t)]_<<t, v, now>>

      MaxTime(t) == [](t \leq E) 

      MinTime(t) == [][A => t \geq D]_v 
  IN \EE t : Timer(t) /\ MaxTime(t) /\ MinTime(t)
-----------------------------------------------------------------------------
RTnow(v) == LET NowNext == /\ now' \in {r \in Real : r > now} 
                           /\ UNCHANGED v
            IN  /\ now \in Real 
                /\ [][NowNext]_now
                /\ \A r \in Real : WF_now(NowNext /\ (now'>r))
-----------------------------------------------------------------------------
THEOREM RTSpec => []RTTypeInv

=============================================================================
\* Modification History
\* Last modified Mon May 09 17:32:20 ART 2022 by sebapc
\* Created Sun May 08 17:49:47 ART 2022 by sebapc
