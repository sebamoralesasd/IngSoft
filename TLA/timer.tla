------------------------------- MODULE timer -------------------------------
EXTENDS Naturals, RealTime
VARIABLES time, running, limit

TTypeInv == /\ time \in Nat
            /\ limit \in Nat 
            /\ running \in {"yes", "no"}

av == <<limit, time, running>>            
sv == <<limit, time, running, now>>
-----------------------------------------------------------------------------

TInit == limit = 0 /\ running = "no"

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

TNext == Start \/ Stop \/ Timeout \/ (\E t \in Nat : Set(t))
TSpec == TInit /\ [][TNext]_sv /\ RTBound(Timeout, av, 0, 1)
-----------------------------------------------------------------------------
THEOREM TSpec => []TTypeInv

=============================================================================

----------------------------- MODULE RealTime -------------------------------

(* Teóricamente RealTime es una librería del toolbox pero por alguna razón *)
(* no está siendo leída. Borrar en caso de que esto ocurra. *)
EXTENDS Reals, Naturals
VARIABLES now
-----------------------------------------------------------------------------
(* Estas definiciones son de DK_RealTime. Se agregaron a este modulo porque *)
(* extenderlo desde aquel era un quilombo. *)
RTTypeInv == now \in Nat
RTInit == now = 0
Tick == now' = now + 1
RTSpec == RTInit /\ WF_now(Tick)
-----------------------------------------------------------------------------
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
\* Last modified Sun Feb 27 21:36:48 ART 2022 by sebapc
\* Created Sun Feb 27 20:21:57 ART 2022 by sebapc
