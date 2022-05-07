--------------------------- MODULE BrazoMecanico ---------------------------
(*EXTENDS timer
CONSTANTS tIr, tDet, tExt
ASSUME /\ tIr \in Nat 
       /\ tIr > 0
       /\ tDet \in Nat 
       /\ tDet > 0
       /\ tExt \in Nat 
       /\ tExt > 0
       *)
VARIABLES direccion, pos, bRunning \*, timeElapsed

vr == <<direccion, pos, bRunning>> \*, timeElapsed>>
ar == <<pos, direccion>>

TypeInv == /\ direccion \in {"izq", "der"}
           /\ pos \in {"izq", "der", "mid"}
           /\ bRunning \in {"yes", "no"}
-----------------------------------------------------------------------------

Init == /\ TypeInv
        /\ direccion = "izq"
        /\ pos = "izq"
        /\ bRunning = "no"
        
MoveTo(p) == /\ direccion /= p
             /\ bRunning = "no"
             /\ bRunning' = "yes"
             /\ direccion' = p
             /\ pos' = "mid"
             
Extremo(p) == /\ pos = "mid"
              /\ direccion = p
              /\ bRunning = "yes"
              /\ bRunning' = "no"
              /\ pos' = p
              /\ direccion' = CHOOSE x \in {"izq", "der"} : x /= p

StopMid == /\ pos = "mid"
           /\ bRunning = "yes"
           /\ bRunning' = "no"
           /\ UNCHANGED ar
           
Reanudar == /\ pos = "mid"
            /\ bRunning = "no"
            /\ bRunning' = "yes"
            /\ UNCHANGED ar

BStop == StopMid \/ Extremo(direccion)

Boton == BStop \/ Reanudar

Next == Boton \/ (\E p \in {"izq", "der"} : MoveTo(p) \/ Extremo(p))

Spec == Init /\ [][Next]_vr /\ WF_vr(Next)
             
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInv

=============================================================================
\* Modification History
\* Last modified Mon Feb 28 20:10:25 ART 2022 by sebapc
\* Created Sun Feb 27 21:47:50 ART 2022 by sebapc
