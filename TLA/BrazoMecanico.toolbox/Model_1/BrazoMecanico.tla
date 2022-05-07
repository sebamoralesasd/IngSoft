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
VARIABLES direccion, pos, bRunning \*, boton , timeElapsed

vr == <<direccion, pos, bRunning>> \*, timeElapsed>>
ar == <<pos, direccion>>

TypeInv == /\ direccion \in {"izq", "der"}
           /\ pos \in {"izq", "der", "mid"}
           /\ bRunning \in {"yes", "no"}
\*           /\ boton \in {0, 1}
-----------------------------------------------------------------------------

Init == /\ direccion = "der"
        /\ pos = "izq"
        /\ bRunning = "no"
\*        /\ boton = 0
        
Avanzar == /\ bRunning = "no"
           /\ bRunning' = "yes"
           /\ pos' = "mid"
           /\ UNCHANGED direccion
             
Extremo == /\ pos = "mid"
           /\ bRunning = "yes"
           /\ bRunning' = "no"
           /\ pos' = direccion
           /\ direccion' = CHOOSE x \in {"izq", "der"} : x /= direccion
              
Retornar == /\ pos = "mid"
            /\ bRunning = "no"
            /\ bRunning' = "yes"
            /\ direccion' = CHOOSE x \in {"izq", "der"} : x /= direccion
            /\ UNCHANGED pos

StopMid == /\ pos = "mid"
           /\ bRunning = "yes"
           /\ bRunning' = "no"
           /\ UNCHANGED ar

Next == Avanzar \/ Extremo \/ Retornar \/ StopMid

Spec == Init /\ [][Next]_vr \* /\ WF_vr(Next)
             
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInv

=============================================================================
\* Modification History
\* Last modified Sat May 07 18:45:20 ART 2022 by sebapc
\* Created Sun Feb 27 21:47:50 ART 2022 by sebapc
