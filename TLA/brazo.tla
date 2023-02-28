------------------------------- MODULE brazo -------------------------------
EXTENDS Naturals
CONSTANTS Tir, Text, Tdet, bot, Boton
ASSUME /\ (Tir \in Nat) /\ (Tir > 0)
       /\ (Text \in Nat) /\ (Text > 0)
       /\ (Tdet \in Nat) /\ (Tdet > 0)
       /\ bot \in Boton

VARIABLES time, running, limit, now, elapsed, last_ext, dir, curr_pos, b_status

vars == <<time, running, limit, elapsed, now, last_ext, dir, curr_pos, b_status>>

TypeInv == /\ time \in Nat 
           /\ now \in Nat 
           /\ limit \in Nat
           /\ elapsed \in Nat 
           /\ running \in {"yes", "no"}
           /\ last_ext \in {"izq","der"}
           /\ dir \in {"izq","der"}
           /\ curr_pos \in {"izq", "mid", "der"}
           /\ b_status \in {"stop", "moving", "waiting_timer", 
                            "timer_set", "waiting_return_timer", 
                            "waiting_continue_timer", "waiting_start_timer"}

Ts == INSTANCE timer

Init == /\ Ts!TInit
        /\ b_status = "stop"
        /\ elapsed = 0
        /\ last_ext = "der"
        /\ dir = "izq"
        /\ curr_pos = "der"

\*El brazo se mueve
Mover == /\ b_status = "stop"
         /\ Ts!Start
         /\ b_status' = "moving"
         /\ curr_pos' = "mid"
         /\ UNCHANGED <<elapsed, last_ext, dir>>

\*El operario aprieta el botón b para detener el brazo entre los extremos
StopMid(b) == /\ b = bot
              /\ b_status = "moving"
              /\ curr_pos = "mid"
              /\ Ts!Stop
              /\ elapsed' = now - time
              /\ b_status = "waiting_timer"
              /\ UNCHANGED <<curr_pos, last_ext, dir>>

\*Se configura el tiempo del brazo en reposo entre los extremos
SetIdleMid == /\ b_status = "waiting_timer"
              /\ curr_pos = "mid"
              /\ Ts!Set(Tdet)
              /\ b_status' = "timer_set"
              /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El brazo queda en reposo entre los extremos
IdleMid == /\ b_status = "timer_set"
           /\ curr_pos = "mid"
           /\ Ts!Start
           /\ b_status' = "stop"
           /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El brazo supera el tiempo de reposo entre los extremos
TOIdleMid == /\ b_status = "stop"
             /\ curr_pos = "mid"
             /\ Ts!Timeout
             /\ b_status' = "waiting_return_timer"
             /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*Se configura el brazo para que retorne al último extremo visitado desde el medio
SetReturnMid == /\ b_status = "waiting_return_timer"
                /\ curr_pos = "mid"
                /\ Ts!Set(elapsed)
                /\ dir' = last_ext
                /\ b_status' = "stop"
                /\ UNCHANGED <<elapsed, last_ext, curr_pos>>

\*El operario reanuda el movimiento desde el medio apretando el botón b
BotonMover(b) == /\ b = bot
                 /\ b_status = "stop"
                 /\ curr_pos = "mid"
                 /\ Ts!Stop
                 /\ b_status' = "waiting_continue_timer"
                 /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*Se configura el brazo para que reanude su movimiento
SetMover == /\ b_status = "waiting_continue_timer"
            /\ curr_pos = "mid"
            /\ Ts!Set(Tir - elapsed)
            /\ b_status' = "stop"
            /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El brazo llega a un extremo
LlegaExt == /\ curr_pos = "mid"
            /\ b_status = "moving"
            /\ Ts!Timeout
            /\ curr_pos' = dir
            /\ last_ext' = dir
            /\ dir' = CHOOSE x \in {"izq", "der"} : x /= dir
            /\ b_status' = "waiting_timer"
            /\ UNCHANGED <<elapsed>>

\*Se configura el tiempo del brazo en reposo en un extremo
SetIdleExt == /\ curr_pos /= "mid"
              /\ b_status = "waiting_timer"
              /\ Ts!Set(Text)
              /\ b_status' = "timer_set"
              /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El brazo queda en reposo en un extremo
IdleExt == /\ curr_pos /= "mid"
           /\ b_status = "timer_set"
           /\ Ts!Start
           /\ b_status' = "stop"
           /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El brazo supera el tiempo de reposo en un extremo
TOIdleExt == /\ curr_pos /= "mid"
             /\ b_status = "stop"
             /\ Ts!Timeout
             /\ b_status' = "waiting_start_timer"
             /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*Se configura el brazo para que se mueva hacia el extremo opuesto
SetReturn == /\ curr_pos /= "mid"
             /\ b_status = "waiting_start_timer"
             /\ Ts!Set(Tir)
             /\ b_status' = "stop"
             /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

\*El operario reanuda el movimiento desde un extremo apretando el botón b
BotonMoverExtremo(b) == /\ b = bot
                        /\ curr_pos /= "mid"
                        /\ b_status = "stop"
                        /\ Ts!Stop
                        /\ b_status' = "waiting_start_timer"
                        /\ UNCHANGED <<elapsed, last_ext, dir, curr_pos>>

Next == Mover \/ SetIdleMid \/ IdleMid \/ TOIdleMid 
        \/ SetReturnMid \/ SetMover \/ LlegaExt
        \/ SetIdleExt \/ IdleExt \/ TOIdleExt \/ SetReturn
        \/ \E b \in Boton : BotonMover(b) \/ StopMid(b) \/ BotonMoverExtremo(b)

Safety == Init /\ [][Next]_vars

Fairness == WF_vars(Mover) /\ WF_vars(SetIdleMid) /\ WF_vars(IdleMid) 
            /\ WF_vars(SetReturnMid) 
            /\ WF_vars(SetMover) /\ WF_vars(LlegaExt) 
            /\ WF_vars(SetIdleExt) /\ WF_vars(IdleExt) 
            /\ WF_vars(SetReturn)
    
Spec == Safety /\ Fairness

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInv
=============================================================================
\* Modification History
\* Last modified Thu Feb 23 19:24:35 ART 2023 by sebapc
\* Created Wed Feb 22 20:29:05 ART 2023 by sebapc
