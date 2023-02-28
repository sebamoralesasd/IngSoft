------------------------------ MODULE tanques ------------------------------
EXTENDS Naturals, Sequences
VARIABLES curr_blanco, lista_blancos, pantalla, hay_conflicto, zona_seteada
CONSTANT MAXTARGET, zona_conflicto
ASSUME MAXTARGET \in Nat /\ MAXTARGET > 0

Pos == (Nat \times Nat) \cup <<>>
ASSUME zona_conflicto \subseteq (Nat \times Nat) /\ zona_conflicto /= {}

vars == <<curr_blanco, lista_blancos, pantalla, hay_conflicto, zona_seteada>>
----------------------------------------------------------------------------
TypeInv == /\ curr_blanco \in Pos
           /\ lista_blancos \in Seq(Pos)
           /\ pantalla \in Seq(Pos)
           /\ hay_conflicto \in BOOLEAN
           /\ zona_seteada \in {0, 1}
           
Init == /\ curr_blanco = <<>>
        /\ lista_blancos = <<>>
        /\ pantalla = <<>>
        /\ hay_conflicto = FALSE
        /\ zona_seteada = 0
        
Blanco(p) == /\ curr_blanco = <<>>
             /\ curr_blanco' = p
             /\ UNCHANGED <<lista_blancos, pantalla, hay_conflicto, zona_seteada>>

Zona == /\ curr_blanco /= <<>>
        /\ zona_seteada = 0
        /\ hay_conflicto' = (curr_blanco \in zona_conflicto)
        /\ zona_seteada' = 1
        /\ UNCHANGED <<curr_blanco, pantalla, lista_blancos>>
        
Accept == /\ curr_blanco /= <<>>
          /\ zona_seteada = 1
          /\ Len(lista_blancos) < MAXTARGET
          /\ lista_blancos' = Append(lista_blancos, curr_blanco)
          /\ curr_blanco' = <<>>
          /\ zona_seteada' = 0
          /\ UNCHANGED <<pantalla, hay_conflicto>>

Pantalla == /\ pantalla' = lista_blancos
            /\ UNCHANGED <<lista_blancos, hay_conflicto, curr_blanco, zona_seteada>>

Reject == /\ curr_blanco /= <<>>
          /\ zona_seteada = 1
          /\ \/ hay_conflicto = TRUE
             \/ Len(lista_blancos) >= MAXTARGET
          /\ curr_blanco' = <<>>
          /\ zona_seteada' = 0
          /\ UNCHANGED <<lista_blancos, pantalla, hay_conflicto>>

Next == (\E p \in (Nat \times Nat) : Blanco(p)) \/ Zona \/ Accept \/ Pantalla \/ Reject

Fairness == WF_vars(Accept) /\ WF_vars(Pantalla) /\ WF_vars(Zona)
Safety == Init /\ [][Next]_vars

Spec == Safety /\ Fairness
----------------------------------------------------------------------------
THEOREM Spec => TypeInv

=============================================================================
\* Modification History
\* Last modified Mon Feb 20 19:07:21 ART 2023 by sebapc
\* Created Sat Feb 18 18:44:52 ART 2023 by sebapc
