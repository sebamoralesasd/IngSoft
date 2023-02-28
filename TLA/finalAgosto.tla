---------------------------- MODULE finalAgosto ----------------------------
EXTENDS Naturals
VARIABLES armado, bocina

TypeSensor == {"mag", "ab"}
Digitos == 0..9
Clave == <<CHOOSE x \in Digitos : x \in Digitos, CHOOSE y \in Digitos : y \in Digitos>>

TypeInv == /\ armado \in {0, 1}
           /\ bocina \in {0, 1}
           
vars == <<armado, bocina>>
-----------------------------------------------------------------------------
TInit == armado = 0 /\ bocina = 0

Codigo(p) == p = Clave

ArmarOp == /\ armado = 0
           /\ armado' = 1

Armar(p) == Codigo(p) /\ ArmarOp

\* La diferencia con Armar es que (SoloArmar) representa el caso en donde
\* simplemente se quiere armar el sistema desarmado.
SoloArmar(p) == Armar(p) /\ UNCHANGED <<bocina>>

DesarmarOp == /\ armado = 1
              /\ armado' = 0
            
Desarmar(p) == Codigo(p) /\ DesarmarOp

\* La diferencia con Desarmar es que (SoloDesarmar) representa el caso en donde
\* simplemente se quiere desarmar el sistema armado.
SoloDesarmar(p) == Desarmar(p) /\ UNCHANGED <<bocina>>

Intrusion(s) == s \in TypeSensor

BocOn == /\ bocina = 0
         /\ bocina' = 1

Alerta(s) == /\ Intrusion(s)
             /\ armado = 1
             /\ BocOn
             /\ UNCHANGED <<armado>>
             
BocOff == /\ bocina = 1
          /\ bocina' = 0
          
OffAlerta(p) == /\ Desarmar(p)
                /\ BocOff

TNext == (\E p \in (Digitos \times Digitos) : SoloArmar(p) \/ SoloDesarmar(p) \/ OffAlerta(p))
         \/ \E s \in TypeSensor : Alerta(s)
\*Liveness == \forall p \in (Digitos \times Digitos) : WF_vars(Armar(p) \/ Desarmar(p))
Fairness == WF_vars(ArmarOp) /\ WF_vars(DesarmarOp) /\ \forall s \in TypeSensor : WF_vars(Alerta(s))
TSpec == TInit /\ [][TNext]_vars /\ Fairness
-----------------------------------------------------------------------------
THEOREM TSpec => []TypeInv

=============================================================================
\* Modification History
\* Last modified Thu Feb 16 00:08:49 ART 2023 by sebapc
\* Created Wed Feb 15 19:54:44 ART 2023 by sebapc
