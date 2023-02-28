-------------------------- MODULE cliente_servidor --------------------------
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS User, File, usuarios, M, FID
ASSUME usuarios \subseteq User /\ M \in Nat /\ M > 0

VARIABLES conexiones, archivos, pedidos, out

vars == <<conexiones, archivos, pedidos, out>>

Request == [type: {"GET"}, fid: FID] \cup 
           [type: {"POST"}, file: File, perm: SUBSET User] \cup
           [type: {"AUTH"}, u: User]

Output == File \cup {"ok", "error"}

null == CHOOSE x : x \notin User \X Output
-----------------------------------------------------------------------------

TypeInv == /\ conexiones \subseteq User
           /\ archivos \in [FID -> [file: File, perm: SUBSET User] \cup {"not"}]
           /\ out \in User \X (Output \cup {null})
           /\ pedidos \in Seq(User \X Request)

Init == /\ conexiones = {}
        /\ archivos = [FID -> "not"]
        /\ pedidos = <<>>
        /\ out = null
        
ClientGet(c, fid) == /\ c \in conexiones
                     /\ fid \in DOMAIN archivos
                     /\ c \in archivos[fid].perm
                     /\ pedidos' = Append(pedidos, <<c, <<"GET", fid>>>>)
                     /\ UNCHANGED <<conexiones, archivos, out>>

ServerGet == /\ Cardinality(pedidos) >= 1
             /\ Head(pedidos)[2].type = "GET"
             /\ Head(pedidos)[2].fid \in DOMAIN archivos
             /\ out' = <<Head(pedidos)[1], archivos[Head(pedidos)[2].fid].file>>
             /\ pedidos' = Tail(pedidos)
             /\ UNCHANGED <<conexiones, archivos>>

ClientPost(c, f, p) == /\ c \in conexiones
                       /\ pedidos' = Append(pedidos, <<c, <<"POST", f, p>>>>)
                       /\ UNCHANGED <<conexiones, archivos, out>>

ServerPost == /\ Cardinality(pedidos) >= 1
              /\ Head(pedidos)[2].type = "POST"
              /\ archivos' = [archivos 
                 EXCEPT ![CHOOSE fid \in FID : archivos[fid] = "not"] 
                    = <<Head(pedidos)[2].file, 
                        Head(pedidos)[2].perm \cup {Head(pedidos)[1]}>>]
              /\ out' = "ok"
              /\ pedidos' = Tail(pedidos)
              /\ UNCHANGED <<conexiones>>

ClientAuth(c) == /\ c \in conexiones
                 /\ c \in usuarios
                 /\ pedidos' = Append(pedidos, <<c, <<"AUTH", c>> >>)
                 /\ UNCHANGED <<conexiones, archivos, out>>

ServerAuth == /\ Cardinality(pedidos) >= 1
              /\ Head(pedidos)[2].type = "AUTH"
              /\ Head(pedidos)[2].u \in usuarios
              /\ Head(pedidos)[2].u \notin conexiones
              /\ out' = <<Head(pedidos)[1], "ok">>
              /\ pedidos' = Tail(pedidos)
              /\ UNCHANGED <<conexiones, archivos>>

AbrirConexion(u) == /\ u \notin conexiones
                    /\ Cardinality(conexiones) < M
                    /\ conexiones' = conexiones \cup {u}
                    /\ UNCHANGED <<archivos, pedidos, out>>

CerrarConexion(u) == /\ u \in conexiones
                     /\ conexiones' = conexiones - {u}
                     /\ UNCHANGED <<archivos, pedidos, out>>

Client(c) ==
    \/ \E fid \in FID : ClientGet(c, fid)
    \/ \E f \in File, p \in SUBSET User : ClientPost(c,f,p)
    \/ ClientAuth(c)

Server == ServerGet \/ ServerPost \/ ServerAuth

Conexion(u) == AbrirConexion(u) \/ CerrarConexion(u)

Next == Server \/ \E c \in User : Conexion(c) \/ Client(c)

Fairness == WF_vars(ServerGet) /\ WF_vars(ServerPost) /\ WF_vars(ServerAuth) 

Spec == Init /\ [][Next]_vars /\ Fairness
-----------------------------------------------------------------------------

THEOREM Spec => []TypeInv
=============================================================================
\* Modification History
\* Last modified Fri Feb 24 22:40:02 ART 2023 by sebapc
\* Created Fri Feb 24 21:09:31 ART 2023 by sebapc
