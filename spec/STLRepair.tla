----------------------------- MODULE STLRepair -----------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Fixed small universe for TLC runs                                       *)
(***************************************************************************)

CONSTANTS v1, v2, v3, v4, t1, t2, t3

Vertex  == {v1, v2, v3, v4}
Triangle == {t1, t2, t3}

(*
  For this model, we hard-code which vertices belong to which triangle.
  This avoids needing a Vertices constant in the .cfg file.
*)
Vertices ==
    [ t1 |-> {v1, v2, v3},
      t2 |-> {v2, v3, v4},
      t3 |-> {v1, v3, v4} ]

(***************************************************************************)
(* Basic mesh operators                                                    *)
(***************************************************************************)

VerticesOfTriangle(t) == Vertices[t]

EdgesOfTriangle(t) ==
    LET vs == VerticesOfTriangle(t) IN
        { {u, w} :
              u \in vs /\ w \in vs /\ u # w }

Edges(mesh) ==
    UNION { EdgesOfTriangle(t) : t \in mesh }

IncidentTriangles(mesh, e) ==
    { t \in mesh : e \in EdgesOfTriangle(t) }

BoundaryEdges(mesh) ==
    { e \in Edges(mesh) :
          Cardinality(IncidentTriangles(mesh, e)) = 1 }

NonManifoldEdges(mesh) ==
    { e \in Edges(mesh) :
          Cardinality(IncidentTriangles(mesh, e)) > 2 }

(***************************************************************************)
(* Degenerate and validity predicates                                      *)
(***************************************************************************)

DegenerateTriangle(t) ==
    \* Abstract: in a real model this would check area, etc.
    FALSE

HasDegenerates(mesh) ==
    \E t \in mesh : DegenerateTriangle(t)

Watertight(mesh) ==
    BoundaryEdges(mesh) = {}

Manifold(mesh) ==
    NonManifoldEdges(mesh) = {}

IsValidMesh(mesh) ==
    /\ mesh \subseteq Triangle
    /\ ~HasDegenerates(mesh)
    /\ Manifold(mesh)
    /\ Watertight(mesh)

(***************************************************************************)
(* Distance / minimal repair                                               *)
(***************************************************************************)

MeshDistance(m1, m2) ==
    Cardinality((m1 \ m2) \cup (m2 \ m1))

MinimalRepair(input, result) ==
    /\ IsValidMesh(result)
    /\ \A m \in SUBSET Triangle :
          IsValidMesh(m) =>
            MeshDistance(input, result)
              <= MeshDistance(input, m)

Repair(mesh) ==
    CHOOSE m \in SUBSET Triangle : MinimalRepair(mesh, m)

=============================================================================
