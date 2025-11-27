----------------------------- MODULE STLRepair -----------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)

CONSTANTS
    Vertex,      \* Finite set of abstract vertices
    Triangle,    \* Finite set of abstract triangles
    Vertices     \* Function: Triangle -> {3-elem subsets of Vertex}

ASSUME /\ Vertex # {}
       /\ Triangle # {}
       /\ Vertices \in [Triangle -> SUBSET Vertex]
       /\ \A t \in Triangle : Cardinality(Vertices[t]) = 3

(***************************************************************************)
(* Basic mesh operators                                                    *)
(***************************************************************************)

VerticesOfTriangle(t) == Vertices[t]

EdgesOfTriangle(t) ==
    LET vs == VerticesOfTriangle(t) IN
        { {v1, v2} :
              v1 \in vs /\ v2 \in vs /\ v1 # v2 }

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
