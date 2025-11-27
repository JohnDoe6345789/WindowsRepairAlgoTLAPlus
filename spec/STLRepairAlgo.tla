-------------------------- MODULE STLRepairAlgo --------------------------
EXTENDS STLRepair, FiniteSets

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
    phase,     \* Current phase of the pipeline
    mesh,      \* Current mesh (subset of Triangle)
    inputMesh  \* Original input mesh, for refinement checking

PhaseType == {"RAW", "CLEANED", "HOLE_FILLED", "FINAL"}

(***************************************************************************)
(* Phase-specific operators                                                *)
(***************************************************************************)

CleanTriangleSoup(m) ==
    \* Remove degenerate triangles (abstractly).
    { t \in m : ~DegenerateTriangle(t) }

FillHoles(m) ==
    \* Find a hole-free superset of m that is minimally different.
    CHOOSE m2 \in SUBSET Triangle :
        /\ m \subseteq m2
        /\ Watertight(m2)
        /\ \A m3 \in SUBSET Triangle :
              (m \subseteq m3 /\ Watertight(m3))
                  => MeshDistance(m, m2)
                       <= MeshDistance(m, m3)

FinalRepair(m) ==
    \* In a richer model, this could use voxel remeshing, etc.
    FillHoles(CleanTriangleSoup(m))

(***************************************************************************)
(* Initialisation and next-state relation                                  *)
(***************************************************************************)

Init ==
    /\ phase = "RAW"
    /\ mesh \subseteq Triangle
    /\ mesh # {}

InitWithInput ==
    /\ Init
    /\ inputMesh = mesh

Next ==
    \/ /\ phase = "RAW"
       /\ mesh' = CleanTriangleSoup(mesh)
       /\ phase' = "CLEANED"
       /\ inputMesh' = inputMesh

    \/ /\ phase = "CLEANED"
       /\ mesh' = FillHoles(mesh)
       /\ phase' = "HOLE_FILLED"
       /\ inputMesh' = inputMesh

    \/ /\ phase = "HOLE_FILLED"
       /\ mesh' = mesh
       /\ phase' = "FINAL"
       /\ inputMesh' = inputMesh

    \/ /\ phase = "FINAL"
       /\ UNCHANGED <<mesh, phase, inputMesh>>

SpecWithInput ==
    InitWithInput /\ [][Next]_<<mesh, phase, inputMesh>>

(***************************************************************************)
(* Invariants and refinement                                               *)
(***************************************************************************)

InvBasic ==
    /\ phase \in PhaseType
    /\ mesh \subseteq Triangle

InvFinalValidity ==
    (phase = "FINAL") => IsValidMesh(mesh)

Refinement ==
    (phase = "FINAL") => mesh = Repair(inputMesh)

=============================================================================
