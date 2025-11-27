-------------------------- MODULE STLRepairAlgo --------------------------
EXTENDS STLRepair, FiniteSets

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
    phase,   \* Current phase of the pipeline
    mesh     \* Current mesh (subset of Triangle)

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
    \* Optionally, we could call VoxelRemesh here instead.
    FillHoles(CleanTriangleSoup(m))

(***************************************************************************)
(* Initialisation and next-state relation                                  *)
(***************************************************************************)

Init ==
    /\ phase = "RAW"
    /\ mesh \subseteq Triangle
    /\ mesh # {}    \* some non-empty starting mesh

Next ==
    \/ /\ phase = "RAW"
       /\ mesh' = CleanTriangleSoup(mesh)
       /\ phase' = "CLEANED"

    \/ /\ phase = "CLEANED"
       /\ mesh' = FillHoles(mesh)
       /\ phase' = "HOLE_FILLED"

    \/ /\ phase = "HOLE_FILLED"
       /\ mesh' = mesh
       /\ phase' = "FINAL"

    \/ /\ phase = "FINAL"
       /\ UNCHANGED <<mesh, phase>>

Spec ==
    Init /\ [][Next]_<<mesh, phase>>

(***************************************************************************)
(* Invariants and refinement                                               *)
(***************************************************************************)

InvBasic ==
    /\ phase \in PhaseType
    /\ mesh \subseteq Triangle

InvFinalValidity ==
    (phase = "FINAL") => IsValidMesh(mesh)

(*
  Refinement: the final mesh equals the abstract minimal Repair of the input.
  To state that, we need to remember the original input mesh.
*)

VARIABLES inputMesh

InitWithInput ==
    /\ Init
    /\ inputMesh = mesh

NextWithInput ==
    /\ Next
    /\ inputMesh' = inputMesh

SpecWithInput ==
    InitWithInput /\ [][NextWithInput]_<<mesh, phase, inputMesh>>

Refinement ==
    (phase = "FINAL") => mesh = Repair(inputMesh)

=============================================================================
