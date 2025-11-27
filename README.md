# WindowsRepairAlgoTLAPlus

Formal TLA+ specification and model-checking workflow that describes a Windows-style 3D mesh repair algorithm.

This project models a multi-phase repair pipeline similar to what Windows 3D Builder does internally:

* Parse triangle soup
* Rebuild topology
* Detect and eliminate degenerate or invalid faces
* Identify and repair boundary edges
* Enforce manifold and watertight constraints
* Select a minimal-distance repaired mesh

The specification is written in **TLA+**, and validated using **TLC** in GitHub Actions.

## Continuous Model Checking

The latest TLC model-checking run for the main branch:

[![TLC](https://github.com/JohnDoe6345789/WindowsRepairAlgoTLAPlus/actions/workflows/tlc.yml/badge.svg)](https://github.com/JohnDoe6345789/WindowsRepairAlgoTLAPlus/actions/workflows/tlc.yml)

Each workflow execution:

* Bootstraps the TLA+ toolchain (downloads `tla2tools.jar`)
* Runs `STLRepairAlgo.tla` through the TLC model checker
* Captures logs into `ci-results/`
* Commits logs to a dedicated `ci/test-results` branch for historical inspection

## Repository Structure

```
/spec
  STLRepair.tla            # Core mesh model & invariants
  STLRepairAlgo.tla        # Stateful algorithm over mesh sets

/models
  STLRepairAlgo.cfg        # TLC configuration

/scripts
  bootstrap.sh             # Downloads tla2tools.jar
  run-tlc.sh               # Executes TLC and stores logs

/.github/workflows
  tlc.yml                  # CI workflow for model checking
```

## Goals

This project aims to:

* Explore formalizing 3D mesh repair logic
* Provide a deterministic specification of the minimal-repair semantics
* Demonstrate GitHub-native automated model checking
* Provide a foundation for more advanced mesh-processing formalisms

## Future Work

* Expand mesh universe beyond fixed small sets
* Add refinement mapping to a concrete implementation
* Add tests for pathological meshes (bow-ties, self-intersections)
* Encode voxel-remeshing path as a separate refinement layer

## License

MIT


[![TLC](https://github.com/JohnDoe6345789/WindowsRepairAlgoTLAPlus/actions/workflows/tlc.yml/badge.svg)](https://github.com/JohnDoe6345789/WindowsRepairAlgoTLAPlus/actions/workflows/tlc.yml)

