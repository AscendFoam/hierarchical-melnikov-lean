# Hilbert 16 Lean-Core

This is a zero-`sorry`, end-to-end Lean 4 formalization of the repository's
explicit lower-bound construction for the number of limit cycles of planar
polynomial vector fields. It targets Lean `4.33.1` and Mathlib `v4.33.1`.

## Machine-checked scope

- `Hilbert16/Counting*`, `Hilbert16/Hierarchy*`, and
  `Hilbert16/Chebyshev/ThreeAdicVisibility.lean` establish the exact three-adic
  counts, visibility relations, and hierarchical indexing used by the
  construction.
- `Hilbert16/Spikes*`, `Hilbert16/Hypergeometric*`, and
  `Hilbert16/Analytic*` connect the Borel--Gauss and Chebyshev kernels to finite
  analytic rank, then turn that rank into hierarchical families of simple
  positive roots.
- `Hilbert16/Dynamics*` constructs the polynomial perturbations and local
  flows, identifies the first Melnikov displacement, continues the simple
  roots to actual periodic orbits, and proves that the resulting carriers are
  isolated and pairwise disjoint.
- `Hilbert16/Degree*` audits the polynomial degree, while
  `Hilbert16/Asymptotics.lean` transfers the exact three-adic subsequence count
  to all sufficiently large degrees.
- `Hilbert16/Main.lean` exports both the exact subsequence theorem
  `threeAdic_subsequence_limitCycle_lower_bound` and the all-degree theorem
  `polynomial_limitCycle_lower_bound_asymptotic`. The latter produces, for all
  sufficiently large `N`, a degree-at-most-`N` polynomial vector field with at
  least `c * N^2 * (log N)^2` actual limit cycles for one explicit positive
  constant `c`.
- `Hilbert16/AxiomAudit.lean` prints the axiom dependencies of the public proof
  surface. The audit uses only Lean/Mathlib's standard logical foundations
  `propext`, `Classical.choice`, and `Quot.sound`; it introduces no
  project-specific axiom.

## Build

With `elan`/`lake` available, an existing checkout should use the committed
manifest without updating dependency revisions:

```text
lake exe cache get
lake build
lake env lean Hilbert16/AxiomAudit.lean
```

The Lean toolchain is pinned in `lean-toolchain`; Mathlib and its transitive
dependencies are locked by `lake-manifest.json`. Run `lake update` only when
intentionally changing dependencies, and commit the resulting manifest change
with that update.

## Git boundary

Git is the source of truth for every handwritten `*.lean` file, the Lake
configuration and manifest, mathematical documentation, reproducibility
scripts, and compact text build/audit reports. A long proof should be split
into readable modules, not omitted from Git merely because it is large.

The following directories are deliberately local-only:

- `.lake/`: downloaded dependencies, Mathlib cache, and compiled objects;
- `Scratch/`: disposable experiments, including files that may contain
  temporary `sorry` declarations and are not imported by `Hilbert16.lean`;
- `local/`: private working notes or machine-specific inputs;
- `artifacts/`: large generated certificates, traces, profiles, and renders.

These directories are ignored rather than backed up. Anything needed to
reproduce a theorem must instead be represented by tracked source, a generator
and its small inputs, plus a compact result summary such as `BUILD_REPORT.md`.
Do not place the only copy of irreplaceable work in an ignored directory.
