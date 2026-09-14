# Hilbert 16 Lean-Core

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22752134.svg)](https://doi.org/10.5281/zenodo.22752134)

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
  roots to actual periodic orbits, and constructs genuine transverse local
  Poincare return certificates. It proves that each planar multiplier is
  positive and differs from one in modulus, and that the resulting carriers
  are isolated and pairwise disjoint.
- `Hilbert16/Degree*` audits the polynomial degree, while
  `Hilbert16/Asymptotics.lean` transfers the exact three-adic subsequence count
  to all sufficiently large degrees.
- `Hilbert16/Main.lean` exports the exact subsequence theorem
  `threeAdic_subsequence_hyperbolicLimitCycle_lower_bound` and the all-degree
  theorem `polynomial_hyperbolicLimitCycle_lower_bound_asymptotic`. The latter
  produces, for every `N >= 144`, a degree-at-most-`N` polynomial vector field
  with an injective family of at least `c * N^2 * (log N)^2`
  standard-hyperbolic limit cycles, where
  `c = 1 / (5184 * (log 3)^2)`. The limit-cycle-only endpoints remain available
  as forgetful corollaries.
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

## Continuous integration

The GitHub Actions workflow uses the pinned toolchain and manifest, runs the
standard Lean project build, and then executes the explicit axiom audit:

```text
lake build
lake env lean Hilbert16/AxiomAudit.lean
```

## Companion manuscript

This repository accompanies *Hierarchical Melnikov Realization and an
N-squared Log-squared Lower Bound for Hilbert Numbers*. The release tagged
`arxiv-v1` identifies the formal source corresponding to the first arXiv
submission. `docs/PROOF_MAP.md` maps manuscript labels to audited Lean
declarations. The immutable release archive is available as
[Zenodo record 10.5281/zenodo.22752134](https://doi.org/10.5281/zenodo.22752134).

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
