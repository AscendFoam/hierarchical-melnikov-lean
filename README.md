# Hilbert 16 Lean-Core

This is a deliberately partial, zero-`sorry` Lean 4 formalization of the
discrete core of the proposed lower-bound construction. It targets Lean
`4.33.1` and Mathlib `v4.33.1`.

## Machine-checked scope

- `Hilbert16/Hierarchy.lean` checks the coordinatewise visibility order,
  monotonicity of `w(k,l)=k+l`, uniqueness of `(k,l)` as the minimum-weight
  point in its visible quadrant, and the one-power gap for every other visible
  block.
- `Hilbert16/Counting.lean` checks the finite double-sum tensor identity over
  an arbitrary commutative ring.
- The same file defines the zero-based 3-adic data
  `y_(k+1)=2*3^(r-k-1)` and `d_(k+1)=3^k`, and checks
  `y_k*d_k=2*3^(r-1)`, `sum y_k=3^r-1`, and the exact total
  `(2*3^(r-1)*r)^2-(3^r-1)^2`. This is the division-free form of
  `4*n^2*r^2/9-(n-1)^2` with `n=3^r`.
- `Hilbert16/AxiomAudit.lean` prints the axiom dependencies of every public
  theorem above; it introduces no project-specific axiom.

## Explicitly not formalized

This repository is not an end-to-end Lean proof of the claimed Hilbert-number
lower bound. In particular, it does not yet formalize:

- the cardinality proofs identifying the analytic row/frequency sets with the
  integer sequences used here;
- Chebyshev/DCT visibility and the mod-12 replication character;
- local analytic rank, rank-to-roots, or Borel-Gauss shift independence;
- the hierarchical simple-root stability theorem in analytic germs;
- the Melnikov kernel and the Poincare-Pontryagin persistence step;
- polynomial degree bounds or the subsequence-to-all-degrees asymptotic step.

Those facts must not be inferred from this Lean-Core. The accurate release
claim is: **the combinatorial and exact-counting core listed above is machine
checked; the analytic and dynamical interfaces remain outside the present
formalization.**

## Build

With `elan`/`lake` available, run:

```text
lake update
lake build
```

The dependency revisions are pinned in `lakefile.toml` and `lean-toolchain`.
