# Lean-Core build report

Date: 2026-08-27

## Versions

- Lean: `4.33.1` (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`)
- Lake: `5.0.0-src+819816b`
- Mathlib: `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`)
- Platform: `arm64-apple-darwin24.6.0`

## Verification performed

The source files were compiled with the pinned Lean toolchain against the
already cached Mathlib build in the sibling `Lean验证` project. Both source
modules compiled with exit code 0 and no diagnostics:

```text
lake env lean /absolute/path/to/lean_core/Hilbert16/Counting.lean
lake env lean /absolute/path/to/lean_core/Hilbert16/Hierarchy.lean
```

The two object files and the root `Hilbert16.lean` object were then rebuilt,
and `Hilbert16/AxiomAudit.lean` was checked against that root object. Its
complete result was:

```text
tensorLayer_counting_identity: [propext, Classical.choice, Quot.sound]
balanced_layer: [propext, Quot.sound]
rowMultiplicity_sum: [propext, Classical.choice, Quot.sound]
balancedWeighted_sum: [propext, Classical.choice, Quot.sound]
threeAdic_exact_count: [propext, Classical.choice, Quot.sound]
threeAdic_exact_count_scaled: [propext, Classical.choice, Quot.sound]
visible_weight_mono: [propext, Quot.sound]
visible_equal_weight_iff: [propext, Quot.sound]
visible_weight_gap: [propext, Quot.sound]
```

These are Lean/Mathlib's standard logical foundations. No project-specific
axiom is declared.

A source scan of every `*.lean` file found no `sorry`, `admit`, custom `axiom`,
or `unsafe` declaration.

## Project-local reproducibility check

On 2026-08-27, `lake update` generated `lake-manifest.json` and locked Mathlib
to `0df444a360eaa60ab8c11dca51a86af692955474`. Lake downloaded dependencies and
precompiled cache into the ignored project-local `.lake/` directory (7.4 GB on
this machine). With that manifest and cache, the following commands completed
successfully:

```text
lake build
lake env lean Hilbert16/AxiomAudit.lean
```

The full Lake build completed all 823 jobs. The axiom output was identical to
the list above and contained no project-specific axiom.

## Boundary of this report

This report certifies compilation of the discrete hierarchy and exact-counting
modules only. It does not certify any of the analytic or dynamical statements
listed as out of scope in `README.md`.

For a clean checkout with network access, the ordinary reproducible build is:

```text
lake exe cache get
lake build
lake env lean Hilbert16/AxiomAudit.lean
```

`lake update` is a dependency-maintenance operation, not a normal clone/build
step; using it routinely can rewrite the committed manifest.
