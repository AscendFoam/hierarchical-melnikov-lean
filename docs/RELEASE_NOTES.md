# Release notes

## v1.1.0 — 2026-10-08

This release accompanies *Hierarchical Melnikov Realization: Logarithmic Factor
Improvement to Hilbert Number Lower Bounds* by Chaoyang Qin and Xiaoming Sun.

- Proves the revised explicit all-degree estimate for every integer `d >= 31`:

  $$B(d)=\frac{(d+5)^2}{324}
  \left(\frac{\ln((d+5)/12)}{\ln 3}\right)^2-\frac{(d+1)^2}{16}.$$

  `polynomial_hyperbolicLimitCycle_lower_bound_explicit` constructs a polynomial
  vector field of degree at most `d` and an injective family of `L` hyperbolic
  limit cycles satisfying `B(d) < L`.
- Retains the exact subsequence theorem and the previous positive asymptotic
  estimate with threshold `144`.
- Updates the proof map, build report, and citation metadata to the current
  theorem and the paper's two-author attribution.
- Keeps Lean `4.33.1` and all manifest-pinned dependency revisions unchanged.

The mathematical source was checked by the full local build and the public
axiom audit on 2026-10-07. The 415 audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`; no project-specific axioms or proof holes
are introduced. GitHub CI also passed for the released mathematical source:
[run 37645528498](https://github.com/AscendFoam/hierarchical-melnikov-lean/actions/runs/37645528498).

The source archive includes the Lean files, pinned build inputs, documentation,
reproducibility scripts, and citation metadata. Downloaded dependencies,
compiled objects, and local experiments are excluded and can be rebuilt using
the README instructions.

## arxiv-v1 — 2026-09-14

Historical software release, preserved at
[10.5281/zenodo.22752134](https://doi.org/10.5281/zenodo.22752134).
Both releases belong to the software version chain identified by concept DOI
[10.5281/zenodo.22752133](https://doi.org/10.5281/zenodo.22752133).
