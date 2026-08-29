# Lean-Core build report

Date: 2026-08-27--2026-08-28

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

After pushing commit `72e31e0`, a fresh shallow clone from the private GitHub
remote was also checked. It had a clean worktree, contained the committed
manifest and all Lean sources, contained no `.lake/` directory, and applied the
local-only ignore rules for `Scratch/`, `local/`, and `artifacts/`. This verifies
the Git payload; the target machine should still perform its own cache download
and full build as the final cross-machine check.

## Boundary of this report

The original portion of this report certifies the discrete hierarchy and exact-counting modules.
The Windows addendum below also certifies the explicitly listed strict-subset slice declarations.
It does not certify the paper-level analytic or dynamical statements listed as open in
`docs/PROOF_MAP.md`.

For a clean checkout with network access, the ordinary reproducible build is:

```text
lake exe cache get
lake build
lake env lean Hilbert16/AxiomAudit.lean
```

## Windows target-machine verification and first high-risk slices

On 2026-08-27 the committed project was rebuilt on the target Windows machine with:

- platform: `x86_64-w64-windows-gnu`;
- Lean `4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`;
- Lake `5.0.0-src+819816b`;
- Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`;
- VS Code Lean extension `leanprover.lean4@0.0.239`.

`lake exe cache get` fetched every manifest dependency and decompressed 8690 Mathlib cache files.
Before source changes, `lake build` completed all 823 baseline jobs and the axiom audit reproduced the
macOS report above.

The first zero-`sorry` B1/B2/B3 slices were then added and imported by `Hilbert16.lean`:

- `Hilbert16/Spikes/BorelGauss.lean`: paper `U_p(alpha)` coefficients, their coefficientwise Borel
  transform into Mathlib's `₂F₁`, parameter symmetry, and the exact series-term interface;
- `Hilbert16/Spikes/ExactMelnikovKernel.lean`: the normalized two-dimensional disk-area base case
  and Taylor product rows `m=0,1`;
- `Hilbert16/Spikes/PoincarePersistence.lean`: canonical phase space, parameter lifting, and local
  integral-curve existence for the original and lifted `C¹` systems.

With these imports, `lake build` completed all 2777 jobs. The extended `AxiomAudit.lean` reported
only `propext`, `Classical.choice`, and `Quot.sound` for the new slice declarations. These slices do
not yet meet their Go criteria: the negative-axis Gauss connection formula, the full cell integral,
and the Poincare return-map persistence theorem remain open.

### B1 negative-axis validation increment

Later on 2026-08-27, `Hilbert16/Spikes/BorelGauss.lean` was extended with the specialized DLMF
15.8.2 right-hand side and an Euler-integral continuation contract. The following facts now compile:

- both transformed Gauss-series parameters and their values at zero;
- exact radius one and explicit `HasSum` certificates at `-x⁻¹` for `x>1`;
- positivity and nonvanishing of both Gamma connection coefficients for `0<alpha<1`;
- reduction of both raw regularized-DLMF coefficients to the paper's ordinary-`₂F₁` coefficients
  using Euler's Gamma reflection formula;
- a Beta-measure realization of the Euler continuation, including normalization at zero,
  almost-everywhere unit-interval support, branch positivity, integrability, and strict positivity
  throughout `s<1`.

This increment still does not claim the exact connection equality. The open boundary is recorded
as `NegativeAxisConnectionFormula`: prove that the Euler-integral continuation equals the compiled
right-hand side, and prove that the Euler integral agrees with the original Borel germ inside the
unit disk. See `docs/B1_NEGATIVE_AXIS.md`.

After this increment, the Windows-native root `lake build` completed all 3472 jobs. The expanded
`Hilbert16/AxiomAudit.lean` passed for every listed B1 declaration and reported only `propext`,
`Classical.choice`, and `Quot.sound`.

### B1 Euler--Borel germ and connection-boundary increment

On 2026-08-28 the first previously open analytic boundary was closed.  The compiled theorem
`gaussEulerContinuation_eq_borelImage` proves, for `0 < alpha < 1` and `|s| < 1`, that the
Euler--Beta continuation is exactly the original Borel `₂F₁` series.  Its proof includes the
nonintegral Beta-density infrastructure, dominated exchange of the binomial series and integral,
the exact Beta moments, and coefficient normalization to Mathlib's ordinary hypergeometric series.

The negative-axis connection proof also gained two project-internal boundary-data theorems:

- `gaussEulerContinuation_leading_tendsto` computes the growing-branch coefficient directly from
  the Euler integral and identifies it with `gaussConnectionA`;
- `gaussEulerContinuation_neg_hasDerivAt` justifies differentiation under the Beta integral on the
  negative axis.

The second boundary was then closed in two new zero-`sorry` modules:

- `Hilbert16/Spikes/BorelGaussODE.lean` proves the ordinary hypergeometric ODE directly from the
  coefficient recurrence, differentiates both infinity branches twice, differentiates the
  Euler/Beta integral twice, and proves the Euler negative-axis ODE by an endpoint-safe Beta
  integration-by-parts identity;
- `Hilbert16/Spikes/BorelGaussConnection.lean` specializes the two Frobenius branches, proves their
  normalized leading/decay limits, subtracts the exact Gamma-weighted connection candidate, and
  closes uniqueness with the conserved scaled Wronskian.

The final theorem `negativeAxisConnectionFormula` now proves `NegativeAxisConnectionFormula alpha`
for every `0 < alpha < 1`; equivalently, for every `x>1`, the Euler/Beta continuation at `-x` is
the compiled Gamma--Gauss connection right-hand side. No DLMF identity is assumed as a project
axiom.

After importing `BorelGaussConnection` from `Hilbert16.lean`, the Windows-native root `lake build`
completed all 3492 jobs. The expanded axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the germ bridge, ODE, Wronskian, zero-remainder, and final connection theorems. A
source scan found no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration.

### B1 shifted-independence completion

Later on 2026-08-28, Paper Lemma 5.1 was completed in two responsibility modules:

- `Hilbert16/Spikes/BorelGaussAnalytic.lean` constructs an explicit local Beta/binomial power
  series at every positive negative-axis coordinate and proves real analyticity there;
- `Hilbert16/Hypergeometric/ShiftIndependence.lean` converts a formal shifted relation into a
  uniform-order differentiated Borel relation, propagates it by analytic uniqueness, proves the
  arbitrary-order leading asymptotic and its nonzero coefficient, and separates the resulting
  pairwise-distinct real exponents.

The public theorem `borelGaussShiftIndependent` covers arbitrary finite strictly ordered parameter
families in `0<alpha<1` and every finite shift range. After importing it from `Hilbert16.lean`, the
Windows-native root `lake build` completed all 3494 jobs. `Hilbert16/AxiomAudit.lean` reports only
`propext`, `Classical.choice`, and `Quot.sound` for all new declarations, and the source scan again
found no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration.

### W7 Cartesian-rank formal-series increment

Later on 2026-08-28, `Hilbert16/Hypergeometric/CartesianRank.lean` completed the formal-series
linear-algebra part of Paper Proposition 5.2. It proves:

- the exact monic degree-`m` polynomial representation of `U_m(beta)` in `beta^2` and the resulting
  nonzero polynomial Vandermonde determinant for distinct positive beta parameters;
- existence of a finite square evaluation minor for every finite linearly independent function
  family, without assuming that an initial Taylor segment suffices;
- the paper's anisotropic beta-column transform, its coefficientwise `lambda → ∞` limit, convergence
  of the selected determinant, and eventual nonvanishing;
- `anisotropicCartesianRank`, giving eventual linear independence of every finite Cartesian family
  of formal product rows; and `anisotropicAnalyticKernelTaylorRank`, which includes the nonzero
  Taylor row factor `2^m/(m+1)!` from Eq. (3.12).

After importing the module from `Hilbert16.lean`, the Windows-native `lake build` completed all
3495 jobs. The new public declarations were added to `Hilbert16/AxiomAudit.lean`; every result lists
only `propext`, `Classical.choice`, and `Quot.sound`. The source scan again found no `sorry`,
`admit`, project `axiom`, or proof-bypassing `unsafe` declaration. This increment certifies the
formal-series portion only: W4 must still realize these sequences as Taylor coefficients of the
actual convergent analytic Melnikov kernels before Proposition 5.2 is marked `proved`.

### W7 convergent analytic-kernel completion

Still later on 2026-08-28, `Hilbert16/Hypergeometric/AnalyticKernel.lean` closed the preceding
boundary. It derives an absolute Cauchy-product majorant from the radius-one Borel--Gauss series,
proves summability of the exact Eq. (3.12) Taylor coefficients at radius `1/4`, constructs their
positive-radius `FormalMultilinearSeries` sum, and proves `HasFPowerSeriesAt` and `AnalyticAt` at
zero. A reusable power-series uniqueness lemma transfers linear independence of Taylor coefficient
sequences to the represented functions.

The final theorem `anisotropicAnalyticKernelRank` proves Proposition 5.2 for the actual convergent
analytic kernels. `finiteBlockCommonAnisotropicKernelRank` also formalizes the paper's subsequent
finite maximum argument and produces one common anisotropy threshold for block-dependent finite
families.

After importing this module from `Hilbert16.lean`, the Windows-native full `lake build` completed
all 3496 jobs. The expanded axiom audit again reports only `propext`, `Classical.choice`, and
`Quot.sound`; a declaration-level source scan found no `sorry`, `admit`, project `axiom`, or
proof-bypassing `unsafe`. Proposition 5.2 is therefore complete. W4 remains open only at the
geometric bridge: the exact Chebyshev cell integral must be proved equal to this analytic kernel.

### W4 exact disk-moment increment

Still later on 2026-08-28, `Hilbert16/Spikes/ExactMelnikovKernel.lean` proved the general even
Cartesian disk moment in Paper Eq. (3.11). The proof evaluates the radial power integral, derives
the mixed angular beta integral from integration by parts and the Wallis product, extends it to
the full `(-π,π)` angular range, applies Fubini on the polar rectangle, and then uses Mathlib's
`integral_comp_polarCoord_symm` to transport the result back to the actual measurable Cartesian
set `x²+y²<2h`.

The public theorem `cartesianEvenMonomialMoment_eq` is therefore a geometric integral theorem, not
a stipulated Taylor-coefficient identity. W4 remains `proving`: the next obligations are the
locally convergent `cos(alpha * arcsin u)` expansion, justified termwise double integration,
ellipse scaling, and the signed Chebyshev-cell change of variables.

`lake update` is a dependency-maintenance operation, not a normal clone/build
step; using it routinely can rewrite the committed manifest.

### W4 convergent disk-mode integration increment

Still later on 2026-08-28, `Hilbert16/Spikes/CosArcsin.lean` proved the exact real identity between
`cos(alpha * arcsin u)` and its Gauss series throughout `|u|<1`, together with absolute
summability. `Hilbert16/Spikes/ExactMelnikovKernel.lean` then formed the absolutely convergent
two-variable Cauchy antidiagonals and proved that every normalized finite row integrates to the
corresponding Eq. (3.12) Taylor row.

The new root-imported module `Hilbert16/Hypergeometric/ModeIntegral.lean` bounds the integral norm
of each antidiagonal by the previously certified summable `analyticKernelMajorant`, applies the
Bochner/Lebesgue dominated infinite-sum theorem, and proves
`normalizedModeDiskIntegral_eq_analyticKernel` for `0<h<1/4` and `lambda≥1`. Thus the actual
normalized Cartesian disk integral of the two cosine--arcsine modes is now exactly the convergent
analytic kernel used in Proposition 5.2.

The Windows-native full root build completed successfully with 3499 jobs. The expanded axiom
audit lists only `propext`, `Classical.choice`, and `Quot.sound` for the cosine expansion,
antidiagonal convergence, termwise integration, and final disk-mode identity. W4 remains
`proving` only for ellipse scaling and the signed Chebyshev single-cell inverse-branch/orientation
bridge.

### W4 ellipse scaling and signed single-cell increment

Still later on 2026-08-28, `Hilbert16/Hypergeometric/EllipseScaling.lean` proved the exact
`w = sqrt(lambda) * v` measure scaling by Fubini and the one-dimensional Haar scaling theorem.
It identifies the elliptic mode integral with `(2*pi*h/sqrt(lambda))` times the convergent analytic
kernel.

`Hilbert16/Spikes/ChebyshevCell.lean` then supplied the explicit Chebyshev inverse branch, proved
its right-inverse identity on `[-1,1]`, computed its derivative on `(-1,1)`, and proved that its
angle remains in `(0,pi)`. Consequently each one-dimensional derivative and the product Jacobian
have a checked constant sign. The declaration `chebyshevCellJacobianOrientation` lies in
`{±1}` and is nonzero. Reflection on the elliptic disk eliminates all odd terms, and
`integral_chebyshevCellMode_eq_weight_mul_area_mul_analyticKernel` gives the exact single-mode
pulled-back cell formula with its DCT weight.

Both modules are now root-imported. The Windows-native full build completed successfully with
3512 jobs. The expanded axiom audit again reports only `propext`, `Classical.choice`, and
`Quot.sound`, and the declaration scan finds no `sorry`, `admit`, project `axiom`, or `unsafe`.
W4 remains `proving`: the outstanding bridge is the actual original-cell `(x,y)` set-integral
change of variables, plus its combination with Green/orbit orientation into the paper's
`sigma_ij`.

### W4 genuine original-cell Jacobian increment

Still later on 2026-08-28, `Hilbert16/Spikes/ChebyshevChangeOfVariables.lean` closed the remaining
B2 change-of-variables boundary. It defines the original cell energy region as the product
inverse-branch image of the elliptic disk and applies Mathlib's general finite-dimensional
`integral_image_eq_integral_abs_det_fderiv_smul` theorem. Injectivity is proved by applying the
compiled `T_n(x_i(u))=u` identities in each coordinate.

The module computes the product Fréchet determinant, differentiates the right-inverse identity to
obtain `T_n'(x_i(u))*x_i'(u)=1`, and uses the previously proved constant Jacobian sign to eliminate
the absolute value. Consequently
`integral_chebyshevDensityMode_cell_eq_orientation_mul_weight_mul_kernel` identifies the actual
original `(x,y)` polynomial density-mode set integral with the exact cell orientation, DCT weight,
area factor `2*pi*h/sqrt(lambda)`, and convergent analytic kernel.

The module is root-imported. The Windows-native full build completed successfully with 3513 jobs;
the expanded axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. The source scan
finds no `sorry`, `admit`, project `axiom`, or `unsafe`. B2 therefore passes its Go criterion. W4
still requires the Green/closed-orbit line-to-area identity and its orbit-orientation convention,
then the finite Chebyshev density sum.

### W4 finite density and vertical Green/FTC increment

Still later on 2026-08-28, `Hilbert16/Spikes/ChebyshevDensity.lean` proved integrability of every
original-cell density mode and lifted the exact single-mode kernel identity to an arbitrary finite
frequency support with arbitrary real coefficients. The theorem
`integral_finiteChebyshevDensity_cell_eq_kernel_sum` is the finite-density form of Paper
Eq. (3.8)--(3.12), including the common cell orientation and ellipse area factor.

Because Mathlib does not currently expose a Green theorem for arbitrary Jordan cells,
`Hilbert16/Spikes/GreenVertical.lean` proves the needed analytic core directly from interval FTC.
For `P(x,y)=integral 0..x q(s,y)`, the upward right-graph contribution minus the upward left-graph
contribution equals the iterated area integral. A separate theorem proves that adding any function
of `y` to `P` does not change this closed-boundary value.

Both modules are root-imported. The Windows-native full build completed successfully with 3515
jobs. The expanded audit again lists only `propext`, `Classical.choice`, and `Quot.sound`. W4 now
remains open only at the explicit Hamiltonian-orbit parameterization, equality of its Mathlib curve
integral with the compiled vertical-boundary functional, and the resulting time orientation.

### W3 Hamiltonian and W4 explicit-orbit increment

Still later on 2026-08-28, `Hilbert16/Spikes/ChebyshevHamiltonian.lean` defined Paper Eq. (3.1),
proved each indexed point is built from simple Chebyshev roots, proved both Hamiltonian-gradient
coordinates vanish there, and proved the displayed Hessian quadratic form is positive definite.
It also proves that the product inverse branches transform the Hamiltonian exactly into
`(u^2 + lambda*v^2)/2`.

`Hilbert16/Spikes/ChebyshevOrbit.lean` then constructed the explicit angular ellipse and its image
inside each cell. The compiled theorems prove exact energy `H=h`, `2*pi` closure, both coordinate
derivatives, the exact relation between angular velocity and the Hamiltonian vector field, and the
sign of the time-reparametrization factor relative to the cell Jacobian orientation. Hence the
orbit and its time direction are no longer informal W4 inputs. Only the equality between the
parameterized `P dy` curve integral and `verticalBoundaryPdy` remains in the Green/orbit bridge.

Both modules are root-imported. The Windows-native full build completed successfully with 3517
jobs. The expanded axiom audit again contains only `propext`, `Classical.choice`, and `Quot.sound`.

The same increment also closes the finite-cardinality part of W3:
`chebyshevRootCoordinate_injective` uses strict antitonicity of cosine on `[0,pi]`,
`chebyshevRootEmbedding` packages all `n` distinct roots, and `chebyshevCenterGrid_card` proves that
their product grid has exactly `n^2` elements.

### W4 Green/orbit/Melnikov completion

Still later on 2026-08-28, the final geometric boundary in W4 was closed without adding a Jordan
curve or Green-theorem axiom:

- `ParameterizedPdy.lean` proves that differentiable reparameterizations of the upward right graph
  and downward left graph equal the compiled `verticalBoundaryPdy` functional;
- `EllipticOrbitPdy.lean` splits the smooth angular ellipse into exactly those two graph arcs;
- `ChebyshevOrbitPdy.lean` pulls the physical `P dy` integral through both Chebyshev inverse
  branches;
- `EllipticSlice.lean` proves the exact vertical-slice Fubini formula for the open energy ellipse;
- `ChebyshevMelnikov.lean` proves continuity of the canonical primitive, performs the inner
  inverse-branch substitution, cancels both forward derivatives against the signed inverse
  derivatives, sums an arbitrary finite frequency support, and attaches the already proved
  Hamiltonian-time orientation.

The final declarations
`chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum` and
`chebyshevFirstMelnikovDisplacement_finiteDensity_eq_cellIntegral` respectively identify the
first energy displacement with the complete finite analytic-kernel formula and with the
independently compiled genuine original-cell set integral. Thus W4 is complete.

After importing `ChebyshevMelnikov` from `Hilbert16.lean`, the Windows-native root `lake build`
completed all 3522 jobs. The expanded `AxiomAudit.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for every new theorem. A source declaration scan found no
`sorry`, `admit`, project `axiom`, or proof-bypassing `unsafe`; the sole textual `admit` match is
ordinary English in a documentation comment in `CartesianRank.lean`.

### W3 common period-annulus completion

Still later on 2026-08-28, `Hilbert16/Spikes/ChebyshevPeriodAnnulus.lean` closed the remaining
geometric interface of W3. The file fixes the uniform energy ceiling `1/4`, proves that every
explicit positive-energy orbit below it lies strictly in its exact Chebyshev cell for every
`lambda ≥ 1`, and proves that its velocity never vanishes. It packages the cell annulus as the
union of these closed energy-orbit ranges and proves separation both between unequal energies and
between unequal cells.

For the finite-family persistence argument, the same file defines the image of a closed energy
band times one full angular period as a compact subannulus. These subannuli are nonempty, lie in
the common period annulus and physical rectangle, retain their exact Hamiltonian energy band, and
are disjoint under separated energy bands or distinct cell indices. The construction is the
geometric input for W9; Hamiltonian-time local flow and Poincaré return maps are not asserted here.

After root-importing the module, the Windows-native `lake build` completed all 3523 jobs.
`Hilbert16/AxiomAudit.lean` checked every new public declaration and again reported only `propext`,
`Classical.choice`, and `Quot.sound`.

### W0 carrier interface and W9 simple-zero analytic closure

Still later on 2026-08-28, the foundational layer acquired the explicit continuous linear
equivalence between `PhaseSpace` and `ℝ × ℝ`, the D003 polynomial-vector-field representation and
degree, and carrier-based `PeriodicOrbit` and `LimitCycle` structures. Periodic parametrizations
remain proposition-valued, are required to be nonconstant global integral curves, and do not enter
orbit identity.

`Hilbert16/Dynamics/SimpleRoot.lean` then specialized Mathlib's implicit-function theorem to a
scalar `C¹` zero. The resulting object records the root branch, its `C¹` regularity, the zero
equation, and the local iff giving uniqueness. A separate theorem proves that the energy derivative
stays nonzero along this branch. `NormalizedDisplacement.lean` proves the exact algebraic closure
for `P(mu,h)=h+mu*D(mu,h)`: at every sufficiently small nonzero parameter, the branch gives a fixed
point and its derivative is `1+mu*d_mu != 1`.

This closes the simple-zero/IFT/multiplier part of W9. Construction of the actual transverse return
map and proof that its normalized displacement is `C¹` with Melnikov trace at `mu=0` remain the
active high-risk obligation.

After root-importing both dynamics modules, the Windows-native `lake build` completed all 3532
jobs. The expanded axiom audit again reports only `propext`, `Classical.choice`, and `Quot.sound`.
A fresh source scan found no proof holes or project axioms; its two textual matches are ordinary
documentation prose in `GreenVertical.lean` and `CartesianRank.lean`.

### W9 transverse return time and unperturbed energy conservation

Still later on 2026-08-28, the dynamics layer added a genuine-flow interface rather than a
return-map assumption. `C1LocalFlow` contains an actual parameterized flow, an open domain with
interval-connected time fibers, the initial equation, and the ODE. `ChebyshevSection.lean` provides
an explicit energy-parametrized physical section point and proves that the actual Hamiltonian vector
field crosses its affine section transversely. `ChebyshevReturn.lean` therefore constructs a locally
unique `C¹` return time by the implicit-function theorem and a `C¹` Hamiltonian-energy displacement.

`EnergyConservation.lean` differentiates the exact Chebyshev Hamiltonian numerator `2H` along the
real ODE and proves the derivative is zero. The real mean-value theorem then gives conservation on
the full time segment. Positivity and continuity of the IFT return time, openness of the flow domain,
and interval-connected time fibers yield
`eventually_energyDisplacement_zero_unperturbed`: the genuine return displacement is exactly zero at
`mu=0` for every energy near the base orbit.

The Windows-native root `lake build` now completes all 3538 jobs. The enlarged axiom audit includes
the return-time, transversality, ODE, and conservation declarations and reports only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan still finds no proof holes or project axioms.
The remaining W9 work is construction of the common-time smooth flow from Picard iteration, the
`C¹` normalized quotient `Delta=mu*D`, and the exact equality of `D(0,h)` with the W4 Melnikov trace.

### W8 concrete polynomial primitive and degree audit

`Hilbert16/Degree.lean` now constructs the paper's algebraic objects inside
`MvPolynomial (Fin 2) ℝ`: coordinate embeddings of univariate Chebyshev polynomials, tensor modes,
finite densities, `q=T_n'(x)T_n'(y)S`, the polynomial Hamiltonian vector field, and the final
perturbed vector field. A coefficientwise `MvPolynomial.integrateAt` supplies the normalized
primitive `P`; both `pderiv 0 P=q` and the one-degree growth bound are proved.

Consequently, for `n>=2` and every actual density with total degree at most `2n-4`, the compiled
chain proves `deg q<=4n-6`, `deg P<=4n-5`, and
`finalVectorField_degree_le : degree(final field)<=4n-5`. The remaining W8 instantiation is only the
support/frequency theorem for the future global hierarchical density.

After importing `Degree.lean`, the Windows-native root build completes all 3542 jobs. All new W8
declarations were added to `AxiomAudit.lean`; the output again contains only `propext`,
`Classical.choice`, and `Quot.sound`.

### W5 three-adic visibility completion

`Hilbert16/Chebyshev/ThreeAdicVisibility.lean` now gives explicit finite parametrizations of the
paper's zero-based row layers and frequency bands.  It proves injectivity, exact cardinalities,
the row valuation and primitive-frequency predicates, pairwise disjointness, the balanced layer
product and the natural-number row sum.  The omitted central row is represented explicitly and its
numerator is proved to be `3^r`.

For the DCT weights, `threeAdic_lower_band_invisible` proves the exact zero for every `p<k`.
`modTwelveCharacter_mul` exhausts the four unit classes modulo `12`, and
`threeAdic_diagonal_cosine_factor` proves the paper's `sqrt(3)/2` frequency-sign/row-sign formula.
The tensor theorems then prove the coordinatewise visibility relation, diagonal replication and
nonvanishing.

After root-importing the module, the Windows-native `lake build` completed all 3543 jobs.  The new
declarations in `AxiomAudit.lean` report only `propext`, `Classical.choice`, and `Quot.sound`.

### W1 analytic rank-to-roots completion

`Hilbert16/Analytic/ValuationBasis.lean` proves the finite-dimensional Taylor elimination used in
Paper Lemma 2.1. Any separating sequence of coefficient linear functionals yields a basis with
strictly increasing leading indices. Applied to linearly independent convergent formal series,
the new basis functions factor as `h^q*g(h)` with analytic `g` and `g(0)≠0`.

`Hilbert16/Analytic/RankToRoots.lean` then applies Descartes' rule of signs to a sparse polynomial,
counts positive roots with multiplicity, and proves that the prescribed roots are simple. The
factored valuation basis supplies a jointly `C¹` scaled equation; the scalar implicit-function
theorem produces locally unique positive simple branches and proves
`h_s(τ)=τρ_s+o(τ)`. The final theorem `rankToSimplePositiveRoots` expands the construction back
into the original analytic family and covers `d=0` (`m=1`) without a separate exceptional axiom.

After root-importing both analytic modules, the Windows-native `lake build` completed all 3548
jobs. The W1 declarations in `AxiomAudit.lean` use only `propext`, `Classical.choice`, and
`Quot.sound`; the source scan found no proof holes or project axioms.

### W2 finite-poset hierarchical realization completion

`Hilbert16/Hierarchy/Realization.lean` defines the normalized response for an arbitrary finite
partially ordered layer type. It proves exact diagonal reduction at `zeta=0`, joint `C¹` regularity
near every selected root, and an exact power identity relating the normalized object to the actual
weighted response. Scalar implicit-function branches are constructed for every finite cell/root
pair, and their eventual neighborhoods are intersected to obtain one common positive `zeta`
threshold. The power identity then preserves both the zeros and their nonzero derivatives in the
single unnormalized response.

The same module composes this construction with W1: `exists_simpleRootCombination_of_rank` selects
one fixed coefficient vector and all required positive simple roots from each linearly independent
analytic family. The final `hierarchicalRealization` theorem therefore returns original-family
coefficients and simultaneous positive simple roots, not an assumed block-root interface.

After root-importing the module, the Windows-native `lake build` completed all 3549 jobs. The five
W2 audit entries use only `propext`, `Classical.choice`, and `Quot.sound`; the source scan found no
proof holes or project axioms.

### W10 exact finite-index count

`Hilbert16/Counting/ThreeAdicCycles.lean` defines `ThreeAdicCycleIndex r`, whose dependent fields
record two actual layers, two actual row parameters, and a root in the corresponding
`d_k d_l - 1` block. Its cardinality is reduced to the real finite double sum and then to the
closed Eq. (6.7) expression. The auxiliary `threeAdic_count_sub_le` proves that the final
natural-number subtraction is not truncated.

Thus `card_threeAdicCycleIndex` is the `ℕ`-valued cardinality theorem needed for a later injective
family of limit cycles; it no longer relies on interpreting an integer identity as a count.

After root import together with W11, the Windows-native `lake build` completed all 3551 jobs. The
W10 count declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

### W11 all-degree asymptotics

`Hilbert16/Asymptotics.lean` proves that the exact count at every `r≥2` strictly dominates
`3^(2r)r²/9`. For every `N≥31`, `allDegreeIndex` uses `Nat.log` to choose consecutive three-adic
scales and proves the exact degree bracket. Casting its upper inequality to `ℝ`, applying strict
monotonicity of `Real.log`, and using `Real.log_pow` yields the two inequalities in Eq. (6.11).
Their product is the explicit Eq. (6.12) lower bound.

The final `hilbert_lower_bound_asymptotic` is stated for an arbitrary monotone lower-bound function
with the compiled subsequence premise. It takes `N₀=144` and the concrete positive constant
`1/(5184*(log 3)^2)` to prove the standard quantified
`Omega(N²(log N)²)` conclusion. This module is independent of the remaining ODE construction and
can be instantiated immediately when the main subsequence theorem closes.

The root build completed all 3551 jobs, and every W11 audit entry reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### W8 actual three-adic global density

`Hilbert16/Degree/ThreeAdicDensity.lean` defines the dependent finite type of all genuine
three-adic tensor modes. Each actual frequency is odd and strictly below the odd degree `3^r`, so
Lean proves the sharpened bound `a≤3^r-2`; every tensor mode therefore satisfies
`a+b≤2*3^r-4`.

`threeAdicHierarchicalDensityPolynomial` is the paper's single finite polynomial sum with the
one-based `zeta^((k+1)+(l+1))` hierarchy and arbitrary selected block coefficients. Its total
degree is at most `2*3^r-4`, and
`threeAdicHierarchicalFinalVectorField_degree_le` instantiates the complete polynomial primitive
chain to prove the final field degree at most `4*3^r-5`.

### W9 exact perturbed-energy factorization and genuine-time trace

`Hilbert16/Dynamics/MelnikovIntegral.lean` defines the normalized displacement directly as the
integral of an energy-production observable along the actual return trajectory. The interval FTC
proves the generic exact identity `Delta=mu*D` from a pointwise energy derivative, with no quotient
or remainder term.

`Hilbert16/Dynamics/PerturbedEnergy.lean` then defines the paper's physical perturbation
`(H_y+mu*P,-H_x)` and proves by an explicit polynomial chain rule that
`dH/dt=mu*H_x*P`. The generic hypothesis is thereby discharged from the ODE field itself.
At zero perturbation, the normalized time integral is also proved exactly equal to `-∫P dy` along
the genuine return curve, and that physical curve is verified to have Hamiltonian velocity.

After root-importing W8 and both new W9 modules, the Windows-native `lake build` completed all
3555 jobs. The enlarged axiom audit completed successfully and every new declaration reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### W9 actual polynomial field and Hamiltonian-oriented one-turn trace

`Hilbert16/Dynamics/PolynomialPerturbation.lean` now proves that the degree-audited
`finalPolyVectorField` evaluates exactly to the perturbed field used by the ODE layer.  Polynomial
evaluation is proved `ContDiff` by coefficient induction, the actual field is jointly `C¹` in
parameter and phase point, and the parameter-lifted Picard theorem supplies a genuine local
integral curve through every initial point.

`Hilbert16/Spikes/ParameterizedPdy.lean` now contains exact affine and monotone-clock
reparametrization theorems.  `Hilbert16/Spikes/HamiltonianAngularTrace.lean` uses the checkerboard
orientation to construct an explicit one-turn curve, proves both coordinate derivatives, proves
its tangent is a strictly positive scalar reparametrization of the Hamiltonian vector, and proves
its `P dy` trace is exactly W4's compiled Hamiltonian-oriented trace.  The same module also proves
the traversal closes after `2*pi`, remains on the prescribed energy and inside its cell, and has
nowhere-zero angular velocity for positive energy.

After root-importing both modules, the Windows-native `lake build` completed all 3558 jobs.  The
expanded `AxiomAudit.lean` also completed successfully; all new declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

### W9 integrated Hamiltonian clock and genuine-time W4 trace

`Hilbert16/Spikes/HamiltonianTimeClock.lean` integrates the reciprocal positive angular factor,
proves continuity, strict monotonicity and positivity of the one-turn period, and constructs the
order isomorphism from angular time `[0,2*pi]` to physical time `[0,T]`.  Its extended inverse has
the expected derivative on `(0,T)` and sends the endpoints to `0` and `2*pi`.

Composing the explicit oval with this inverse gives a genuine physical-time solution of the
Hamiltonian ODE, proved in both coordinates.  For every continuous one-form coefficient `P`, the
monotone substitution theorem proves that this solution's one-period `P dy` trace equals the W4
Hamiltonian-oriented angular trace.  Consequently the compiled first Melnikov displacement is
exactly the negative physical-time trace.  The inverse clock is also proved to be a right inverse
on the angular interval, and `chebyshevHamiltonianTimeOrbit_sectionPoint` identifies the explicit
physical time at which this solution passes through the horizontal Poincaré-section base point.

After root import, the Windows-native `lake build` completed all 3559 jobs.  The enlarged axiom
audit passed; every new time-clock declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.  A source scan still finds no proof holes or project axiom declarations; its only
matches are the existing words `admit` and `axiom` inside documentation comments.

### W9 section-based positive return and public phase-space bridge

`Hilbert16/Spikes/HamiltonianSectionClock.lean` shifts the integrated positive clock so physical
time zero is exactly the chosen horizontal Poincare-section base point.  It proves global angular
`2*pi` periodicity, strict monotonicity and positivity of the shifted one-turn period, constructs
the inverse clock, and proves both Hamilton equations on the open physical-time period.  The
explicit solution equals the cell orbit at angular zero both initially and after the strictly
positive period.

`Hilbert16/Dynamics/ChebyshevExplicitReturn.lean` transports this solution to the project's public
`PhaseSpace`.  The compiled endpoint theorems identify time zero and the positive-period endpoint
with `chebyshevPhaseSectionPoint`; the transported coordinate derivative theorems identify its
velocity with `chebyshevPhaseHamiltonianVector`.  A global first hit of the unlocalized horizontal
line is deliberately not asserted: the opposite point is another half-period intersection, while
the existing return-time IFT selects the local branch near the full positive period.

After both modules were root-imported, the Windows-native `lake build` completed all 3561 jobs.
The enlarged axiom audit passed; all new declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

### W9 compact-ball ODE uniqueness and genuine-flow W4 identification

The section inverse clock is now built on a padded angular interval while retaining the same
`[0,T]` endpoint formulas.  This gives two-sided derivatives at physical time zero and at the
positive return period.  Periodicity of the angular orbit, angular velocity, and interval integral
proves `chebyshevHamiltonianSectionTimePdy_eq_angularPdy`: moving the clock origin to the section
does not change the compiled W4 trace.

`Hilbert16/Dynamics/ChebyshevFlowIdentification.lean` proves the Hamiltonian polynomial vector
field is `C¹`, encloses both compact trajectory images in one closed ball, obtains a Lipschitz
constant on that convex compact ball, and applies Mathlib ODE uniqueness.  Consequently every
genuine zero-parameter `C1LocalFlow` covering the explicit period segment agrees with the explicit
section-clock curve on the entire interval and returns to the same base point.  The new
`chebyshevReturnSetupOfSectionPeriod` constructor fills the return equality automatically, and its
zero-parameter Melnikov factor is proved equal to the negative W4 angular trace.

After root import, the Windows-native `lake build` completed all 3562 jobs.  The enlarged axiom
audit passed with only `propext`, `Classical.choice`, and `Quot.sound`.

### W9 local C¹ parameter integrals and actual return-map persistence

`Hilbert16/Dynamics/ParametricIntegralC1.lean` proves reusable fixed- and variable-endpoint
parameter-integral theorems.  The local versions assume `C¹` only on an open neighborhood of the
compact base fiber.  Their proofs use a partial Fréchet derivative, compact uniform derivative
bounds, Mathlib differentiation under the integral, and a rescaling of the variable interval to
`[0,1]`; no global smoothness of the supplied flow is assumed.

`Hilbert16/Dynamics/MelnikovIntegral.lean` applies this result to a genuine return trajectory and
proves `ChebyshevReturnSetup.contDiffAt_melnikovIntegral`.  In
`Hilbert16/Dynamics/PerturbedEnergy.lean`, the actual energy-production observable `H_x P` is
proved `C¹`, giving `ChebyshevReturnSetup.contDiffAt_actualMelnikov` for the actual normalized
factor `D(mu,h)`.

`Hilbert16/Dynamics/MelnikovPersistence.lean` constructs one open admissible neighborhood on which
the energy remains in range, the return time stays positive, and every point of the scaled return
segment lies in the flow domain.  On this neighborhood the exact actual factorization and the
equality between the actual and normalized energy return maps hold.  Consequently
`eventually_energyReturnMap_fixed_and_hyperbolic` proves that a simple actual Melnikov zero yields,
for every sufficiently small nonzero parameter, a fixed point of the actual energy return map with
multiplier different from `1`.

After root-importing the new persistence module, the affected Windows-native `lake build` completed
all 3566 jobs.  The expanded axiom audit passed; every new declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

### W9 Banach-Picard C¹ local-flow construction

`Hilbert16/Dynamics/SmoothLocalFlow.lean` defines continuous normalized curves on `[-1,1]`, the
Volterra operator, the actual polynomial Nemytskii field, and the scale-dependent Picard residual.
At scale zero its curve derivative is the identity, so Mathlib's Banach-space implicit-function
theorem produces a local `C¹` curve branch.

`SmoothLocalFlowDynamics.lean` proves that zero residual rescaled by a nonzero physical time solves
the actual lifted ODE.  Compact-ball Lipschitz uniqueness makes endpoints of overlapping branches
equal.  `SmoothLocalFlowConstruction.lean` shrinks branches to good open balls, glues their
endpoints, proves joint `C¹` regularity, the physical-time ODE law, interval-connected time fibers,
and preservation of the frozen parameter coordinate.  The planar second coordinate is packaged as
the genuine `chebyshevPolynomialC1LocalFlow`.

The Windows-native build completed all 3569 jobs, including the root module and expanded axiom
audit.  Every new declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The remaining flow obligation is finite continuation along the compact target period segments;
the common zero-time jointly smooth local flow itself is no longer assumed.

### W9 finite compact-period C¹ flow continuation

`Hilbert16/Dynamics/SmoothLocalFlowContinuation.lean` turns compactness of the explicit section
orbit into a uniform Picard time tube, subdivides the positive period into finitely many equal
steps, and uses compact-ball ODE uniqueness to identify every fixed-step iterate with the exact
Hamiltonian orbit mesh point.  It also proves that consecutive physical-time continuation charts
agree on arbitrary overlaps.

`Hilbert16/Dynamics/SmoothLocalFlowFinite.lean` restricts these charts to overlapping open time
strips.  Nonconsecutive strips are disjoint, so adjacent compatibility makes chart selection
value-independent.  The resulting finite union map is jointly `C¹`; its open time fibers are
star-shaped about zero and hence intervals.  Its planar component is packaged as
`chebyshevPolynomialFiniteC1LocalFlow`, which satisfies the actual degree-audited polynomial ODE
and whose domain contains the entire requested section-period segment.

This removes the last flow-construction hypothesis from the W9 return-map chain.  The remaining
dynamical work is isolated-periodic-orbit packaging, a common nonzero parameter for the finite
family, and the carrier-injection/counting assembly.

### Concrete local three-adic hierarchy

`Hilbert16/Hierarchy/LocalRealization.lean` strengthens rank-to-roots by selecting every fixed
simple root inside an arbitrary positive interval `(0,R)`.  Its local hierarchy theorem only asks
for basis responses to be `C¹` on that interval and proves that all continued roots remain in it.
`analyticKernel_contDiffOn_Ioo_quarter` derives the required local regularity from the explicit
quarter-radius summability majorant.

`Hilbert16/Hierarchy/ThreeAdicRealization.lean` instantiates the result with the actual dependent
three-adic tensor layers, rows, and frequencies.  It compiles the finite common anisotropic Taylor
rank into formal-series rank, includes the nonzero frequency characters, proves triangular
invisibility and the row/frequency diagonal factorization, and obtains one family of simultaneous
positive simple roots with `h < 1/4`.

After root-importing both modules, the Windows-native root and axiom-audit build completed all 3573
jobs.  Every audited new declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

### Actual three-adic polynomial return chain and common parameter

`Hilbert16/Dynamics/PolynomialPrimitive.lean` proves that evaluating
`MvPolynomial.integrateAt 0` is exactly the canonical first-coordinate interval primitive used by
the geometric Melnikov calculation.  `ThreeAdicMelnikov.lean` identifies the actual hierarchical
finite density with the compiled mode-kernel response, while `ThreeAdicPolynomialBridge.lean`
proves that the degree-audited density and primitive polynomials evaluate pointwise to those same
functions.  Thus the simultaneous three-adic simple roots are simple roots of the actual
polynomial perturbation's first Melnikov displacement.

`Hilbert16/Dynamics/ReturnMelnikovGerm.lean` proves joint `C¹` regularity of the physical angular-time
density and the energy-dependent section period.  A compact scaled-period tube, ODE uniqueness, and
the local uniqueness of the return-time IFT identify the genuine zero-parameter return factor with
the W4 displacement on an energy neighborhood, rather than only at one energy.

`Hilbert16/Dynamics/ThreeAdicReturnPersistence.lean` packages the resulting actual finite flow,
return setup, simple Melnikov root, continued fixed point, and nonunit multiplier for every exact
`ThreeAdicCycleIndex r`.  A finite intersection then selects one common positive perturbation
parameter for the whole family in `threeAdicPolynomialCommonReturnParameter`.

After root-importing all five bridge modules, the Windows-native `lake build` completed successfully
with 3577 jobs.  The expanded `AxiomAudit.lean` also completed successfully; every newly audited
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.  The remaining dynamics
work is global periodic-integral-curve packaging, carrier isolation, and carrier disjointness/injection.

### Global periodic carriers, root-slot injection, and finite separation

`Hilbert16/Dynamics/PeriodicExtension.lean` now repeats a closed positive-time return segment on
the whole real line using floor/fract coordinates and proves the seam derivative.  Together with
`ReturnEndpoint.lean` and `ReturnPeriodicOrbit.lean`, this packages every continued return fixed
point as a genuine global `PeriodicOrbit`.  `ThreeAdicPeriodicOrbit.lean` selects one common
positive parameter for the entire exact cycle-index family.

The analytic and hierarchy layers now preserve root-slot injectivity all the way from
`ScaledSimpleRootFamily.eventually_root_injective` to the concrete polynomial return certificates.
`ThreeAdicOrbitGeometry.lean` proves injectivity of the physical row-pair label and pairwise
disjointness of the corresponding compact unperturbed carriers.  `ReturnCarrierStability.lean`
normalizes the varying return segment to `[0,1]`; joint `C¹` continuity and the generalized tube
lemma keep the entire actual periodic carrier inside any prescribed open neighborhood.
`FiniteCompactSeparation.lean` simultaneously separates a finite pairwise-disjoint compact family
by pairwise-disjoint open supersets.  The resulting theorem
`threeAdicPolynomialCommonSeparatedPeriodicOrbits` gives, at one common positive parameter,
pairwise-disjoint global periodic carriers for all exact three-adic cycle indices.

`PeriodicOrbitUniqueness.lean` proves that periodic carriers of a `C¹` autonomous field which share
a point are equal.  `ReturnIsolation.lean` proves isolation of a scalar return fixed point from a
nonunit multiplier and exposes the final conditional carrier-isolation theorem.  The remaining
geometric obligation is to show that every periodic carrier inside a sufficiently small return tube
hits the selected local section.

The Windows-native root build completed all 3587 jobs.  The expanded axiom audit completed
successfully; every newly audited declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

### Final return-tube isolation and end-to-end main theorems

`AngularSection.lean` proves that a differentiable periodic planar trace with nonzero radius and
strict angular cross product must meet the positive ray.  `ChebyshevAngularSection.lean` transfers
this to the actual perturbed Chebyshev field on one uniform open tube.  `ReturnTubeSection.lean`
identifies positive-ray hits with the energy-parametrized local section and proves that the actual
return endpoint remains on that ray.

`MonotoneReturn.lean` proves both order preservation of the normalized return map on a fixed compact
energy interval and convergence of every interval-confined iterate sequence to a fixed point.
`ReturnTubeIsolation.lean` combines this with repeated local-flow segments, carrier closedness, the
uniform simple-root uniqueness neighborhood, and autonomous ODE uniqueness.  Thus every continued
periodic orbit is isolated for all sufficiently small nonzero parameters.

`threeAdicPolynomialCommonSeparatedPeriodicOrbits` now selects one common positive parameter at
which all exact cycle-index carriers are simultaneously isolated and pairwise disjoint.
`exists_threeAdicPolynomialVectorField_with_limitCycles` reindexes them by
`Fin (cycleLowerBound r)` and evaluates the final degree-audited polynomial field.  `Main.lean`
exports the exact subsequence statement and a direct all-degree existential theorem with the
explicit positive `N²(log N)²` lower bound.

On 2026-08-28 the Windows-native full command `lake build` completed successfully with 3593 jobs.
`lake env lean Hilbert16/AxiomAudit.lean` then completed successfully.  Every newly added isolation
and main theorem reports exactly the standard logical foundations `propext`, `Classical.choice`,
and `Quot.sound`; no project-specific axiom appears.
