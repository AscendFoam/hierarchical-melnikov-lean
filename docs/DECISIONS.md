# Hilbert 16 Lean design decisions

Last updated: 2026-08-28

The decisions below are binding for the main proof branch. A change requires a new dated entry that
records the affected declarations and a successful full rebuild before and after the change.

## D001 — Frozen environment

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib tag: `v4.33.1`
- Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`
- Dependency resolution: the committed `lake-manifest.json`; routine development must not run
  `lake update`.
- Primary development platform: Windows x86_64 using native Elan/Lake.
- WSL2 is a fallback only. Windows and Linux must not alternately build the same checkout because
  `.lake` contains platform-specific artifacts.

Rationale: the current source workspace is on `D:` and the native build avoids `/mnt/d` filesystem
overhead and duplicate platform caches.

## D002 — Phase space

Use

```lean
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 2)
```

as the canonical phase space. Coordinate calculations may use an explicit continuous linear
equivalence with `ℝ × ℝ`, but public dynamics declarations use `PhaseSpace`.

Rationale: `Fin 2` aligns with `MvPolynomial (Fin 2) ℝ`, while `EuclideanSpace` supplies the complete
normed and inner-product structures needed by ODE, Fréchet derivative, and Jacobian theorems.

## D003 — Polynomial vector fields and degree

Represent a polynomial vector field by two coordinate polynomials:

```lean
abbrev PolyVectorField := Fin 2 → MvPolynomial (Fin 2) ℝ
```

Define its analytic evaluation separately. Its degree is the maximum `totalDegree` of the two
coordinates, with the zero polynomial following Mathlib's existing convention. The final theorem
uses `X.degree ≤ N`, not equality.

## D004 — Periodic-orbit identity

The identity of a periodic orbit is its carrier set in `PhaseSpace`, not a selected base point,
period, or parametrization. A periodic-orbit structure therefore stores `carrier : Set PhaseSpace`
and a proposition-valued existence certificate for a periodic integral curve with that image.

Rationale: time translations and changes of starting point must not create distinct limit cycles.
Disjoint annular neighborhoods will prove inequality of carriers in the final injection.

## D005 — Limit cycle and hyperbolicity

- A limit cycle is a periodic-orbit carrier isolated among nearby periodic-orbit carriers.
- Hyperbolicity is certified by a local transverse Poincare map whose derivative at the fixed point
  is not `1`.
- The dynamics package must prove that this certificate implies isolation; it is not an input axiom.

## D006 — Analytic representatives

Do not introduce a stalk/germ quotient in the main proof. Each finite family of analytic functions
is represented on one explicit open interval containing `0`, together with `AnalyticOnNhd` or
`AnalyticAt` facts and restriction lemmas.

Rationale: the paper only uses finitely many germs at each stage, so a common interval removes
quotient bookkeeping and makes `C¹` estimates and root neighborhoods explicit.

## D007 — Counting interface

The core lower-bound predicate is

```lean
∃ C : Fin L → HyperbolicLimitCycle X, Function.Injective C
```

Do not define the Hilbert number as a natural number. The optional paper notation `H(N)` may later
be represented by a supremum in an extended cardinal/ordered type, but it is not needed to prove the
existence lower bound.

## D008 — Main theorem arithmetic

Use the division-free natural-number expression

```lean
(2 * 3 ^ (r - 1) * r) ^ 2 - (3 ^ r - 1) ^ 2
```

and separately prove, under `2 ≤ r`, that subtraction is not truncated and that its real coercion
equals the paper's expression with denominator `9`.

## D009 — Parameter order

The construction fixes parameters only in the order

```text
n → lambda_n → block coefficients/root scales/intervals → zeta → mu.
```

Every uniform-threshold theorem must expose this quantifier order. No lemma may choose `lambda`,
`zeta`, or `mu` through a circular dependency.

## D010 — Scope of new analytic foundations

Prove specialized theorems sufficient for `main.tex`:

- the Gauss connection formula only for `a=-alpha/2`, `b=alpha/2`, `c=1`, and the negative real axis;
- the change-of-variables/Green identity only for the explicit Chebyshev cell domains;
- Poincare--Pontryagin persistence first for the explicit compact Hamiltonian annuli.

General libraries are extracted only after the specialized theorem compiles and has another caller.

## D011 — Spike policy

High-risk experiments live under `Hilbert16/Spikes/`, contain no `sorry`, and compile independently.
They may establish only a strict subset of the final theorem, but their comments must state the next
missing implication. A spike that passes its Go criterion is moved into a responsibility-based final
module and added to the public axiom audit.

## D012 — Proof and release audit

- No `sorry`, `admit`, project `axiom`, or proof-bypassing `unsafe` declaration in the import closure
  of `Hilbert16.lean`.
- Standard Lean/Mathlib logical axioms are allowed and are listed by `#print axioms`.
- Finite-field and symbolic scripts are regression checks only.
- Every `proved` row in `PROOF_MAP.md` must compile in the root library and in a clean clone.

## D013 — B1 analytic continuation boundary

Mathlib's `ordinaryHypergeometric` is used only where its defining series converges. In
particular, no declaration may interpret `gaussBorelImage alpha (-x)` as a continued value for
`x > 1`, because the locked Mathlib implementation returns a junk value outside the series radius.

The canonical specialized continuation is `gaussEulerContinuation`, the Euler integral for
`a=-alpha/2`, `b=alpha/2`, `c=1`, implemented as expectation under Mathlib's
`Beta(alpha/2, 1-alpha/2)` probability measure. This representation reuses the library's proof of
the Gamma normalization and endpoint integrability and exposes an almost-everywhere unit-interval
support interface for dominated convergence. The negative-axis formula is represented by the proposition
`NegativeAxisConnectionFormula alpha`, comparing that integral at `-x` with
`negativeAxisConnectionRHS alpha x`.

Both analytic-continuation obligations are now proved. `gaussEulerContinuation_eq_borelImage`
identifies the Euler/Beta representative with the original Borel series on `|s|<1`, while
`negativeAxisConnectionFormula` proves the exact connection identity for `x>1`. The latter is
obtained internally from the specialized hypergeometric ODE, Beta-integral differentiation and
integration by parts, two infinity coefficients, and a conserved scaled Wronskian. No general DLMF
connection identity and no project axiom are imported.

## D014 — B1 uniqueness mechanism

For the specialized negative-axis equation

```text
x(1+x) y'' + (1+x) y' - (alpha/2)^2 y = 0,
```

the canonical uniqueness proof uses `x` times the Wronskian. This scaled Wronskian has derivative
zero. The two Frobenius branches are normalized by the pair consisting of their leading
`x^(alpha/2)` coefficient and the decay operator
`x^(alpha/2) (x y' - (alpha/2)y)`. Their limiting data are respectively `(1,0)` and
`(0,-alpha)`, so their mutual scaled Wronskian is the nonzero constant `-alpha`.

Rationale: this avoids importing a general complex analytic-continuation theorem and uses exactly
the two boundary coefficients computed from the Euler/Beta integral.

## D015 — B1 differentiated relation and exponent separation

Paper Lemma 5.1 is proved with the uniform derivative order `e - 1`, rather than selecting the
largest shift appearing in the support of a hypothetical relation. The `q`-th shifted series then
becomes derivative order `e - 1 - q`, and its negative-axis leading exponent is

```text
q + alpha_i / 2 - (e - 1).
```

The Euler/Beta continuation is first proved real analytic on `x>0` by an explicit local
binomial/Beta power series. This lets the relation established on `0<x<1` propagate to every
`x>0` using Mathlib's real-analytic identity theorem. Arbitrary differentiated asymptotics are then
proved directly by dominated convergence. Since `0<alpha_i<1`, distinct integer shifts cannot
cancel the fractional exponent difference; injectivity of the parameters therefore gives pairwise
distinct exponents. A reusable finite maximal-exponent lemma closes linear independence.

Rationale: the fixed order removes support-dependent bookkeeping, keeps every derivative order
natural, and exposes a theorem with exactly the finite quantifiers required by Paper Lemma 5.1.

## D016 — W7 polynomial normalization and finite-minor selection

Normalize the Borel coefficient as

```text
U_m(beta) = ((-1)^m / (4^m m!)) P_m(beta^2),
```

where `P_m` is monic of degree exactly `m`. Thus the first `e` coefficient columns at distinct
positive `beta_j` form a polynomial Vandermonde matrix in the pairwise-distinct nodes `beta_j^2`.
The anisotropic column transform is performed on these normalized beta columns before taking
`lambda → ∞` coefficientwise.

For the alpha/shift rows, do not assume that the first `d*e` Taylor coefficients contain a
nonzero minor. Instead, derive an arbitrary finite evaluation minor from functional linear
independence via Mathlib's `span_flip_eq_top_iff_linearIndependent`; its selected natural-number
rows are then held fixed throughout the determinant limit. This exactly preserves the paper's
existential finite-minor argument and avoids an unjustified initial-segment strengthening.

Rationale: this split makes every determinant factor explicit and nonzero. The convergent analytic
realization is supplied separately by `Hypergeometric/AnalyticKernel.lean`; W4 only needs to identify
the geometric cell integral with that already constructed kernel.

## D017 — W7 analytic-kernel convergence majorant

Construct the Eq. (3.12) kernel as the sum of the scalar formal power series with coefficients

```text
(2^m/(m+1)!) * formalProductRow alpha beta lambda m.
```

For `lambda ≥ 1`, dominate its norm at radius `1/4` by the Cauchy product of the two nonnegative
Borel majorants

```text
|U_m(alpha)| / m! * (1/2)^m.
```

Each majorant is summable because the corresponding ordinary `₂F₁` Borel series has exact radius
one. The termwise comparison uses `p!(m-p)! ≤ (m+1)!` and
`|lambda⁻¹|^(m-p) ≤ 1`. Mathlib's formal-series radius theorem then yields a positive convergence
radius, and one-dimensional power-series uniqueness lifts coefficient-sequence independence to
independence of the actual analytic functions.

Rationale: this gives a project-internal convergence proof with a fixed uniform witness (`1/4`),
avoids assuming convergence of the divergent formal `₂F₀` factors themselves, and keeps the later
geometric integral identification independent from Proposition 5.2's rank argument.

## D018 — W4 disk moment through the actual polar-coordinate Jacobian

Represent the normalized Cartesian disk as the measurable subset

```text
{(x,y) : ℝ × ℝ | x^2 + y^2 < 2h}.
```

Prove the radial moment by `intervalIntegral.integral_pow`. Prove the mixed angular beta integral
without an endpoint-singular substitution: integration by parts gives

```text
(2q+1) I(p+1,q) = (2p+1) I(p,q+1),
I(p,q) = I(p+1,q) + I(p,q+1),
```

and Mathlib's Wallis product supplies the base row. Extend from the first quadrant to
`(-π,π)`, separate the polar rectangle by `setIntegral_prod_mul`, and finally invoke
`integral_comp_polarCoord_symm`. The indicator of the Cartesian disk vanishes on the portion of
the polar target outside `0 < r < √(2h)`, so the change-of-variables theorem yields the exact
general moment in Paper Eq. (3.11).

Rationale: the public theorem is connected to a genuine Cartesian set integral and Mathlib's
proved Jacobian formula. No informal polar-coordinate rule or coefficient-level disk-moment axiom
is introduced. The open disk is used at this stage; replacing it by the paper's closed disk only
requires the boundary-null equivalence and does not alter the integral.

## D019 — W4 cosine--arcsine expansion and dominated antidiagonal integration

Realize each mode by the exact identity

```text
cos(alpha * arcsin u)
  = ∑ p, ordinaryHypergeometricCoefficient (-alpha/2) (alpha/2) (1/2) p * u^(2p)
```

for `0<alpha<1` and `|u|<1`. The identity is proved internally: both sides solve the same
Chebyshev ODE, their scaled Wronskian vanishes, and real-analytic uniqueness propagates the local
equality throughout `(-1,1)`. Absolute summability then makes the two-mode product a genuine
Cauchy antidiagonal series.

For `0<h<1/4` and `lambda≥1`, integrate each finite antidiagonal using the already proved Cartesian
disk moment. Bound the integral of its norm by `(2*pi*h)` times `analyticKernelMajorant`; the latter
is summable. Mathlib's dominated `hasSum_integral_of_summable_integral_norm` therefore exchanges
the infinite sum with the restricted disk integral. The resulting public theorem
`normalizedModeDiskIntegral_eq_analyticKernel` identifies the actual normalized mode integral with
the convergent Eq. (3.12) analytic kernel.

Rationale: the geometric-to-analytic bridge now rests on absolute convergence and a checked
Lebesgue-integral majorant, not on formal coefficient manipulation. Ellipse scaling and the
signed Chebyshev-cell inverse branches remain separate geometric obligations.

## D020 — W4 ellipse scaling and cell orientation are separate from Green orientation

Scale the elliptic energy disk by the one-dimensional Haar-measure identity
`w = sqrt(lambda) * v` inside a Fubini decomposition. This produces the exact
`lambda^(-1/2)` area factor and reduces the even--even mode integral to the already audited
Cartesian disk kernel.

For a Chebyshev cell, use the explicit branch

```text
x_i(u) = cos(phi_i + epsilon_i * arcsin(u) / n),
epsilon_i = (-1)^(i+1).
```

The branch angle lies in `(0,pi)`, so its sine is positive and
`(-epsilon_i) * x_i'(u) > 0`. Therefore the two-dimensional inverse-Jacobian orientation is the
constant `epsilon_i * epsilon_j ∈ {±1}` and is nonzero. Keep this change-of-variables orientation
separate from the Green/orbit orientation until the original `(x,y)` set-integral theorem is
proved; only their final product should be named the paper's `sigma_ij`.

Rationale: this prevents the phrase “the sign is absorbed by `sigma_ij`” from hiding either a
Jacobian sign error or an orbit-orientation convention. The compiled pulled-back cell formula is
already exact, while the remaining Green/orbit bridge stays visibly open.

## D021 — Define the original cell as the inverse-branch image and use the general Jacobian theorem

Define the original `(x,y)` energy region of cell `(i,j)` as the image of the measurable elliptic
disk under the product inverse branch. Apply Mathlib's
`integral_image_eq_integral_abs_det_fderiv_smul` to that inverse map. This avoids silently treating
a curvilinear cell as a rectangle and supplies measurability of the image through the theorem's
differentiable injective-map machinery.

The proof separately establishes:

```text
det D(x_i,x_j) = x_i'(u) x_j'(v),
T_n'(x_i(u)) x_i'(u) = 1,
abs(x_i'(u) x_j'(v)) = epsilon_i epsilon_j x_i'(u) x_j'(v).
```

Thus the original density factor `T_n'(x)T_n'(y)` cancels the absolute inverse Jacobian and leaves
exactly the already certified cell orientation. The final theorem connects an actual original-cell
set integral—not merely a syntactic pulled-back integral—to the analytic kernel.

Rationale: defining the cell as an inverse image branch image makes injectivity and surjectivity
explicit and keeps all measure-theoretic obligations inside a standard Mathlib change-of-variables
theorem. Green's formula and closed-orbit orientation remain a separate W4 theorem.

## D022 — Split Green's formula into a vertical FTC identity and orbit identification

Mathlib `v4.33.1` has a rectangle divergence theorem and a general curve-integral API, but no
ready-made Green theorem for an arbitrary differentiable Jordan cell. Do not introduce a project
axiom to bridge that gap. Instead define `verticalBoundaryPdy` as the `P dy` contribution of the
right graph traversed upward minus the left graph traversed upward. For the canonical primitive

```text
P(x,y) = integral from 0 to x of q(s,y) ds,
```

one-dimensional FTC and additivity of interval integrals prove pointwise that the graph difference
is `integral from left(y) to right(y) of q(x,y) dx`; integrating in `y` gives the vertical Green
identity. Adding a function of `y` cancels between the two graphs.

Keep the remaining statement separate: the actual Hamiltonian energy orbit must be parameterized
as these two graphs, its Mathlib curve integral must equal `verticalBoundaryPdy`, and its time
direction must be computed. This is the only Green-specific geometry still open after the finite
density theorem.

Rationale: the difficult Jordan-boundary topology is reduced to an explicit orbit calculation,
while the analytic line-to-area step is already compiled and axiom-free.

## D023 — Parametrize the orbit in ellipse angle before proving the graph integral

Use the counterclockwise ellipse

```text
u(t) = sqrt(2h) cos(t),
v(t) = sqrt(2h) / sqrt(lambda) sin(t)
```

and compose it with the two explicit Chebyshev inverse branches. This keeps endpoint square-root
singularities out of the derivative proof. `ChebyshevOrbit.lean` proves that the resulting curve is
closed, lies exactly on `H=h`, and has the stated coordinate derivatives. It also proves

```text
sqrt(lambda) T_n'(x(t)) T_n'(y(t)) * orbitVelocity(t) = -X_H(orbit(t))
```

and proves that the scalar on the left has the cell-Jacobian sign. Thus the Hamiltonian-time
orientation is formally fixed and no longer delegated to a convention.

The remaining line-to-area obligation is deliberately narrower: define the parameterized `P dy`
integral, split the angular ellipse into its two vertical graphs (or prove an equivalent interval
substitution theorem), and identify it with `verticalBoundaryPdy`. The already compiled time-sign
and absolute-Jacobian sign then combine to the paper's `sigma_ij`.

Rationale: the smooth angular parametrization proves the dynamical geometry without first handling
the square-root graph endpoints; the graph representation is needed only for the final integral
identity.

## D024 — Close W4 by graph substitution, vertical Fubini, and signed derivative cancellation

The open clauses in D022--D023 are discharged in four explicit layers:

```text
angular physical P dy
  = pulled ellipse angular Q dv
  = upward right graph minus upward left graph
  = vertical slices of the pulled finite density
  = finite analytic-kernel sum.
```

`ParameterizedPdy.lean` proves the reusable one-dimensional graph-reparameterization theorem.
`EllipticOrbitPdy.lean` identifies the two angular half-arcs with the right and left ellipse graphs.
`EllipticSlice.lean` proves Fubini for the exact open ellipse and its vertical intervals.
`ChebyshevMelnikov.lean` proves joint continuity of the canonical primitive, substitutes each
Chebyshev inverse branch in the inner interval integral, and cancels
`T_n'(x_i(u)) x_i'(u)=1` and `T_n'(y_j(v)) y_j'(v)=1` before integration.

Define the Hamiltonian-oriented geometric integral by multiplying the counterclockwise angular
integral by `-chebyshevCellJacobianOrientation i j`; this is the sign forced by the vector identity
and positive time-factor theorem already recorded in D023. Hence the first energy displacement
`-∮ P dy` equals the cell orientation times the angular integral. The public theorem
`chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum` is the complete finite form of
Paper Eq. (3.8)--(3.12), and
`chebyshevFirstMelnikovDisplacement_finiteDensity_eq_cellIntegral` proves agreement with the
independent absolute-Jacobian change-of-variables route.

Rationale: endpoint square-root singularities never enter a derivative proof, no Jordan-domain
Green theorem is assumed, and both possible sources of sign—the Hamiltonian traversal and the
absolute inverse Jacobian—remain separately proved before their final comparison.

## D025 — Represent the common period annulus by explicit energy-orbit ranges

For the geometric content of Paper Section 3, define the cell period annulus as the union

```text
⋃ (0 < h < 1/4), range (chebyshevCellOrbit n i j lambda h).
```

The ceiling `1/4` is deliberately stricter than the paper's `1/2`: it is uniform in every legal
cell and every `lambda ≥ 1`, and it agrees with the analytic-kernel convergence range already used
by W4. `ChebyshevPeriodAnnulus.lean` proves exact inverse-branch interval membership, containment
in the open physical cell rectangle, nonvanishing orbit velocity, disjointness of distinct energy
levels, and disjointness of distinct cells. It also packages closed energy bands over one angular
period as compact subannuli and proves their energy and cell separation properties.

This is intentionally a geometric period-annulus interface over `ℝ × ℝ`. It does not identify the
angular parameter itself with Hamiltonian time: `ChebyshevOrbit.lean` proves the exact nonzero
scalar relation to the Hamiltonian vector field and its sign, while construction of the actual
local flow, transverse section, return time, and Poincaré map remains the W9 responsibility.

Rationale: W3 can now supply uniform compact, pairwise separated neighborhoods to W9 without
smuggling an unproved flow or Poincaré–Pontryagin theorem into the geometry layer.

## D026 — Separate normalized-displacement persistence from return-map construction

The public W0 layer now implements D002--D004 directly: `phaseSpaceProdEquiv` is the canonical
continuous linear coordinate bridge; `PolyVectorField` is exactly `Fin 2 → MvPolynomial (Fin 2) ℝ`
with separate analytic evaluation and maximum coordinate total degree; and `PeriodicOrbit` stores
only a carrier plus a proposition-valued nonconstant periodic-integral-curve certificate.
`PeriodicOrbit.ext` and `LimitCycle.ext` prove that carrier equality determines object equality.

For W9, factor the return displacement as

```text
Delta(mu,h) = mu * D(mu,h)
P(mu,h) = h + mu * D(mu,h).
```

`SimpleRoot.lean` applies Mathlib's implicit-function theorem to `D`, retaining both a `C¹` root
branch and the local iff that proves uniqueness. It also proves that a nonzero energy derivative
remains nonzero along that branch. `NormalizedDisplacement.lean` then proves that every sufficiently
small nonzero `mu` gives a fixed point of `P` with derivative `1 + mu*d_mu != 1`.

Rationale: the simple-root and multiplier argument is now fully discharged without presupposing a
project Poincaré–Pontryagin theorem. The remaining B3 obligation is cleanly isolated: construct the
actual return map from the ODE and prove that its displacement has the stated normalized `C¹`
extension with `D(0,h)` equal to the compiled Melnikov function.

## D027 — Make the return-time and unperturbed-conservation layer conditional only on a genuine flow

`C1LocalFlow` is not an existence axiom: it is a data structure containing an actual flow function,
an open time domain containing every zero time, interval-connected time fibers, `C¹` regularity,
the initial equation, and the ODE derivative equation. `ChebyshevReturnSetup` additionally records
one positive unperturbed return period and the equality of the parameter-zero vector field with the
transported Chebyshev Hamiltonian vector field.

From exactly this data, `ChebyshevReturn.lean` derives the physical transverse derivative, constructs
the locally unique return-time branch by Mathlib's implicit-function theorem, and defines a `C¹`
Hamiltonian-energy displacement. `EnergyConservation.lean` proves directly that the numerator `2H`
has zero derivative along the Hamiltonian flow, integrates this derivative over the full return
segment, and obtains `eventually_energyDisplacement_zero_unperturbed`: `Delta(0,h)=0` for every
nearby energy. Openness, return-time continuity, and interval-connected time fibers discharge the
whole-segment domain condition.

Rationale: zero-order Poincaré displacement is now a proved consequence of the ODE, not a field of a
return-map interface. The remaining W9 foundation is sharply exposed: construct this genuine flow
with enough parameter regularity, form the `C¹` quotient by `mu`, and identify its zero-parameter
trace with the exact W4 Melnikov integral.

## D028 — Audit the final degree on actual multivariate polynomials

`Degree.lean` embeds every univariate Chebyshev polynomial into a selected `Fin 2` coordinate of
`MvPolynomial (Fin 2) ℝ`. The global density is a finite sum of actual products
`T_a(x)T_b(y)`, not a function carrying a separate degree certificate. The perturbation polynomial
is definitionally `q=T_n'(x)T_n'(y)S`.

Because Mathlib has no multivariate polynomial antiderivative constructor, the file defines
`MvPolynomial.integrateAt` coefficientwise, proves
`pderiv i (integrateAt i p)=p`, and proves that total degree rises by at most one. The final field is
then represented in the public `PolyVectorField` type, and `finalVectorField_degree_le` proves the
paper's exact `4n-5` bound from the single concrete hypothesis `totalDegree S <= 2n-4`.

Rationale: the degree proof now checks the same polynomial objects that will be passed to the ODE,
and does not infer degree from pointwise function formulas. Only the finite support/frequency theorem
for the eventual W2/W5 hierarchical density remains before Eq. (6.8) can be marked fully instantiated.

## D029 — Parametrize the three-adic layers by their primitive residues

Use zero-based layer index `k<r`.  Instead of first filtering all naturals by divisibility and then
proving a difficult filter-cardinality theorem, represent the paper's `Y_(k+1)` rows by

```text
(b,q) in Fin 2 × Fin (3^(r-k-1)),
u = 6q + 4b + 1,
i = (3^k u)/2,
```

and represent `W_(k+1)` by `t in Fin (3^k)` with primitive numerator
`m=3t+1+(t mod 2)` and actual frequency `m*3^(r-k-1)`.  The maps to natural row and
frequency indices are proved injective.  Their image `Finset`s therefore have the paper's exact
cardinalities.  Each row image has valuation exactly `k`, each frequency numerator is positive,
odd, below `3^(k+1)`, and not divisible by `3`; different layers are disjoint.

The same integer identities are used for the analytic statement.  Earlier bands give an odd
multiple of `pi/2`, hence zero cosine.  On the diagonal the phase is `m*u*pi/6`.  Exhaustion of the
four unit residues `1,5,7,11 mod 12` proves the real sign character is multiplicative and yields the
exact tensor row-sign/frequency-sign factorization, with a separately audited nonzero theorem.

Rationale: this representation makes the cardinalities computational rather than quotient-heavy,
while still proving the exact divisibility predicates and actual Chebyshev phases from the paper.
It also exposes a direct `Fin`-indexed interface for W2 and W10.

## D030 — Build the valuation basis from separating Taylor functionals

Represent an `m`-dimensional analytic germ family by `m` linearly independent convergent
`FormalMultilinearSeries`, without introducing a quotient type of germs. On the coefficient space
`Fin m → ℝ`, the `k`th Taylor coefficient is a linear functional. These functionals separate
points by linear independence of the series. Choose the least nonzero functional, split off one
vector transverse to its kernel, and recurse on that kernel. `finrank_ker_add_one_of_ne_zero` and
`Basis.mkFinCons` certify the dimension drop and the extended basis. This produces strictly
increasing leading indices with all earlier coefficients exactly zero.

For each transformed analytic function, Mathlib's iterated `dslope` factorization gives the global
identity `f_j(h)=h^(q_j) g_j(h)` and `g_j(0)≠0`. The normalized equation is therefore defined without
division by `τ`; it is jointly `C¹` at `(τ,t)=(0,ρ_s)` and equals the sparse limiting polynomial
when `τ=0`. Descartes' multiplicity bound forces all prescribed positive roots to be simple, and
the scalar implicit-function theorem gives the root branches and the exact little-`o` location.

Rationale: this follows the paper's Taylor Gaussian elimination while staying entirely inside
finite-dimensional linear algebra and convergent series. It avoids assuming that the first `m`
consecutive Taylor rows are independent and avoids a separate general ECT/Wronskian library.

## D031 — Normalize each finite-poset layer without division

Represent the hierarchy by an arbitrary finite partially ordered type `A`, a finite cell type `C`,
a layer map `C → A`, and strictly order-increasing natural weights. For a cell in layer `alpha`,
define its normalized response by retaining only visible blocks `beta` with `alpha ≤ beta` and
using the nonnegative exponent `weight beta - weight alpha`. This gives an exact diagonal value at
`zeta=0`; no quotient by a parameter-dependent function and no removable-singularity axiom is
needed.

Apply the scalar implicit-function theorem to every cell/root pair at that diagonal value. Since
both index types are finite, intersect their eventual neighborhoods to obtain one common positive
`zeta` threshold. The identity
`zeta^(weight alpha) * normalized = weighted` then transfers zerohood and the nonzero energy
derivative to the actual single weighted response whenever `zeta>0`.

Finally, call `rankToSimplePositiveRoots` once per finite layer, choose a sufficiently small
positive concentration parameter in each result, and insert the resulting fixed coefficient
vectors into the hierarchy. Thus `hierarchicalRealization` concludes directly about coefficients
of the original analytic basis responses rather than an abstract diagonal-root hypothesis.

Rationale: the theorem is general enough to instantiate the paper's `Fin`-indexed three-adic
layers, while its finite intersection makes the common threshold explicit in the theorem's
quantifier order. The normalized object remains an internal proof device; the public conclusion is
about the unnormalized perturbation density.

## D032 — Count a dependent finite type, not an integer expression

Define `ThreeAdicCycleIndex r` as the dependent sum of two layer indices `k,l : Fin r`, one actual
`ThreeAdicRow r k` and `ThreeAdicRow r l`, and a final
`Fin (card(ThreeAdicFrequency k) * card(ThreeAdicFrequency l) - 1)` root index. This is the exact
finite object whose elements will label the constructed limit cycles.

First compute its `Fintype.card` as the finite double sum using dependent-sum and product
cardinalities. Then cast the sum to `ℤ`, invoke the already audited division-free tensor identity,
and cast back only after proving
`(3^r-1)^2 ≤ (2*3^(r-1)*r)^2`. The final Eq. (6.7) therefore lives in `ℕ`; no negative count
or silently truncated subtraction can enter the main theorem.

Rationale: a later injective map from this type into limit cycles states the exact cardinal lower
bound definitionally, while retaining all layer/row/root coordinates needed for distinctness.

## D033 — State the all-degree passage for an abstract monotone lower-bound function

The asymptotic argument does not need the internal representation of the final vector fields.
Accordingly, `subsequenceToAllDegrees` accepts any `H : ℕ → ℝ`, a monotonicity proof, and the
exact subsequence estimate at `subsequenceDegree r = 4*3^r-5`. This keeps W11 independent of the
remaining dynamical construction while preserving exactly the implication used by the paper.

For arbitrary `N ≥ 31`, choose
`allDegreeIndex N = Nat.log 3 ((N+5)/4)`. Natural division with remainder proves the consecutive
degree bracket. Its upper half gives `(N+5)/12 < 3^r`; strict monotonicity of `Real.log` and
`Real.log_pow` give the matching logarithmic inequality. For the conventional Omega statement,
take `N₀=144` and the explicit positive constant
`1 / (5184 * (log 3)^2)`; monotonicity of log proves the shifted logarithm is at least half of
`log N`.

Rationale: both the stronger displayed Eq. (6.12) and the quantified
`c*N²*(log N)²` conclusion are audited. The final main theorem only has to instantiate `H` and
its subsequence premise.

## D034 — Index the global density by dependent three-adic modes

Define `ThreeAdicMode r` as the dependent sum of two layer indices and one genuine frequency
parameter from each corresponding band. The global polynomial density is the finite sum over this
type, rather than a loose `Finset (ℕ×ℕ)` plus an external membership certificate. The hierarchical
version multiplies each coefficient by the paper's one-based weight
`zeta^((k+1)+(l+1))`.

Prove every actual frequency is odd. Since it is also strictly less than the odd number `3^r`, it
is at most `3^r-2`; hence every tensor mode has total frequency at most `2*3^r-4`. The generic
polynomial degree chain can then be instantiated directly with the actual hierarchical density,
yielding `threeAdicHierarchicalFinalVectorField_degree_le`.

Rationale: arbitrary block coefficients include exactly those later selected by W2, so degree does
not depend on their values or on `zeta`. This closes W8 without a separate support hypothesis at
the main-theorem boundary.

## D035 — Define the normalized displacement by energy production, not division

For the paper's perturbation `(H_y+mu*P,-H_x)`, define the normalized return displacement as the
time integral of `H_x P` along the actual perturbed return trajectory. A direct polynomial chain
rule proves `dH/dt = mu H_x P`. The interval FTC therefore yields the exact identity
`Delta(mu,h)=mu*D(mu,h)` without defining `D=Delta/mu`, choosing an arbitrary value at `mu=0`, or
proving a removable singularity.

At `mu=0`, the same definition is definitionally a time integral along the genuine unperturbed
flow. Since its physical second velocity is `-H_x`, Lean proves this is exactly `-∫P dy` on that
time-parametrized return segment. The remaining comparison with W4 is now purely geometric: prove
that the chosen positive return traverses the explicit Chebyshev oval once in Hamiltonian
orientation. Smooth dependence and the `C¹` regularity of this integral remain separate ODE and
parametric-integration obligations.

Rationale: this formulation fixes the sign at the differential-equation level and strictly
separates three issues that should not be conflated: energy algebra, smooth dependence of the
actual flow, and one-turn orbit reparametrization.

## D036 — Identify the degree-audited field with the ODE field by evaluation

Evaluate every `MvPolynomial (Fin 2) ℝ` in the physical product coordinates and prove that the
public `PolyVectorField.eval` commutes with `phaseSpaceProdEquiv`.  With this bridge,
`finalPolyVectorField_eval_eq_perturbedPhaseVector` shows that W8's field and W9's field are the
same function, not merely two objects with matching displayed formulas.  A coefficient induction
also proves that multivariate polynomial evaluation is `ContDiff` to every finite order.

Consequently the actual parameterized perturbation is jointly `C¹`, and Mathlib's Picard theorem
gives a parameter-lifted local integral curve through every `(mu,x)`.  This deliberately stops
short of claiming a common-time flow: pointwise local existence and smooth dependence of a flow
map are different theorems.

Rationale: degree, dynamics, and later limit-cycle statements must refer to one evaluated vector
field.  The explicit equality prevents an untracked conversion assumption at the main theorem.

## D037 — Make Hamiltonian orientation a positive-clock theorem

Choose the affine angular clock determined by `chebyshevCellJacobianOrientation`.  The reoriented
explicit oval has derivative `-orientation` times the original angular velocity.  Combining this
with the previously proved velocity identity gives
`positiveFactor • angularVelocity = HamiltonianVector`, where positivity is proved pointwise.

The general affine change-of-variables theorem for `parameterizedPdy` then proves that the new
one-turn trace is exactly `chebyshevHamiltonianOrientedPdy`, including both checkerboard signs.
Thus W4's orientation convention is realized by an actual differentiable curve with a
positive Hamiltonian clock.  The integration and inversion of this clock are recorded separately
in D038; W9 still has to align the resulting closed solution with its section-based first return.

Rationale: a bare sign multiplier on a line integral is insufficient for the ODE argument.  The
positive-factor theorem records precisely the geometric datum required for the remaining
Hamiltonian-time reparametrization.

## D038 — Integrate the positive clock before comparing return trajectories

Define physical elapsed time as the interval integral of the reciprocal positive angular factor.
Continuity and strict positivity make this clock strictly increasing, with positive one-turn
period.  Its restriction to `[0,2*pi]` is therefore an order isomorphism onto `[0,T]`; extend the
inverse constantly outside this interval only so that it is a total Lean function.

On `(0,T)`, the inverse-function derivative theorem gives `d angle/dt = timeFactor(angle t)`.
Composing the angular oval with this inverse proves, coordinatewise, that the resulting physical
curve satisfies the genuine Hamiltonian ODE.  Monotone interval substitution then proves
`chebyshevHamiltonianTimePdy_eq_angularPdy` for every continuous `P`, and hence
`chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianTimePdy`.

Rationale: the W4 integral is now attached to an actual one-period Hamiltonian-time solution, not
only to a positively oriented geometric trace.  This removes clock integration/inversion from the
W9 backlog.  Section-phase alignment is handled in D039 and ODE uniqueness in D040;
common-time smooth-flow and parametric `C¹` work remain.

## D039 — Shift the clock origin to the section and select the local positive-period branch

Define a shifted elapsed-time clock whose angular offset `0` is the already chosen horizontal
Poincare-section base point.  Its one-turn value is strictly positive, its inverse has the expected
derivative, and the resulting physical-time solution starts at the base point and returns to the
same base point after that positive period.  Transport the endpoint equalities and both coordinate
Hamilton equations to the public `PhaseSpace` in `ChebyshevExplicitReturn.lean`.

Do not require this period to be the first intersection with the entire global horizontal line.
The same oval generally meets that line at the opposite point after half a turn.  The return-time
IFT is local near the chosen base point and near the full positive period, so its locally unique
time branch selects the desired return.  The remaining identification obligation is ordinary ODE
uniqueness between the explicit zero-parameter solution and a common-time local flow, not a global
minimal-section-hit theorem.  That uniqueness is now compiled in D040; construction of the flow
itself remains.

Rationale: this is the exact geometric datum used by `ChebyshevReturnSetup`: a positive time at
which the local flow returns to the selected base.  Asking for global first-hit minimality would be
stronger than the interface, false for the unlocalized horizontal section, and irrelevant to the
local Poincare map.

## D040 — Identify the zero-parameter flow by compact-ball ODE uniqueness

Pad the inverse section clock by one angular unit at both ends.  This leaves every `[0,T]`
formula unchanged but makes physical times `0` and `T` interior points of the inverse-clock domain,
so the explicit curve has a genuine two-sided derivative at the initial time.

For any supplied `C1LocalFlow` whose zero-parameter domain contains `[0,T]`, transport its curve to
product coordinates.  The flow curve and explicit curve are continuous on the compact interval,
so their image union lies in one closed ball.  The polynomial Hamiltonian vector field is `C¹` and
therefore Lipschitz on that convex compact ball.  Mathlib's interval ODE uniqueness theorem then
identifies the curves on all of `[0,T]`.

Expose both the pointwise trajectory equality and its endpoint return consequence.  Define
`chebyshevReturnSetupOfSectionPeriod` so ODE uniqueness, rather than caller-supplied equality,
fills `ChebyshevReturnSetup.returns_to_base`.  Periodicity of the angular integrand also proves that
the section-start physical trace equals W4's angular trace; hence the constructed setup's
zero-parameter Melnikov factor is exactly the negative W4 coefficient.

Rationale: the remaining common-flow constructor only has to provide smoothness and a domain
covering finitely many compact period segments.  It no longer carries any separate orbit,
return-equality, phase-alignment, or Melnikov-identification obligation.

## D041 — Prove C¹ Melnikov regularity on a local compact parameter tube

Do not strengthen `C1LocalFlow.flow` to a globally `C¹` map.  Instead, prove generic fixed- and
variable-endpoint parameter-integral theorems that require `C¹` only on an open neighborhood of
the compact base fiber.  For fixed endpoints, use the partial Fréchet derivative in the parameter,
compactness of a closed parameter ball times the unordered time interval, and a uniform derivative
bound to invoke differentiation under the integral.  For a variable endpoint, rescale the interval
to `[0,1]`; this handles positive and negative endpoints with the same formula.

Apply the local theorem to the energy-section pullback of the genuine flow and its return time.
For every `C¹` observable `Q`, this proves `ChebyshevReturnSetup.contDiffAt_melnikovIntegral`; the
actual observable `Q = H_x P` is `C¹` whenever `P` is, so
`ChebyshevReturnSetup.contDiffAt_actualMelnikov` closes the joint-regularity obligation for the
actual factor `D(mu,h)`.

Use compactness of the scaled return segment `r ∈ [0,1]` to construct one open parameter-energy
neighborhood on which the energy remains admissible, the return time is positive, and the entire
variable segment remains in the flow domain.  On that neighborhood, prove both the exact actual
factorization and equality of the actual energy return map with the normalized map.  The existing
simple-root continuation theorem then transfers to the actual return map, yielding a fixed point
and multiplier `rho ≠ 1` for every sufficiently small nonzero parameter.

Rationale: joint `C¹` regularity of `D` and actual-return-map persistence are now independent of
the common-flow construction.  The flow constructor is responsible only for a jointly smooth
common-time flow/domain covering the finite period segments; isolated-limit-cycle and finite-family
assembly remain separate geometric obligations.

## D042 — Build the zero-time C¹ flow by a scale-zero Picard IFT and glue its germs

Normalize every candidate trajectory to `[-1,1]` and put the physical time scale `tau` into the
Picard residual
`R((tau,z),gamma) = gamma - const(z) - tau * Volterra(V ∘ gamma)`.  At `tau=0` and the constant
curve, the partial derivative in `gamma` is exactly the identity.  The Banach-space implicit
function theorem therefore gives a `C¹` curve germ without a separate Neumann-series estimate.
Prove the actual Chebyshev polynomial Nemytskii operator is `C¹` by polynomial induction.

Convert zero residual into the physical ODE by interval FTC and time rescaling.  Compact-ball
Lipschitz uniqueness proves that overlapping Picard germs have identical endpoints.  Shrink each
germ to an open ball on which both the residual equation and pointwise `C¹` regularity hold, take
the union of these time-zero-centered balls, and glue endpoints by classical choice plus overlap
uniqueness.  The centered-ball geometry gives interval-connected time fibers.  A slightly larger
time scale inside each ball proves the glued endpoint's time derivative is the lifted vector
field; the zero first component proves that the parameter coordinate remains frozen.

Package the planar second coordinate as `chebyshevPolynomialC1LocalFlow`.  Its open domain,
zero-time membership, interval fibers, joint `C¹` regularity, initial value, and ODE law are all
compiled and axiom-audited.  This constructor is intentionally only the common zero-time local
flow.  The next layer must finitely continue it along the compact target period segments before it
can instantiate `chebyshevReturnSetupOfSectionPeriod`.

Rationale: scale zero makes the curve derivative literally invertible and avoids importing an
unproved smooth-dependence theorem.  Separating local germ construction from finite trajectory
continuation keeps the remaining W9 obligation explicit and geometric.

## D043 — Continue the local flow by finite open Picard strips

Use compactness of the explicit zero-parameter section orbit to obtain one uniform local Picard
time radius.  Subdivide its positive period into finitely many equal positive steps smaller than
that radius.  ODE uniqueness identifies each fixed-step Picard iterate with the corresponding
explicit orbit mesh point, so every step is admissible through the full period.

For joint smoothness, center the `k`-th continuation chart at time `k*delta` and restrict it to the
open strip of time radius `delta`.  Only equal or consecutive strip indices can overlap.
Consecutive charts have the same value at their intervening mesh point, and compact-interval ODE
uniqueness propagates this equality throughout either side of the overlap.  Therefore a classical
choice of a containing chart is value-independent.  Local equality with one open chart proves the
chosen union map is jointly `C¹`.

The open finite union is star-shaped in every time fiber about zero: admissibility fills all
completed mesh intervals, and the current chart fills the partial final interval.  Thus it has the
interval property required by `C1LocalFlow`.  Projecting the glued lifted flow to phase space gives
`chebyshevPolynomialFiniteC1LocalFlow`, with initial value, frozen parameter, physical ODE law, and
full prescribed-period coverage all compiled.

Rationale: finite strips avoid any global completeness claim and make overlap combinatorics
strictly adjacent.  The construction supplies exactly the compact time coverage required by the
return-time IFT while preserving the existing local-flow interface.

## D044 — Select hierarchy roots inside the certified analytic radius

Do not assert global `C¹` regularity for `analyticKernel`.  Its compiled Taylor majorant certifies
the concrete interval `0 < h < 1/4`, which is exactly the energy range used by the cell-integral
formula.  Strengthen rank-to-roots so the fixed diagonal roots can be selected below any prescribed
positive radius `R`, and formulate a local hierarchy theorem requiring only `ContDiffOn` on
`(0,R)`.  Continuity of the implicit root branches then keeps all perturbed roots below `R` for one
common sufficiently small positive hierarchy parameter.

Instantiate this local theorem with `R=1/4`, the genuine dependent three-adic row/frequency types,
the product partial order, the one-based tensor weight, the lower-band invisibility theorem, and
the mod-twelve diagonal factorization.  Use the coefficient-series form of the common anisotropic
rank theorem, reindex it by the actual block equivalence, and preserve the nonzero frequency signs
by unit scaling.

Rationale: this is the strongest statement justified by the convergence proof and it feeds W4
without an unproved global analyticity assumption.  The resulting concrete theorem supplies one
common anisotropy threshold and simultaneous simple roots satisfying `0 < h < 1/4` on every marked
cell.

## D045 — Identify Melnikov germs, not only marked values

Equality of the compiled W4 coefficient and the genuine return factor at one marked energy is not
enough to transfer a nonzero energy derivative.  Prove instead that the physical angular-time
density is jointly `C¹` in energy and angle and hence that the explicit section period is `C¹` in
energy.  Compactness of the scaled nearby period segments gives a common tube inside the finite
flow domain.  ODE uniqueness identifies the flow with the explicit Hamiltonian orbit throughout
that tube, and the local uniqueness clause of the return-time implicit function theorem identifies
the selected return time with the explicit period.

The public result
`C1LocalFlow.eventually_chebyshevReturnSetupOfSectionPeriod_melnikov_eq_first` is therefore an
eventual equality in energy.  Values and derivatives of the genuine zero-parameter Melnikov factor
can both be rewritten to the compiled W4 displacement without an unjustified pointwise derivative
congruence.

Rationale: the persistence theorem needs a simple zero of the actual return factor, which is a germ
statement.  This closes exactly that logical gap and does not impose global flow completeness.

## D046 — Select the common perturbation parameter on the exact finite cycle-index type

Package each marked root as a `ChebyshevPolynomialReturnCertificate`.  The certificate stores the
actual finite `C1LocalFlow`, return setup, polynomial-field identities, genuine Melnikov value and
derivative, local zero continuation, and the eventual fixed-point/multiplier conclusion.  Instantiate
these certificates directly over `ThreeAdicCycleIndex r`, so the family being intersected is exactly
the finite type whose cardinality is used by W10.

Apply a finite `Filter.Eventually` intersection to all certificate neighborhoods and then choose one
strictly positive parameter in the resulting punctured neighborhood.  The theorem
`threeAdicPolynomialCommonReturnParameter` returns one hierarchy parameter, the full certificate
family, and one common positive `mu` at which every actual return map has a fixed point with
multiplier different from `1`.

Rationale: this fixes the quantifier order required by Paper Lemma 6.3.  The remaining finite-family
work is geometric—global periodic parametrization, isolation, and carrier injection—not another
parameter-uniformity argument.

## D047 — Globalize a closed return segment by floor/fract periodic extension

Package a return-map fixed point as a global periodic integral curve by rescaling its closed
positive-time segment to `[0,1]`, composing with `Int.fract`, and scaling back by the return time.
Endpoint equality glues continuity and the equal autonomous velocity at the seam glues the
derivative.  The carrier is the range of this explicit `periodicExtension`, so no quotient by time
translation or global completeness assumption is introduced.

Rationale: the finite local flow only needs to cover one return segment.  Periodic repetition is a
mathematical consequence of endpoint closure and autonomy, not a request for a globally defined
flow map.

## D048 — Preserve root-slot injectivity through every hierarchy layer

Simple roots alone do not show that two named slots denote different roots.  Prove injectivity of
the continued scaled-root family near the singular parameter and carry it through
`SimpleRootCombination`, the bounded local hierarchy, the concrete three-adic realization, the
actual polynomial Melnikov bridge, and the return/periodic-orbit certificates.

Rationale: the exact cycle-index cardinality counts marked root slots.  Carrier injection is valid
only after the implementation proves that distinct slots remain distinct at the selected common
hierarchy parameter.

## D049 — Separate carrier uniqueness from return-section isolation

For a `C¹` autonomous field, compact-ball Lipschitz uniqueness implies that two global integral
curves agreeing at time zero agree everywhere.  Consequently periodic carriers that share a point
are equal.  Separately, a scalar return fixed point with derivative different from `1` is locally
the unique fixed point.  Package the final implication as
`PeriodicOrbit.isIsolated_of_returnSection`: if every periodic carrier in an open return tube meets
the local section at an energy in that fixed-point neighborhood, then the selected carrier is
isolated.

Rationale: this exposes the only remaining geometric obligation.  Multiplier nondegeneracy handles
the scalar fixed point; it does not by itself prove that an arbitrary nearby periodic carrier meets
the chosen local section.

## D050 — Transfer finite carrier separation through compact normalized return tubes

Store the canonical unperturbed period and the certified energy ceiling in each return certificate.
Normalize every varying return segment to `[0,1]`.  Joint `C¹` continuity along the compact base
fiber and the generalized tube lemma show that any open neighborhood of the unperturbed oval
contains the whole actual periodic carrier for all sufficiently small parameters.  For the finite
exact index family, normality supplies pairwise-disjoint open supersets of the pairwise-disjoint
compact unperturbed ovals.  Intersect the corresponding eventual parameter predicates and select
one common positive parameter.

Rationale: pairwise separation at `mu=0` is not automatically a statement about perturbed global
carriers.  The compact normalized-return argument supplies precisely the uniform containment needed
to preserve separation without assuming global flow completeness.

## D051 — Close return-tube isolation by angular cutting and monotone iteration

Use the forward Chebyshev coordinates
`u=T_n(x)` and `v=-sigma*sqrt(lambda)*T_n(y)`.  On a compact tube around one
unperturbed oval, their squared radius and oriented angular cross product remain strictly positive
for every sufficiently small perturbation.  A single-valued stereographic angle on the complement
of the positive ray has derivative of one strict sign; periodicity therefore forces every periodic
carrier in the tube to meet that ray.  A local inverse-function argument identifies such a hit with
the energy-parametrized Poincare section.

Do not assume that the selected local return branch closes an arbitrary nearby periodic carrier in
one step.  Instead, use ODE uniqueness to keep every successive local return on the same carrier.
The localized ray tube keeps all returned energies in one compact interval.  Joint `C¹` regularity
of the normalized displacement makes the return map order-preserving there.  Its iterates converge
to a fixed point, uniform simple-root uniqueness identifies the limit with the continued marked
root, and closedness plus ODE carrier uniqueness identifies the whole periodic carrier.

Rationale: this proves the required isolation without an unjustified "first return equals one local
branch" assumption and without invoking winding-number or global-flow machinery.

## D052 — State the final asymptotic theorem as direct field existence

Define `DegreeNAdmitsAtLeast N L` by existence of a real planar polynomial vector field of degree at
most `N` together with an injective `Fin L` family of actual `LimitCycle`s.  Reindex the exact
dependent `ThreeAdicCycleIndex r` family by its proved cardinality and use pairwise carrier
disjointness for injectivity.  The public subsequence theorem instantiates this at
`N=4*3^r-5` and `L=cycleLowerBound r`.

For arbitrary `N≥144`, select `r=allDegreeIndex N`, use the compiled degree bracket, and return the
subsequence field itself as a degree-`≤N` witness.  Combine the exact count with the existing real-log
inequalities to obtain the explicit positive multiple of `N²(log N)²`.

Rationale: the final theorem no longer assumes a monotone or finite-valued Hilbert-number function;
it directly returns the polynomial field and finite injective limit-cycle family required by the
paper's existential lower bound.
