# B1 negative-axis connection audit

Last updated: 2026-08-28

## Scope and current verdict

Paper Eq. (5.5)--(5.8) and Lemma 5.1 are now Lean theorems. The connection formula holds for
`0 < alpha < 1` and `x > 1`; the final linear-independence theorem covers arbitrary finite strictly
ordered parameter families and arbitrary finite shift ranges.
The public proof is `negativeAxisConnectionFormula` in
`Hilbert16/Spikes/BorelGaussConnection.lean`; it proves the proposition contract
`NegativeAxisConnectionFormula alpha`.

Locked Mathlib still defines ordinary `₂F₁` only as a power-series sum with a junk value outside
its radius, so `gaussBorelImage alpha (-x)` is deliberately not used for `x>1`. The left-hand side
is the valid Euler/Beta continuation `gaussEulerContinuation alpha (-x)`. The separate theorem
`gaussEulerContinuation_eq_borelImage` proves that this continuation agrees with the original
Borel hypergeometric series on `|s|<1`.

## Parameter substitution in DLMF 15.8.2

Use

```text
a = -alpha / 2
b =  alpha / 2
c = 1
z = -x,  x > 1.
```

Then

```text
b - a       = alpha
a - c + 1   = -alpha / 2
a - b + 1   = 1 - alpha
b - c + 1   =  alpha / 2
b - a + 1   = 1 + alpha
1 / z       = -1 / x.
```

Thus the two ordinary Gauss factors are exactly

```text
PhiPlus  = ₂F₁(-alpha/2, -alpha/2; 1-alpha; -1/x)
PhiMinus = ₂F₁( alpha/2,  alpha/2; 1+alpha; -1/x).
```

DLMF 15.8.2 uses Olver's regularized function `bold F`. Converting the two functions on the
right to ordinary `₂F₁` produces the raw coefficients

```text
CPlus  = (pi / sin(pi*alpha)) /
         (Gamma(alpha/2) Gamma(1+alpha/2) Gamma(1-alpha))

CMinus = -(pi / sin(pi*alpha)) /
         (Gamma(-alpha/2) Gamma(1-alpha/2) Gamma(1+alpha)).
```

Euler reflection at `alpha` and `-alpha` gives

```text
CPlus  = Gamma(alpha) /
         (Gamma(alpha/2) Gamma(1+alpha/2)) = A_alpha

CMinus = Gamma(-alpha) /
         (Gamma(-alpha/2) Gamma(1-alpha/2)) = B_alpha.
```

These two reductions are the compiled theorems `dlmfConnectionA_eq` and
`dlmfConnectionB_eq`.

## Branch and convergence audit

- Since DLMF's `z=-x`, one has `-z=x>0`. The principal complex powers in 15.8.2 therefore reduce
  to the positive real powers used by `negativeAxisConnectionRHS`; no phase factor is introduced.
- `0 < alpha < 1` makes the exponent difference `alpha` nonintegral, so this specialization is
  nonresonant.
- If `x>1`, then `|-x⁻¹|<1`. Lean proves this as `negativeAxis_inverse_mem_unitDisk`.
- Lean proves that the two transformed ordinary hypergeometric series both have radius exactly
  one (`gaussPhiPlus_radius_eq_one`, `gaussPhiMinus_radius_eq_one`) and supplies explicit
  `HasSum` certificates at `-x⁻¹` (`gaussPhiPlus_hasSum`, `gaussPhiMinus_hasSum`).
- `gaussConnectionA_pos` and `gaussConnectionB_pos` prove that both coefficients are strictly
  positive, hence finite and nonzero in Lean's real-valued Gamma model.
- The continuation is implemented as an expectation under Mathlib's Beta probability measure.
  Lean proves that this measure is concentrated on `0<t<1`, that the real-power base is positive
  almost everywhere for every `s<1`, and that the integrand is genuinely integrable there.

## Lean declarations and proof boundary

| Obligation | Declaration | State |
|---|---|---|
| Paper coefficients | `gaussConnectionA`, `gaussConnectionB` | defined |
| DLMF normalization to paper coefficients | `dlmfConnectionA_eq`, `dlmfConnectionB_eq` | proved |
| Coefficient nondegeneracy | `gaussConnectionA_pos`, `gaussConnectionB_pos` | proved |
| Two transformed factors | `gaussPhiPlus`, `gaussPhiMinus` | defined |
| Value at zero | `gaussPhiPlus_zero`, `gaussPhiMinus_zero` | proved |
| Radius and convergence at `-1/x` | four `radius_eq_one` / `hasSum` theorems | proved |
| Valid continuation object on the negative axis | `gaussEulerContinuation` | defined |
| Normalization at the Borel base point | `gaussEulerContinuation_zero` | proved |
| Support, branch safety, and integrability on `s<1` | `betaMeasure_ae_mem_Ioo`, `gaussEulerIntegrand_pos_ae`, `gaussEulerIntegrand_integrable` | proved |
| Positivity of the continuation on `s<1` | `gaussEulerContinuation_pos` | proved |
| Exact Euler-continuation connection identity | `negativeAxisConnectionFormula` | proved |
| Agreement with the original Borel germ on `|s|<1` | `gaussEulerContinuation_eq_borelImage` | proved |
| Growing and decaying infinity coefficients | `gaussEulerContinuation_leading_tendsto`, `gaussEulerContinuation_decay_operator_tendsto` | proved |
| Specialized Gauss ODE and both Frobenius branches | `ordinaryHypergeometric_ode`, `gaussInfinityBranch_ode`, `gaussEulerNegative_ode` | proved |
| Wronskian uniqueness and zero remainder | `scaledWronskian_hasDerivAt_zero`, `gaussConnectionRemainder_eq_zero` | proved |
| Local Taylor expansion of the continuation at every `x>0` | `gaussEulerNegative_hasFPowerSeriesAt` | proved |
| Real analyticity on the positive negative-axis coordinate | `gaussEulerNegative_analyticOnNhd` | proved |
| Formal relation to a fixed-order Borel derivative relation | `formalShift_relation_borelDerivativeCoefficients`, `formalShift_relation_gaussBorelDerivatives` | proved |
| Identity-theorem continuation of the differentiated relation | `formalShift_relation_gaussNegativeDerivatives` | proved |
| Arbitrary differentiated leading asymptotic | `gaussNegativeDerivative_tendsto` | proved |
| Nonzero differentiated leading coefficient | `gaussNegativeDerivativeLeading_ne_zero` | proved |
| Pairwise distinct shift/parameter exponents | `borelGaussShiftExponent_injective` | proved |
| Paper Lemma 5.1 | `formalTwoFZeroShift_linearIndependent`, `borelGaussShiftIndependent` | proved |

## Chosen completion route

The specialized Euler integral from DLMF 15.6.1 is the canonical continuation object. In Lean it
is represented as the following Beta expectation:

```text
E_{t ~ Beta(alpha/2, 1-alpha/2)} [(1-s*t)^(alpha/2)].
```

Unfolding Mathlib's Beta density gives exactly

```text
1 / (Gamma(alpha/2) Gamma(1-alpha/2)) *
integral (t=0..1)
  t^(alpha/2-1) (1-t)^(-alpha/2) (1-s*t)^(alpha/2) dt.
```

All obligations through Paper Lemma 5.1 are complete:

1. On `|s|<1`, dominated termwise integration of the binomial series, exact Beta moments, and
   coefficient normalization prove `gaussEulerContinuation_eq_borelImage`.
2. On the negative axis, two differentiations under the Beta integral plus an endpoint-safe
   integration-by-parts identity prove that the Euler continuation solves the specialized ODE.
   The two transformed Gauss series are independently proved to solve the same ODE. Direct Beta
   limits compute the growing coefficient `A` and the decaying coefficient `B`. Finally,
   `x` times the Wronskian is constant; its limits give zero Wronskians for the connection
   remainder and mutual branch Wronskian `-alpha`, forcing the remainder to vanish.
3. A local binomial/Beta expansion at every `x>0` proves real analyticity of the Euler continuation.
   Hence a formal shifted relation, after a uniform `e-1` Borel differentiation, first holds on the
   unit disk and then on the whole positive coordinate of the negative axis by the real-analytic
   identity theorem.
4. Dominated convergence computes every differentiated leading term. For `(q,i)` its exponent is
   `q + alpha i / 2 - (e-1)` and its coefficient is nonzero. The parameter strip makes these
   exponents pairwise distinct, so a maximal-exponent argument proves
   `borelGaussShiftIndependent`.

The B1 Go criterion is therefore passed. The next consumer is Proposition 5.2 / W7, which must
combine this theorem with the `beta^2` Vandermonde and the finite Taylor-minor argument.

## Non-proof regression check

As a transcription check only, 80-digit `mpmath` evaluations were run at
`alpha = 0.1, 1/3, 0.75, 0.99` and `x = 1.01, 2, 10, 1000`. The displayed formula agreed with
direct analytic-continuation evaluation to roughly `10^-80` relative precision. This check is not
part of the proof and was not used to discharge any Lean obligation.

## Primary references

- [DLMF 15.8.2, connection formula](https://dlmf.nist.gov/15.8.E2)
- [DLMF 15.2, regularized hypergeometric normalization](https://dlmf.nist.gov/15.2)
- [DLMF 15.6.1, Euler integral](https://dlmf.nist.gov/15.6.E1)
