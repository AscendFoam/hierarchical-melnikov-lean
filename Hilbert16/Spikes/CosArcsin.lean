import Hilbert16.Spikes.BorelGaussODE
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

set_option autoImplicit false

namespace Hilbert16.Spikes

open Nat Polynomial Filter Set
open scoped Topology

/-- The convergent Gauss function whose argument is `u²` in the cosine--arcsine identity. -/
noncomputable def cosArcsinGauss (alpha u : ℝ) : ℝ :=
  ordinaryHypergeometric (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2)

/-- Its Gauss-series coefficient, before substituting `u²`. -/
noncomputable def cosArcsinCoefficient (alpha : ℝ) (p : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient (-alpha / 2) (alpha / 2) (1 / 2) p

/-- Paper Eq. (3.10)'s cosine coefficient is `U_p(alpha)/(1/2)_p`. -/
theorem cosArcsinCoefficient_eq (alpha : ℝ) (p : ℕ) :
    cosArcsinCoefficient alpha p =
      formalTwoFZeroCoefficient alpha p / (ascPochhammer ℝ p).eval (1 / 2) := by
  have hhalf : (ascPochhammer ℝ p).eval (1 / 2 : ℝ) ≠ 0 :=
    (ascPochhammer_pos p (1 / 2 : ℝ) (by norm_num)).ne'
  simp only [cosArcsinCoefficient, ordinaryHypergeometricCoefficient,
    formalTwoFZeroCoefficient]
  field_simp [hhalf]

private theorem natCast_ne_between_zero_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (n : ℕ) : (n : ℝ) ≠ t := by
  intro hn
  have hnlt : n < 1 := by exact_mod_cast (hn.symm ▸ ht1)
  have hnzero : n = 0 := Nat.lt_one_iff.mp hnlt
  subst n
  norm_num at hn
  exact ht.ne' hn.symm

private theorem natCast_ne_neg_of_pos {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (n : ℝ) ≠ -t := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The cosine--arcsine Gauss series has exact radius one in the paper's parameter range. -/
theorem cosArcsinGauss_radius_eq_one {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) (1 / 2)).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro n
  have hpos : (n : ℝ) ≠ alpha / 2 :=
    natCast_ne_between_zero_one (by linarith) (by linarith) n
  have hneg : (n : ℝ) ≠ -(alpha / 2) :=
    natCast_ne_neg_of_pos (by linarith) n
  have hhalf : (n : ℝ) ≠ -(1 / 2 : ℝ) :=
    natCast_ne_neg_of_pos (by norm_num) n
  simpa only [neg_div, neg_neg] using ⟨hpos, hneg, hhalf⟩

/-- `arcsin` is real analytic at every interior point of its natural interval. -/
theorem analyticAt_arcsin_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    AnalyticAt ℝ Real.arcsin x := by
  have hx' : -1 < x ∧ x < 1 := abs_lt.mp hx
  let y := Real.arcsin x
  have hylo : -(Real.pi / 2) < y := Real.neg_pi_div_two_lt_arcsin.mpr hx'.1
  have hyhi : y < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hx'.2
  have heq : (Real.arcsin ∘ Real.sin) =ᶠ[𝓝 y] id := by
    filter_upwards [Ioo_mem_nhds hylo hyhi] with z hz
    simpa only [Function.comp_apply, id_eq] using Real.arcsin_sin hz.1.le hz.2.le
  have hcomp : AnalyticAt ℝ (Real.arcsin ∘ Real.sin) y :=
    analyticAt_id.congr heq.symm
  have hxrad : 0 < 1 - x ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr hx)
  have hderiv : deriv Real.sin y ≠ 0 := by
    dsimp [y]
    rw [Real.deriv_sin, Real.cos_arcsin]
    exact (Real.sqrt_pos.2 hxrad).ne'
  have harcsinAtSin : AnalyticAt ℝ Real.arcsin (Real.sin y) :=
    (analyticAt_comp_iff_of_deriv_ne_zero Real.analyticAt_sin hderiv).mp hcomp
  simpa [y, Real.sin_arcsin hx'.1.le hx'.2.le] using harcsinAtSin

/-- The actual cosine--arcsine mode is analytic throughout `|u|<1`. -/
theorem analyticAt_cos_mul_arcsin {alpha u : ℝ} (hu : |u| < 1) :
    AnalyticAt ℝ (fun x : ℝ => Real.cos (alpha * Real.arcsin x)) u := by
  exact Real.analyticAt_cos.comp
    (analyticAt_const.mul (analyticAt_arcsin_of_abs_lt_one hu))

/-- The first derivative of the Gauss realization after the quadratic substitution. -/
noncomputable def cosArcsinGaussD1 (alpha u : ℝ) : ℝ :=
  2 * u * ordinaryHypergeometricD1 (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2)

/-- The second derivative of the Gauss realization after the quadratic substitution. -/
noncomputable def cosArcsinGaussD2 (alpha u : ℝ) : ℝ :=
  2 * ordinaryHypergeometricD1 (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2) +
    4 * u ^ 2 * ordinaryHypergeometricD2 (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2)

private theorem cosArcsinGauss_radius_mem {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    ‖u ^ 2‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) (1 / 2)).radius := by
  rw [cosArcsinGauss_radius_eq_one hα hα1, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [Real.norm_eq_abs, abs_pow] using (sq_lt_one_iff_abs_lt_one u).mpr hu

theorem cosArcsinGauss_hasDerivAt {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    HasDerivAt (cosArcsinGauss alpha) (cosArcsinGaussD1 alpha u) u := by
  have houter := ordinaryHypergeometric_hasDerivAt_D1
    (cosArcsinGauss_radius_mem hα hα1 hu)
  have houter' : HasDerivAt
      (ordinaryHypergeometric (-alpha / 2) (alpha / 2) (1 / 2))
      (ordinaryHypergeometricD1 (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2))
      ((fun x : ℝ => x * x) u) := by
    simpa [pow_two] using houter
  have hinner : HasDerivAt (fun x : ℝ => x * x) (u + u) u := by
    have H := ((hasDerivAt_id u).mul (hasDerivAt_id u)).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by simp)
  have hcomp := houter'.comp (h := fun x : ℝ => x * x) u hinner
  have hcomp' := hcomp.congr_of_eventuallyEq (f₁ := cosArcsinGauss alpha)
    (Filter.Eventually.of_forall fun x => by
      simp [cosArcsinGauss, pow_two])
  exact hcomp'.congr_deriv (by
    unfold cosArcsinGaussD1
    ring)

theorem cosArcsinGaussD1_hasDerivAt {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    HasDerivAt (cosArcsinGaussD1 alpha) (cosArcsinGaussD2 alpha u) u := by
  have houter := ordinaryHypergeometricD1_hasDerivAt_D2
    (cosArcsinGauss_radius_mem hα hα1 hu)
  have houter' : HasDerivAt
      (ordinaryHypergeometricD1 (-alpha / 2) (alpha / 2) (1 / 2))
      (ordinaryHypergeometricD2 (-alpha / 2) (alpha / 2) (1 / 2) (u ^ 2))
      ((fun x : ℝ => x * x) u) := by
    simpa [pow_two] using houter
  have hinner : HasDerivAt (fun x : ℝ => x * x) (u + u) u := by
    have H := ((hasDerivAt_id u).mul (hasDerivAt_id u)).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by simp)
  have hcomp := houter'.comp (h := fun x : ℝ => x * x) u hinner
  have hprod := ((hasDerivAt_id u).const_mul 2).mul hcomp
  have hprod' := hprod.congr_of_eventuallyEq (f₁ := cosArcsinGaussD1 alpha)
    (Filter.Eventually.of_forall fun x => by
      simp [cosArcsinGaussD1, Function.comp_def, pow_two])
  exact hprod'.congr_deriv (by
    unfold cosArcsinGaussD2
    simp only [Function.comp_apply, id_eq]
    rw [pow_two]
    ring)

/-- The Gauss realization satisfies the Chebyshev equation on `|u|<1`. -/
theorem cosArcsinGauss_ode {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    (1 - u ^ 2) * cosArcsinGaussD2 alpha u -
        u * cosArcsinGaussD1 alpha u + alpha ^ 2 * cosArcsinGauss alpha u = 0 := by
  have H := ordinaryHypergeometric_ode (a := -alpha / 2) (b := alpha / 2)
    (c := 1 / 2) (z := u ^ 2) (by norm_num)
    (cosArcsinGauss_radius_mem hα hα1 hu)
  unfold cosArcsinGauss cosArcsinGaussD1 cosArcsinGaussD2
  linear_combination 4 * H

/-- The actual trigonometric mode appearing on a Chebyshev inverse branch. -/
noncomputable def cosMulArcsin (alpha u : ℝ) : ℝ :=
  Real.cos (alpha * Real.arcsin u)

noncomputable def cosMulArcsinD1 (alpha u : ℝ) : ℝ :=
  -alpha * Real.sin (alpha * Real.arcsin u) / Real.sqrt (1 - u ^ 2)

noncomputable def cosMulArcsinD2 (alpha u : ℝ) : ℝ :=
  -(alpha ^ 2) * Real.cos (alpha * Real.arcsin u) / (1 - u ^ 2) -
    alpha * u * Real.sin (alpha * Real.arcsin u) /
      (Real.sqrt (1 - u ^ 2) ^ 3)

theorem cosMulArcsin_hasDerivAt {alpha u : ℝ} (hu : |u| < 1) :
    HasDerivAt (cosMulArcsin alpha) (cosMulArcsinD1 alpha u) u := by
  have hu' : -1 < u ∧ u < 1 := abs_lt.mp hu
  have hneNeg : u ≠ -1 := by linarith
  have hnePos : u ≠ 1 := by linarith
  have harc := Real.hasDerivAt_arcsin hneNeg hnePos
  have hinner := harc.const_mul alpha
  have H := hinner.cos
  have H' := H.congr_of_eventuallyEq (f₁ := cosMulArcsin alpha)
    (Filter.Eventually.of_forall fun x => by simp [cosMulArcsin])
  exact H'.congr_deriv (by
    unfold cosMulArcsinD1
    ring)

theorem cosMulArcsinD1_hasDerivAt {alpha u : ℝ} (hu : |u| < 1) :
    HasDerivAt (cosMulArcsinD1 alpha) (cosMulArcsinD2 alpha u) u := by
  have hu' : -1 < u ∧ u < 1 := abs_lt.mp hu
  have hneNeg : u ≠ -1 := by linarith
  have hnePos : u ≠ 1 := by linarith
  have hxrad : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
  have hsqrtNe : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.2 hxrad).ne'
  have harc := Real.hasDerivAt_arcsin hneNeg hnePos
  have hangle := harc.const_mul alpha
  have hsin := hangle.sin
  have hnum := hsin.const_mul (-alpha)
  have hsq : HasDerivAt (fun x : ℝ => x * x) (u + u) u := by
    have H := ((hasDerivAt_id u).mul (hasDerivAt_id u)).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by simp)
  have hrad : HasDerivAt (fun x : ℝ => 1 - x * x) (-(u + u)) u := by
    have H := ((hasDerivAt_const (x := u) (c := (1 : ℝ))).sub hsq).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => 1 - x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by ring)
  have hsqrt := hrad.sqrt (by simpa [pow_two] using hxrad.ne')
  have H := hnum.div hsqrt (by simpa [pow_two] using hsqrtNe)
  have H' := H.congr_of_eventuallyEq (f₁ := cosMulArcsinD1 alpha)
    (Filter.Eventually.of_forall fun x => by
      simp [cosMulArcsinD1, pow_two])
  exact H'.congr_deriv (by
    unfold cosMulArcsinD2
    have hsqrtSq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 :=
      Real.sq_sqrt hxrad.le
    have hsqrtCube : Real.sqrt (1 - u ^ 2) ^ 3 =
        (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) := by
      rw [show (3 : ℕ) = 2 + 1 by omega, pow_add, pow_one, hsqrtSq]
    field_simp [hsqrtNe]
    rw [hsqrtCube]
    ring)

/-- The actual trigonometric realization satisfies the same Chebyshev equation. -/
theorem cosMulArcsin_ode {alpha u : ℝ} (hu : |u| < 1) :
    (1 - u ^ 2) * cosMulArcsinD2 alpha u -
        u * cosMulArcsinD1 alpha u + alpha ^ 2 * cosMulArcsin alpha u = 0 := by
  have hxrad : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
  have hsqrtNe : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.2 hxrad).ne'
  have hsqrtSq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 :=
    Real.sq_sqrt hxrad.le
  unfold cosMulArcsin cosMulArcsinD1 cosMulArcsinD2
  field_simp [hsqrtNe]
  rw [hsqrtSq]
  ring

/-- Wronskian of the actual trigonometric mode and its Gauss realization. -/
noncomputable def cosArcsinWronskian (alpha u : ℝ) : ℝ :=
  cosMulArcsin alpha u * cosArcsinGaussD1 alpha u -
    cosMulArcsinD1 alpha u * cosArcsinGauss alpha u

theorem cosArcsinWronskian_hasDerivAt {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    HasDerivAt (cosArcsinWronskian alpha)
      (cosMulArcsin alpha u * cosArcsinGaussD2 alpha u -
        cosMulArcsinD2 alpha u * cosArcsinGauss alpha u) u := by
  have hA := cosMulArcsin_hasDerivAt (alpha := alpha) hu
  have hA1 := cosMulArcsinD1_hasDerivAt (alpha := alpha) hu
  have hG := cosArcsinGauss_hasDerivAt hα hα1 hu
  have hG1 := cosArcsinGaussD1_hasDerivAt hα hα1 hu
  have H := (hA.mul hG1).sub (hA1.mul hG)
  have H' := H.congr_of_eventuallyEq (f₁ := cosArcsinWronskian alpha)
    (Filter.Eventually.of_forall fun x => by simp [cosArcsinWronskian])
  exact H'.congr_deriv (by ring)

/-- The endpoint-regularized Wronskian for the Chebyshev equation. -/
noncomputable def scaledCosArcsinWronskian (alpha u : ℝ) : ℝ :=
  Real.sqrt (1 - u ^ 2) * cosArcsinWronskian alpha u

theorem scaledCosArcsinWronskian_hasDerivAt_zero {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    HasDerivAt (scaledCosArcsinWronskian alpha) 0 u := by
  have hxrad : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
  have hsqrtNe : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.2 hxrad).ne'
  have hsq : HasDerivAt (fun x : ℝ => x * x) (u + u) u := by
    have H := ((hasDerivAt_id u).mul (hasDerivAt_id u)).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by simp)
  have hrad : HasDerivAt (fun x : ℝ => 1 - x * x) (-(u + u)) u := by
    have H := ((hasDerivAt_const (x := u) (c := (1 : ℝ))).sub hsq).congr_of_eventuallyEq
      (f₁ := fun x : ℝ => 1 - x * x) (Filter.Eventually.of_forall fun x => by simp)
    exact H.congr_deriv (by ring)
  have hsqrt := hrad.sqrt (by simpa [pow_two] using hxrad.ne')
  have hW := cosArcsinWronskian_hasDerivAt hα hα1 hu
  have H := hsqrt.mul hW
  have H' := H.congr_of_eventuallyEq (f₁ := scaledCosArcsinWronskian alpha)
    (Filter.Eventually.of_forall fun x => by
      simp [scaledCosArcsinWronskian, pow_two])
  have hGode := cosArcsinGauss_ode hα hα1 hu
  have hAode := cosMulArcsin_ode (alpha := alpha) hu
  have hrelation :
      (1 - u ^ 2) *
          (cosMulArcsin alpha u * cosArcsinGaussD2 alpha u -
            cosMulArcsinD2 alpha u * cosArcsinGauss alpha u) =
        u * cosArcsinWronskian alpha u := by
    unfold cosArcsinWronskian
    linear_combination cosMulArcsin alpha u * hGode - cosArcsinGauss alpha u * hAode
  exact H'.congr_deriv (by
    rw [show u * u = u ^ 2 by ring]
    have hsqrtSq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 :=
      Real.sq_sqrt hxrad.le
    calc
      -(u + u) / (2 * Real.sqrt (1 - u ^ 2)) * cosArcsinWronskian alpha u +
          Real.sqrt (1 - u ^ 2) *
            (cosMulArcsin alpha u * cosArcsinGaussD2 alpha u -
              cosMulArcsinD2 alpha u * cosArcsinGauss alpha u) =
          (-u * cosArcsinWronskian alpha u +
            Real.sqrt (1 - u ^ 2) ^ 2 *
              (cosMulArcsin alpha u * cosArcsinGaussD2 alpha u -
                cosMulArcsinD2 alpha u * cosArcsinGauss alpha u)) /
            Real.sqrt (1 - u ^ 2) := by field_simp [hsqrtNe] <;> ring
      _ = 0 := by rw [hsqrtSq, hrelation]; ring)

theorem scaledCosArcsinWronskian_eq_zero {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    scaledCosArcsinWronskian alpha u = 0 := by
  have hu' : u ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hu
  have hzeroMem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hdiff : DifferentiableOn ℝ (scaledCosArcsinWronskian alpha) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (scaledCosArcsinWronskian_hasDerivAt_zero hα hα1 (abs_lt.mpr hx)).differentiableAt
      |>.differentiableWithinAt
  have hdz : Set.EqOn (deriv (scaledCosArcsinWronskian alpha)) 0
      (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (scaledCosArcsinWronskian_hasDerivAt_zero hα hα1 (abs_lt.mpr hx)).deriv
  have hconst : scaledCosArcsinWronskian alpha u = scaledCosArcsinWronskian alpha 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hdz hu' hzeroMem
  have hzero : scaledCosArcsinWronskian alpha 0 = 0 := by
    simp [scaledCosArcsinWronskian, cosArcsinWronskian, cosMulArcsin,
      cosMulArcsinD1, cosArcsinGauss, cosArcsinGaussD1]
  exact hconst.trans hzero

theorem cosArcsinWronskian_eq_zero {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    cosArcsinWronskian alpha u = 0 := by
  have hxrad : 0 < 1 - u ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
  have hsqrtNe : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.2 hxrad).ne'
  have H := scaledCosArcsinWronskian_eq_zero hα hα1 hu
  unfold scaledCosArcsinWronskian at H
  exact (mul_eq_zero.mp H).resolve_left hsqrtNe

/-- The Gauss realization is analytic at every point whose quadratic argument is inside radius one. -/
theorem analyticAt_cosArcsinGauss {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    AnalyticAt ℝ (cosArcsinGauss alpha) u := by
  let P := ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) (1 / 2)
  have hPpos : 0 < P.radius := by
    change 0 < (ordinaryHypergeometricSeries ℝ
      (-alpha / 2) (alpha / 2) (1 / 2)).radius
    rw [cosArcsinGauss_radius_eq_one hα hα1]
    norm_num
  have hzmem : u ^ 2 ∈ Metric.eball (0 : ℝ) P.radius := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    simpa only [P, ← ofReal_norm] using cosArcsinGauss_radius_mem hα hα1 hu
  have houter : AnalyticAt ℝ P.sum (u ^ 2) :=
    (P.hasFPowerSeriesOnBall hPpos).analyticAt_of_mem hzmem
  have houter' : AnalyticAt ℝ P.sum ((fun x : ℝ => x * x) u) := by
    simpa [pow_two] using houter
  have hinner : AnalyticAt ℝ (fun x : ℝ => x * x) u :=
    analyticAt_id.mul analyticAt_id
  have hcomp := houter'.comp (f := fun x : ℝ => x * x) hinner
  have hcomp' := hcomp.congr (g := cosArcsinGauss alpha)
    (Filter.Eventually.of_forall fun x => by
    simp [P, cosArcsinGauss, ordinaryHypergeometric, pow_two])
  exact hcomp'

/-- The classical cosine--arcsine hypergeometric identity on the full open unit interval. -/
theorem cos_mul_arcsin_eq_gauss {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    Real.cos (alpha * Real.arcsin u) = cosArcsinGauss alpha u := by
  have hG0 : cosArcsinGauss alpha 0 ≠ 0 := by
    simp [cosArcsinGauss]
  have hGnear : ∀ᶠ x in 𝓝 (0 : ℝ), cosArcsinGauss alpha x ≠ 0 :=
    (cosArcsinGauss_hasDerivAt hα hα1 (by norm_num : |(0 : ℝ)| < 1)).continuousAt
      |>.eventually_ne hG0
  rcases Metric.eventually_nhds_iff.mp hGnear with ⟨ε, hε, hGε⟩
  let δ : ℝ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  let R : ℝ → ℝ := fun x => cosMulArcsin alpha x / cosArcsinGauss alpha x
  have hRderiv : ∀ x ∈ Set.Ioo (-δ) δ, HasDerivAt R 0 x := by
    intro x hx
    have hxabs : |x| < δ := abs_lt.mpr hx
    have hxunit : |x| < 1 := lt_of_lt_of_le hxabs (min_le_right ε 1)
    have hxeps : dist x 0 < ε := by
      simpa [Real.dist_eq] using lt_of_lt_of_le hxabs (min_le_left ε 1)
    have hGne : cosArcsinGauss alpha x ≠ 0 := hGε hxeps
    have hA := cosMulArcsin_hasDerivAt (alpha := alpha) hxunit
    have hG := cosArcsinGauss_hasDerivAt hα hα1 hxunit
    have H := hA.div hG hGne
    have H' := H.congr_of_eventuallyEq (f₁ := R)
      (Filter.Eventually.of_forall fun y => by simp [R])
    have hW := cosArcsinWronskian_eq_zero hα hα1 hxunit
    exact H'.congr_deriv (by
      unfold cosArcsinWronskian at hW
      field_simp [hGne]
      linear_combination -hW)
  have hRdiff : DifferentiableOn ℝ R (Set.Ioo (-δ) δ) := by
    intro x hx
    exact (hRderiv x hx).differentiableAt.differentiableWithinAt
  have hRzero : Set.EqOn (deriv R) 0 (Set.Ioo (-δ) δ) := by
    intro x hx
    exact (hRderiv x hx).deriv
  have hzeroMem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by exact ⟨neg_neg_of_pos hδ, hδ⟩
  have hlocal : cosMulArcsin alpha =ᶠ[𝓝 (0 : ℝ)] cosArcsinGauss alpha := by
    change ∀ᶠ x in 𝓝 (0 : ℝ), cosMulArcsin alpha x = cosArcsinGauss alpha x
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have hxabs : |x| < δ := by simpa [Real.dist_eq] using hx
    have hxmem : x ∈ Set.Ioo (-δ) δ := abs_lt.mp hxabs
    have hxeps : dist x 0 < ε := by
      simpa [Real.dist_eq] using lt_of_lt_of_le hxabs (min_le_left ε 1)
    have hGne : cosArcsinGauss alpha x ≠ 0 := hGε hxeps
    have hconst : R x = R 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hRdiff hRzero hxmem hzeroMem
    have hratio : cosMulArcsin alpha x / cosArcsinGauss alpha x = 1 := by
      simpa [R, cosMulArcsin, cosMulArcsinD1, cosArcsinGauss] using hconst
    exact (div_eq_one_iff_eq hGne).mp hratio
  have hAanalytic : AnalyticOnNhd ℝ (cosMulArcsin alpha) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (analyticAt_cos_mul_arcsin (alpha := alpha) (abs_lt.mpr hx)).congr
      (g := cosMulArcsin alpha) (Filter.Eventually.of_forall fun y => by simp [cosMulArcsin])
  have hGanalytic : AnalyticOnNhd ℝ (cosArcsinGauss alpha) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact analyticAt_cosArcsinGauss hα hα1 (abs_lt.mpr hx)
  have hall := hAanalytic.eqOn_of_preconnected_of_eventuallyEq hGanalytic
    isPreconnected_Ioo (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hlocal
  simpa only [cosMulArcsin] using hall (abs_lt.mp hu)

/-- The exact locally convergent cosine--arcsine expansion used before termwise disk integration. -/
theorem cos_mul_arcsin_hasSum {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    HasSum (fun p : ℕ => cosArcsinCoefficient alpha p * u ^ (2 * p))
      (Real.cos (alpha * Real.arcsin u)) := by
  have H := ordinaryHypergeometric_hasSum_coeff
    (a := -alpha / 2) (b := alpha / 2) (c := 1 / 2) (z := u ^ 2)
    (cosArcsinGauss_radius_mem hα hα1 hu)
  have hvalue := cos_mul_arcsin_eq_gauss hα hα1 hu
  rw [hvalue]
  unfold cosArcsinGauss
  simpa only [cosArcsinCoefficient, pow_mul] using H

/-- Absolute summability of the cosine--arcsine expansion at every interior point. -/
theorem summable_norm_cosArcsinCoefficient {alpha u : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hu : |u| < 1) :
    Summable (fun p : ℕ => ‖cosArcsinCoefficient alpha p * u ^ (2 * p)‖) := by
  have H := (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) (1 / 2)).summable_norm_apply
    (show u ^ 2 ∈ Metric.eball (0 : ℝ)
        (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) (1 / 2)).radius by
      simpa [Metric.mem_eball] using cosArcsinGauss_radius_mem hα hα1 hu)
  refine H.congr fun p => ?_
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp only [cosArcsinCoefficient, smul_eq_mul, pow_mul]

end Hilbert16.Spikes
