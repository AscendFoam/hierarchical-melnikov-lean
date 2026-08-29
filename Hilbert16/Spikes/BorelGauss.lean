import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

set_option autoImplicit false

namespace Hilbert16.Spikes

open Nat Polynomial MeasureTheory Filter

/--
The coefficient `U_p(alpha)` from Paper Eq. (3.9).  The associated `₂F₀` series is used only as a
formal coefficient encoder; no convergence is asserted here.
-/
noncomputable def formalTwoFZeroCoefficient (alpha : ℝ) (p : ℕ) : ℝ :=
  (ascPochhammer ℝ p).eval (-alpha / 2) *
    (ascPochhammer ℝ p).eval (alpha / 2) / p.factorial

@[simp]
theorem formalTwoFZeroCoefficient_zero (alpha : ℝ) :
    formalTwoFZeroCoefficient alpha 0 = 1 := by
  simp [formalTwoFZeroCoefficient]

@[simp]
theorem formalTwoFZeroCoefficient_one (alpha : ℝ) :
    formalTwoFZeroCoefficient alpha 1 = -(alpha ^ 2) / 4 := by
  simp [formalTwoFZeroCoefficient, ascPochhammer_one]
  ring

/--
The convergent Borel image from Paper Eq. (5.3), represented by Mathlib's ordinary
hypergeometric function.  Mathlib assigns a junk value outside the power-series radius, so the
future connection-formula theorem must introduce a genuine negative-axis continuation rather than
evaluate this definition at `s < -1`.
-/
noncomputable def gaussBorelImage (alpha s : ℝ) : ℝ :=
  ordinaryHypergeometric (-alpha / 2) (alpha / 2) 1 s

@[simp]
theorem gaussBorelImage_zero (alpha : ℝ) : gaussBorelImage alpha 0 = 1 := by
  simp [gaussBorelImage]

/-- The Borel image is even in the parameter, already at the formal-series level. -/
theorem gaussBorelImage_neg (alpha s : ℝ) :
    gaussBorelImage (-alpha) s = gaussBorelImage alpha s := by
  unfold gaussBorelImage ordinaryHypergeometric
  have h := ordinaryHypergeometricSeries_symm (𝔸 := ℝ)
    (alpha / 2) (-alpha / 2) (1 : ℝ)
  simpa only [neg_div, neg_neg] using congrArg (fun F => F.sum s) h

/-- Dividing the paper's formal `₂F₀` coefficient by `p!` gives the Gauss-series coefficient. -/
theorem formalTwoFZeroCoefficient_borel (alpha : ℝ) (p : ℕ) :
    formalTwoFZeroCoefficient alpha p / p.factorial =
      ordinaryHypergeometricCoefficient (-alpha / 2) (alpha / 2) 1 p := by
  simp [formalTwoFZeroCoefficient, ordinaryHypergeometricCoefficient,
    ascPochhammer_eval_one]
  ring

/--
The exact `p`-th term of the Mathlib `₂F₁` series used as the Borel image.  Together with
`formalTwoFZeroCoefficient_borel`, this closes the coefficientwise Borel-transform identity.  The
next step is constructing the negative-real-axis continuation.
-/
theorem gaussBorelImage_term (alpha s : ℝ) (p : ℕ) :
    ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1 p (fun _ => s) =
      ((p !⁻¹ : ℝ) * (ascPochhammer ℝ p).eval (-alpha / 2) *
        (ascPochhammer ℝ p).eval (alpha / 2) *
        ((ascPochhammer ℝ p).eval 1)⁻¹) * s ^ p := by
  simpa only [smul_eq_mul] using
    ordinaryHypergeometricSeries_apply_eq (-alpha / 2) (alpha / 2) (1 : ℝ) s p

/-! ### Negative-axis Gauss connection data

The declarations below encode the specialization of DLMF 15.8.2 at
`a = -alpha / 2`, `b = alpha / 2`, `c = 1`, and `z = -x`.  They deliberately name
the *right-hand side* of the connection formula: Mathlib currently defines `₂F₁` only as its
power-series sum and supplies no analytic-continuation or Gauss-connection theorem, so equality
with a continuation of `gaussBorelImage alpha` is the remaining analytic obligation.
-/

/-- Coefficient of the growing `x ^ (alpha / 2)` branch in the negative-axis connection formula. -/
noncomputable def gaussConnectionA (alpha : ℝ) : ℝ :=
  Real.Gamma alpha /
    (Real.Gamma (alpha / 2) * Real.Gamma (1 + alpha / 2))

/-- Coefficient of the decaying `x ^ (-alpha / 2)` branch. -/
noncomputable def gaussConnectionB (alpha : ℝ) : ℝ :=
  Real.Gamma (-alpha) /
    (Real.Gamma (-alpha / 2) * Real.Gamma (1 - alpha / 2))

/-- The first convergent Gauss series in the connection formula. -/
noncomputable def gaussPhiPlus (alpha z : ℝ) : ℝ :=
  ordinaryHypergeometric (-alpha / 2) (-alpha / 2) (1 - alpha) z

/-- The second convergent Gauss series in the connection formula. -/
noncomputable def gaussPhiMinus (alpha z : ℝ) : ℝ :=
  ordinaryHypergeometric (alpha / 2) (alpha / 2) (1 + alpha) z

/--
Euler-integral representative of the analytic continuation of the Borel image on `s < 1`.
The future germ-bridge theorem must prove that this agrees with `gaussBorelImage` on `|s| < 1`;
unlike Mathlib's power-series definition, this expression remains meaningful on the full negative
axis. This is DLMF 15.6.1 specialized to `a = -alpha/2`, `b = alpha/2`, and `c = 1`, implemented
as expectation under Mathlib's `Beta(alpha/2, 1-alpha/2)` probability measure. Unfolding that
measure's density gives the usual Gamma-normalized Euler interval integral.
-/
noncomputable def gaussEulerContinuation (alpha s : ℝ) : ℝ :=
  ∫ t : ℝ, (1 - s * t) ^ (alpha / 2)
    ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)

@[simp]
theorem gaussPhiPlus_zero (alpha : ℝ) : gaussPhiPlus alpha 0 = 1 := by
  simp [gaussPhiPlus]

@[simp]
theorem gaussPhiMinus_zero (alpha : ℝ) : gaussPhiMinus alpha 0 = 1 := by
  simp [gaussPhiMinus]

/-- The Euler representative has the same constant coefficient as the Borel germ. -/
@[simp]
theorem gaussEulerContinuation_zero {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    gaussEulerContinuation alpha 0 = 1 := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta
    (show 0 < alpha / 2 by linarith) (show 0 < 1 - alpha / 2 by linarith)
  simp [gaussEulerContinuation]

/-- The Beta measure used by the Euler representative is concentrated on the open unit interval. -/
theorem betaMeasure_ae_mem_Ioo (a b : ℝ) :
    ∀ᵐ t ∂ProbabilityTheory.betaMeasure a b, t ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [ProbabilityTheory.betaMeasure,
    MeasureTheory.ae_withDensity_iff (by
      change Measurable
        (fun t => ENNReal.ofReal (ProbabilityTheory.betaPDFReal a b t))
      exact ENNReal.measurable_ofReal.comp
        (ProbabilityTheory.measurable_betaPDFReal a b))]
  filter_upwards [] with t
  intro ht
  constructor
  · by_contra h
    exact ht (ProbabilityTheory.betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
  · by_contra h
    exact ht (ProbabilityTheory.betaPDF_eq_zero_of_one_le (le_of_not_gt h))

theorem betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    0 ≤ ProbabilityTheory.betaPDFReal a b t := by
  rw [ProbabilityTheory.betaPDFReal]
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg (one_div_nonneg.mpr (ProbabilityTheory.beta_pos ha hb).le)
        (Real.rpow_nonneg h.1.le _))
      (Real.rpow_nonneg (by linarith [h.2]) _)
  · exact le_rfl

theorem betaPDF_toReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (ProbabilityTheory.betaPDF a b t).toReal =
      ProbabilityTheory.betaPDFReal a b t := by
  rw [ProbabilityTheory.betaPDF, ENNReal.toReal_ofReal]
  exact betaPDFReal_nonneg ha hb t

theorem betaPDF_measurable (a b : ℝ) :
    Measurable (ProbabilityTheory.betaPDF a b) := by
  change Measurable
    (fun t => ENNReal.ofReal (ProbabilityTheory.betaPDFReal a b t))
  exact ENNReal.measurable_ofReal.comp
    (ProbabilityTheory.measurable_betaPDFReal a b)

theorem betaPDF_ae_lt_top (a b : ℝ) :
    ∀ᵐ t : ℝ, ProbabilityTheory.betaPDF a b t < ⊤ := by
  exact ae_of_all _ fun t => by simp [ProbabilityTheory.betaPDF]

/-- Rewrite an expectation against a beta distribution as its defining interval integral. -/
theorem betaMeasure_integral_eq_intervalIntegral {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ) :
    ∫ t : ℝ, f t ∂ProbabilityTheory.betaMeasure a b =
      (ProbabilityTheory.beta a b)⁻¹ *
        ∫ t : ℝ in 0..1, t ^ (a - 1) * (1 - t) ^ (b - 1) * f t := by
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable a b) (betaPDF_ae_lt_top a b)]
  simp_rw [betaPDF_toReal ha hb, smul_eq_mul]
  have hfun :
      (fun t : ℝ => ProbabilityTheory.betaPDFReal a b t * f t) =
        (Set.Ioo (0 : ℝ) 1).indicator
          (fun t => (ProbabilityTheory.beta a b)⁻¹ *
            (t ^ (a - 1) * (1 - t) ^ (b - 1) * f t)) := by
    funext t
    rw [ProbabilityTheory.betaPDFReal]
    split_ifs with h
    · have hmem : t ∈ Set.Ioo (0 : ℝ) 1 := h
      rw [Set.indicator_apply, if_pos hmem]
      ring
    · have hmem : t ∉ Set.Ioo (0 : ℝ) 1 := h
      rw [Set.indicator_apply, if_neg hmem]
      simp
  rw [hfun, integral_indicator measurableSet_Ioo]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [← intervalIntegral.integral_const_mul]

private theorem betaPDFReal_mul_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (t : ℝ) :
    ProbabilityTheory.betaPDFReal a b t * t ^ n =
      (ProbabilityTheory.beta (a + n) b / ProbabilityTheory.beta a b) *
        ProbabilityTheory.betaPDFReal (a + n) b t := by
  rw [ProbabilityTheory.betaPDFReal, ProbabilityTheory.betaPDFReal]
  split_ifs with h
  · have hBab : ProbabilityTheory.beta a b ≠ 0 :=
      (ProbabilityTheory.beta_pos ha hb).ne'
    have hBshift : ProbabilityTheory.beta (a + n) b ≠ 0 :=
      (ProbabilityTheory.beta_pos (by positivity) hb).ne'
    field_simp
    rw [← Real.rpow_natCast]
    calc
      t ^ (a - 1) * (1 - t) ^ (b - 1) * t ^ (n : ℝ) =
          (1 - t) ^ (b - 1) * (t ^ (a - 1) * t ^ (n : ℝ)) := by ring
      _ = (1 - t) ^ (b - 1) * t ^ ((a - 1) + n) := by
        rw [Real.rpow_add h.1]
      _ = (1 - t) ^ (b - 1) * t ^ (a + n - 1) := by ring_nf
  · simp

/-- Natural moments of Mathlib's real Beta probability measure. -/
theorem betaMeasure_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ t : ℝ, t ^ n ∂ProbabilityTheory.betaMeasure a b =
      ProbabilityTheory.beta (a + n) b / ProbabilityTheory.beta a b := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta (show 0 < a + n by positivity) hb
  have hone : ∫ t : ℝ, (1 : ℝ) ∂ProbabilityTheory.betaMeasure (a + n) b = 1 := by
    simp
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable a b) (betaPDF_ae_lt_top a b)]
  simp_rw [betaPDF_toReal ha hb, smul_eq_mul]
  rw [MeasureTheory.integral_congr_ae
    (ae_of_all _ (betaPDFReal_mul_pow ha hb n)), MeasureTheory.integral_const_mul]
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable (a + n) b) (betaPDF_ae_lt_top (a + n) b)] at hone
  simp_rw [betaPDF_toReal (show 0 < a + n by positivity) hb, smul_eq_mul, mul_one] at hone
  rw [hone, mul_one]

private theorem betaPDFReal_mul_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) (t : ℝ) :
    ProbabilityTheory.betaPDFReal a b t * t ^ q =
      (ProbabilityTheory.beta (a + q) b / ProbabilityTheory.beta a b) *
        ProbabilityTheory.betaPDFReal (a + q) b t := by
  rw [ProbabilityTheory.betaPDFReal, ProbabilityTheory.betaPDFReal]
  split_ifs with h
  · have hBab : ProbabilityTheory.beta a b ≠ 0 :=
      (ProbabilityTheory.beta_pos ha hb).ne'
    have hBshift : ProbabilityTheory.beta (a + q) b ≠ 0 :=
      (ProbabilityTheory.beta_pos haq hb).ne'
    field_simp
    calc
      t ^ (a - 1) * (1 - t) ^ (b - 1) * t ^ q =
          (1 - t) ^ (b - 1) * (t ^ (a - 1) * t ^ q) := by ring
      _ = (1 - t) ^ (b - 1) * t ^ ((a - 1) + q) := by
        rw [Real.rpow_add h.1]
      _ = (1 - t) ^ (b - 1) * t ^ (a + q - 1) := by ring_nf
  · simp

/-- Real moments of a Beta probability law, including the nonintegral moments needed at infinity. -/
theorem betaMeasure_rpow_moment {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    ∫ t : ℝ, t ^ q ∂ProbabilityTheory.betaMeasure a b =
      ProbabilityTheory.beta (a + q) b / ProbabilityTheory.beta a b := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta haq hb
  have hone : ∫ t : ℝ, (1 : ℝ) ∂ProbabilityTheory.betaMeasure (a + q) b = 1 := by
    simp
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable a b) (betaPDF_ae_lt_top a b)]
  simp_rw [betaPDF_toReal ha hb, smul_eq_mul]
  rw [MeasureTheory.integral_congr_ae
    (ae_of_all _ (betaPDFReal_mul_rpow ha hb haq)), MeasureTheory.integral_const_mul]
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable (a + q) b) (betaPDF_ae_lt_top (a + q) b)] at hone
  simp_rw [betaPDF_toReal haq hb, smul_eq_mul, mul_one] at hone
  rw [hone, mul_one]

private theorem betaPDFReal_mul_one_sub_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbq : 0 < b + q) (t : ℝ) :
    ProbabilityTheory.betaPDFReal a b t * (1 - t) ^ q =
      (ProbabilityTheory.beta a (b + q) / ProbabilityTheory.beta a b) *
        ProbabilityTheory.betaPDFReal a (b + q) t := by
  rw [ProbabilityTheory.betaPDFReal, ProbabilityTheory.betaPDFReal]
  split_ifs with h
  · have hBab : ProbabilityTheory.beta a b ≠ 0 :=
      (ProbabilityTheory.beta_pos ha hb).ne'
    have hBshift : ProbabilityTheory.beta a (b + q) ≠ 0 :=
      (ProbabilityTheory.beta_pos ha hbq).ne'
    field_simp
    calc
      t ^ (a - 1) * (1 - t) ^ (b - 1) * (1 - t) ^ q =
          t ^ (a - 1) * ((1 - t) ^ (b - 1) * (1 - t) ^ q) := by ring
      _ = t ^ (a - 1) * (1 - t) ^ ((b - 1) + q) := by
        rw [Real.rpow_add (by linarith [h.2])]
      _ = t ^ (a - 1) * (1 - t) ^ (b + q - 1) := by ring_nf
  · simp

/-- Moments of `1-t` under a Beta probability law. -/
theorem betaMeasure_one_sub_rpow_moment {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbq : 0 < b + q) :
    ∫ t : ℝ, (1 - t) ^ q ∂ProbabilityTheory.betaMeasure a b =
      ProbabilityTheory.beta a (b + q) / ProbabilityTheory.beta a b := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta ha hbq
  have hone : ∫ t : ℝ, (1 : ℝ) ∂ProbabilityTheory.betaMeasure a (b + q) = 1 := by
    simp
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable a b) (betaPDF_ae_lt_top a b)]
  simp_rw [betaPDF_toReal ha hb, smul_eq_mul]
  rw [MeasureTheory.integral_congr_ae
    (ae_of_all _ (betaPDFReal_mul_one_sub_rpow ha hb hbq)),
    MeasureTheory.integral_const_mul]
  rw [ProbabilityTheory.betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (betaPDF_measurable a (b + q)) (betaPDF_ae_lt_top a (b + q))] at hone
  simp_rw [betaPDF_toReal ha hbq, smul_eq_mul, mul_one] at hone
  rw [hone, mul_one]

/-- Integrability companion to `betaMeasure_one_sub_rpow_moment`. -/
theorem betaMeasure_one_sub_rpow_integrable {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbq : 0 < b + q) :
    Integrable (fun t : ℝ => (1 - t) ^ q) (ProbabilityTheory.betaMeasure a b) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (ProbabilityTheory.betaMeasure a (b + q)) := by
    let _ := ProbabilityTheory.isProbabilityMeasureBeta ha hbq
    exact integrable_const 1
  rw [ProbabilityTheory.betaMeasure,
    integrable_withDensity_iff_integrable_smul'
      (betaPDF_measurable a (b + q)) (betaPDF_ae_lt_top a (b + q))] at hone
  simp_rw [betaPDF_toReal ha hbq, smul_eq_mul, mul_one] at hone
  rw [ProbabilityTheory.betaMeasure,
    integrable_withDensity_iff_integrable_smul'
      (betaPDF_measurable a b) (betaPDF_ae_lt_top a b)]
  simp_rw [betaPDF_toReal ha hb, smul_eq_mul]
  have hfun :
      (fun t : ℝ => ProbabilityTheory.betaPDFReal a b t * (1 - t) ^ q) =
        fun t => (ProbabilityTheory.beta a (b + q) / ProbabilityTheory.beta a b) *
          ProbabilityTheory.betaPDFReal a (b + q) t := by
    funext t
    exact betaPDFReal_mul_one_sub_rpow ha hb hbq t
  rw [hfun]
  exact hone.const_mul _

/-- Real positive-argument specialization of the Gamma/Pochhammer ratio. -/
theorem Gamma_add_nat_div_Gamma_eq_ascPochhammer {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.Gamma (u + n) / Real.Gamma u = (ascPochhammer ℝ n).eval u := by
  induction n with
  | zero => simp [(Real.Gamma_pos_of_pos hu).ne']
  | succ n ih =>
      have hrec := Real.Gamma_add_one (s := u + n) (by positivity : u + n ≠ 0)
      rw [Nat.cast_succ]
      rw [show u + (↑n + 1) = (u + n) + 1 by ring, hrec]
      rw [ascPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
      rw [← ih]
      field_simp

private theorem beta_ratio_special {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (n : ℕ) :
    ProbabilityTheory.beta (u + n) (1 - u) / ProbabilityTheory.beta u (1 - u) =
      (ascPochhammer ℝ n).eval u / n.factorial := by
  have hGu : Real.Gamma u ≠ 0 := (Real.Gamma_pos_of_pos hu).ne'
  have hGoneSub : Real.Gamma (1 - u) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [ProbabilityTheory.beta, ProbabilityTheory.beta]
  rw [show u + (1 - u) = 1 by ring,
    show u + ↑n + (1 - u) = (n : ℝ) + 1 by ring,
    Real.Gamma_nat_eq_factorial]
  have hratio := Gamma_add_nat_div_Gamma_eq_ascPochhammer hu n
  have hGsum : Real.Gamma (u + n) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [Real.Gamma_one]
  field_simp
  rw [← hratio]
  field_simp

/-- The exact Beta moment needed in the specialized Euler--Gauss integral. -/
theorem gaussBetaMoment {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) (n : ℕ) :
    ∫ t : ℝ, t ^ n
      ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2) =
        (ascPochhammer ℝ n).eval (alpha / 2) / n.factorial := by
  rw [betaMeasure_moment (by linarith : 0 < alpha / 2)
    (by linarith : 0 < 1 - alpha / 2)]
  exact beta_ratio_special (by linarith) (by linarith) n

/-- On the open unit disk, the Euler--Beta continuation is the original Borel
hypergeometric series. The proof expands the real binomial power, dominates the
terms uniformly on the support of the Beta law, and evaluates every Beta moment. -/
theorem gaussEulerContinuation_eq_borelImage {alpha s : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hs : |s| < 1) :
    gaussEulerContinuation alpha s = gaussBorelImage alpha s := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let F : ℕ → ℝ → ℝ := fun n t => Ring.choose u n * (-s * t) ^ n
  let bound : ℕ → ℝ → ℝ := fun n _ =>
    ‖binomialSeries ℝ u n (fun _ => |s|)‖
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  have hbinomialSummable :
      Summable fun n => ‖binomialSeries ℝ u n (fun _ => |s|)‖ := by
    apply FormalMultilinearSeries.summable_norm_apply
    rw [Metric.mem_eball, edist_dist,
      binomialSeries_radius_eq_one (𝔸 := ℝ) (fun k hk => by
        have hk0 : k = 0 := by
          by_contra hk0
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
          linarith
        subst k
        norm_num at hk
        linarith), ENNReal.ofReal_lt_one]
    simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg s)] using hs
  have hboundSummable : ∀ᵐ t ∂μ, Summable fun n => bound n t := by
    exact ae_of_all _ fun _ => hbinomialSummable
  have hboundIntegrable : Integrable (fun t => ∑' n, bound n t) μ := by
    simpa [bound] using
      (integrable_const (μ := μ)
        (∑' n, ‖binomialSeries ℝ u n (fun _ => |s|)‖))
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (by fun_prop : Continuous (F n)).aestronglyMeasurable
  have hFbound : ∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ bound n t := by
    intro n
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have htAbs : |t| ≤ 1 := by
      rw [abs_of_pos ht.1]
      exact ht.2.le
    calc
      ‖F n t‖ = |Ring.choose u n| * (|s| * |t|) ^ n := by
        simp [F, norm_mul, norm_pow, abs_mul]
      _ ≤ |Ring.choose u n| * |s| ^ n := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left htAbs (abs_nonneg s)
      _ = bound n t := by
        simp [bound, binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm]
  have hFlim : ∀ᵐ t ∂μ, HasSum (fun n => F n t) ((1 - s * t) ^ u) := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hst : |-s * t| < 1 := by
      rw [abs_mul, abs_neg]
      calc
        |s| * |t| ≤ |s| * 1 := mul_le_mul_of_nonneg_left
          (by simpa [abs_of_pos ht.1] using ht.2.le) (abs_nonneg s)
        _ < 1 := by simpa using hs
    have hmem : -s * t ∈ Metric.eball (0 : ℝ) 1 := by
      rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
      simpa [Real.dist_eq] using hst
    simpa [F, binomialSeries, FormalMultilinearSeries.coeff_ofScalars,
      mul_comm, sub_eq_add_neg] using
      (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := u)).hasSum hmem
  have hIntegrated :
      HasSum (fun n => ∫ t, F n t ∂μ) (gaussEulerContinuation alpha s) := by
    have h := MeasureTheory.hasSum_integral_of_dominated_convergence
      bound hFmeas hFbound hboundSummable hboundIntegrable hFlim
    simpa [μ, u, gaussEulerContinuation] using h
  have hterm (n : ℕ) :
      (∫ t, F n t ∂μ) =
        ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1 n (fun _ => s) := by
    dsimp [F, μ, u]
    rw [show (fun t : ℝ => Ring.choose (alpha / 2) n * (-s * t) ^ n) =
        fun t => (Ring.choose (alpha / 2) n * (-s) ^ n) * t ^ n by
      funext t
      rw [mul_pow]
      ring]
    rw [MeasureTheory.integral_const_mul, gaussBetaMoment hα hα1]
    rw [ordinaryHypergeometricSeries_apply_eq]
    simp only [smul_eq_mul, ascPochhammer_eval_one]
    have hchoose : Ring.choose (alpha / 2) n =
        (n.factorial : ℝ)⁻¹ * (descPochhammer ℝ n).eval (alpha / 2) := by
      rw [Ring.choose_eq_smul, smul_eq_mul,
        Polynomial.descPochhammer_smeval_eq_ascPochhammer,
        Polynomial.ascPochhammer_smeval_eq_eval,
        ← descPochhammer_eval_eq_ascPochhammer]
    have hpoch := ascPochhammer_eval_neg_eq_descPochhammer (R := ℝ) (alpha / 2) n
    have hpoch' : (ascPochhammer ℝ n).eval (-alpha / 2) =
        (-1) ^ n * (descPochhammer ℝ n).eval (alpha / 2) := by
      convert hpoch using 1 <;> ring
    have hneg : (-s) ^ n = (-1 : ℝ) ^ n * s ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [hchoose, hpoch', hneg]
    simp only [div_eq_mul_inv]
    ring
  have htermFun :
      (fun n => ∫ t, F n t ∂μ) =
        (fun n => ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1 n
          (fun _ => s)) := funext hterm
  have hGauss :
      HasSum
        (fun n => ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1 n
          (fun _ => s))
        (gaussEulerContinuation alpha s) := by
    rw [← htermFun]
    exact hIntegrated
  unfold gaussBorelImage ordinaryHypergeometric FormalMultilinearSeries.sum
  exact hGauss.tsum_eq.symm

/-- For every `s < 1`, the real-power base in the Euler representative is positive almost
everywhere. This is the branch-safety fact needed for differentiation and dominated convergence. -/
theorem betaMeasure_one_sub_mul_pos_ae (a b : ℝ) {s : ℝ} (hs : s < 1) :
    ∀ᵐ t ∂ProbabilityTheory.betaMeasure a b, 0 < 1 - s * t := by
  filter_upwards [betaMeasure_ae_mem_Ioo a b] with t ht
  rcases le_total s 0 with hs0 | hs0
  · have hst : s * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 ht.1.le
    linarith
  · rcases hs0.eq_or_lt with rfl | hspos
    · norm_num
    · have hst : s * t < s * 1 := mul_lt_mul_of_pos_left ht.2 hspos
      linarith

/-- Consequently, the Euler integrand itself is positive almost everywhere on `s < 1`. -/
theorem gaussEulerIntegrand_pos_ae {alpha s : ℝ} (hs : s < 1) :
    ∀ᵐ t ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2),
      0 < (1 - s * t) ^ (alpha / 2) := by
  filter_upwards
    [betaMeasure_one_sub_mul_pos_ae (alpha / 2) (1 - alpha / 2) hs] with t ht
  exact Real.rpow_pos_of_pos ht _

/-- The Euler representative is a genuine Bochner integral, rather than the integral's junk value,
throughout the paper's parameter range and the whole continuation domain `s < 1`. -/
theorem gaussEulerIntegrand_integrable {alpha s : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1)
    (hs : s < 1) :
    MeasureTheory.Integrable (fun t : ℝ => (1 - s * t) ^ (alpha / 2))
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta
    (show 0 < alpha / 2 by linarith) (show 0 < 1 - alpha / 2 by linarith)
  refine MeasureTheory.Integrable.of_bound (C := (1 + |s|) ^ (alpha / 2))
    (by fun_prop (disch := linarith)) ?_
  filter_upwards
    [betaMeasure_ae_mem_Ioo (alpha / 2) (1 - alpha / 2),
      betaMeasure_one_sub_mul_pos_ae (alpha / 2) (1 - alpha / 2) hs] with t ht hbase
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hbase _)]
  apply Real.rpow_le_rpow hbase.le
  · have htAbs : |t| ≤ 1 := by
      rw [abs_of_pos ht.1]
      exact ht.2.le
    have hmul : |s * t| ≤ |s| := by
      calc
        |s * t| = |s| * |t| := abs_mul s t
        _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left htAbs (abs_nonneg s)
        _ = |s| := mul_one _
    have hneg : -(s * t) ≤ |s * t| := neg_le_abs (s * t)
    linarith
  · linarith

/-- The chosen continuation is positive on the entire real domain `s < 1`. -/
theorem gaussEulerContinuation_pos {alpha s : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1)
    (hs : s < 1) : 0 < gaussEulerContinuation alpha s := by
  let _ := ProbabilityTheory.isProbabilityMeasureBeta
    (show 0 < alpha / 2 by linarith) (show 0 < 1 - alpha / 2 by linarith)
  unfold gaussEulerContinuation
  have hpos := gaussEulerIntegrand_pos_ae (alpha := alpha) hs
  have hint := gaussEulerIntegrand_integrable hα hα1 hs
  have hnonneg :
      ∀ᵐ t ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2),
        0 ≤ (1 - s * t) ^ (alpha / 2) :=
    hpos.mono fun _ ht => ht.le
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsupport :
      ∀ᵐ t ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2),
        t ∈ Function.support (fun t : ℝ => (1 - s * t) ^ (alpha / 2)) :=
    hpos.mono fun _ ht => ht.ne'
  have hmeas : Measurable (fun t : ℝ => (1 - s * t) ^ (alpha / 2)) := by
    fun_prop (disch := linarith)
  have hmeasure :
      ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)
          (Function.support (fun t : ℝ => (1 - s * t) ^ (alpha / 2))) = 1 :=
    (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_support hmeas)).mp hsupport
  rw [hmeasure]
  norm_num

/-- The coefficient of the growing Frobenius branch at negative infinity is obtained directly
from the Euler--Beta integral.  This is the first of the two boundary data used to identify the
connection formula without assuming a library hypergeometric-continuation theorem. -/
theorem gaussEulerContinuation_leading_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto
      (fun x : ℝ => gaussEulerContinuation alpha (-x) / x ^ (alpha / 2))
      atTop (nhds (gaussConnectionA alpha)) := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  have hDCT :
      Tendsto (fun x : ℝ => ∫ t, (t + x⁻¹) ^ u ∂μ) atTop
        (nhds (∫ t, t ^ u ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => (2 : ℝ) ^ u)
    · filter_upwards with x
      exact ((continuous_id.add continuous_const).rpow_const
        (fun _ => Or.inr hu.le)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
      have htx0 : 0 ≤ t + x⁻¹ :=
        add_nonneg ht.1.le (inv_nonneg.mpr (by linarith : 0 ≤ x))
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htx0 u)]
      exact Real.rpow_le_rpow htx0
        (by
          have hinv1 : x⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < x)).mpr hx
          calc
            t + x⁻¹ ≤ 1 + 1 := add_le_add ht.2.le hinv1
            _ = 2 := by norm_num)
        hu.le
    · exact integrable_const _
    · filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
      have ht0 : t + 0 ≠ 0 := by simpa using ht.1.ne'
      simpa using
        (tendsto_const_nhds.add tendsto_inv_atTop_zero).rpow_const (.inl ht0)
  have hrewrite : ∀ᶠ x : ℝ in atTop,
      gaussEulerContinuation alpha (-x) / x ^ u =
        ∫ t, (t + x⁻¹) ^ u ∂μ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [u, μ]
    unfold gaussEulerContinuation
    rw [← MeasureTheory.integral_div]
    apply integral_congr_ae
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hxt : 0 < x * t := mul_pos hx ht.1
    have hbase : 0 ≤ 1 - -x * t := by linarith
    rw [← Real.div_rpow hbase hx.le]
    congr 1
    field_simp
    ring
  have hmoment : (∫ t, t ^ u ∂μ) = gaussConnectionA alpha := by
    rw [betaMeasure_rpow_moment hu (by linarith) (by linarith : 0 < u + u)]
    dsimp [u, μ]
    unfold gaussConnectionA ProbabilityTheory.beta
    rw [show alpha / 2 + alpha / 2 = alpha by ring,
      show alpha / 2 + (1 - alpha / 2) = 1 by ring,
      show alpha + (1 - alpha / 2) = 1 + alpha / 2 by ring,
      Real.Gamma_one]
    field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < alpha / 2)).ne',
      (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - alpha / 2)).ne',
      (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + alpha / 2)).ne']
    rw [div_self (Real.Gamma_pos_of_pos (by linarith : 0 < (2 - alpha) / 2)).ne']
  change Tendsto
    (fun x : ℝ => gaussEulerContinuation alpha (-x) / x ^ u)
    atTop (nhds (gaussConnectionA alpha))
  rw [← hmoment]
  exact hDCT.congr' (hrewrite.mono fun _ h => h.symm)

/-- Differentiation of the Euler continuation along the negative axis. -/
theorem gaussEulerContinuation_neg_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => gaussEulerContinuation alpha (-y))
      (∫ t : ℝ, (alpha / 2) * t *
        (1 + x * t) ^ (alpha / 2 - 1)
        ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) x := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let F : ℝ → ℝ → ℝ := fun y t => (1 + y * t) ^ u
  let F' : ℝ → ℝ → ℝ := fun y t => u * t * (1 + y * t) ^ (u - 1)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  have hs : Set.Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
  have hFmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (F y) μ := by
    filter_upwards with y
    exact ((continuous_const.add (continuous_const.mul continuous_id)).rpow_const
      (fun _ => Or.inr hu.le)).aestronglyMeasurable
  have hFint : Integrable (F x) μ := by
    simpa [F, μ, u, sub_eq_add_neg] using
      gaussEulerIntegrand_integrable hα hα1 (show -x < 1 by linarith)
  have hF'meas : AEStronglyMeasurable (F' x) μ := by
    exact (by fun_prop (disch := linarith) : Measurable (F' x)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ Set.Ioi (0 : ℝ), ‖F' y t‖ ≤ u := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    intro y hy
    have hyt : 0 ≤ y * t := mul_nonneg hy.le ht.1.le
    have hbase : 1 ≤ 1 + y * t := by linarith
    have hbase0 : 0 ≤ 1 + y * t := le_trans zero_le_one hbase
    have hrpow : (1 + y * t) ^ (u - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have hnonneg : 0 ≤ F' y t := by
      exact mul_nonneg (mul_nonneg hu.le ht.1.le) (Real.rpow_nonneg hbase0 _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp [F']
    have hprod : t * (1 + y * t) ^ (u - 1) ≤ 1 :=
      mul_le_one₀ ht.2.le (Real.rpow_nonneg hbase0 _) hrpow
    nlinarith
  have hdiff : ∀ᵐ t ∂μ, ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (F · t) (F' y t) y := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    intro y hy
    have hyt : 0 < y * t := mul_pos hy ht.1
    have hbase : 0 < 1 + y * t := by linarith
    dsimp [F, F']
    have hinner : HasDerivAt (fun z : ℝ => 1 + z * t) t y := by
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id y).mul_const t).const_add (1 : ℝ)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hinner.rpow_const (.inl hbase.ne')
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => u) (s := Set.Ioi 0)
    hs hFmeas hFint hF'meas hbound (integrable_const _) hdiff
  simpa [F, F', μ, u, gaussEulerContinuation, sub_eq_add_neg] using h.2

/--
The candidate negative-axis value furnished by the two convergent series at `-1 / x`.
For `x > 0`, the real powers here are exactly the principal powers `(-z)⁻ᵃ` in DLMF 15.8.2,
because its `z` is `-x` and hence `-z = x > 0`.
-/
noncomputable def negativeAxisConnectionRHS (alpha x : ℝ) : ℝ :=
  gaussConnectionA alpha * x ^ (alpha / 2) * gaussPhiPlus alpha (-(x⁻¹)) +
    gaussConnectionB alpha * x ^ (-alpha / 2) * gaussPhiMinus alpha (-(x⁻¹))

/-- Exact theorem contract for Paper Eq. (5.5).  It is a named proposition, not a theorem: proving
this proposition is the remaining specialized Gauss-connection obligation. -/
def NegativeAxisConnectionFormula (alpha : ℝ) : Prop :=
  ∀ x : ℝ, 1 < x →
    gaussEulerContinuation alpha (-x) = negativeAxisConnectionRHS alpha x

/-- On the negative axis beyond the singular point, both transformed Gauss series are evaluated
strictly inside their unit disk. -/
theorem negativeAxis_inverse_mem_unitDisk {x : ℝ} (hx : 1 < x) :
    |-(x⁻¹)| < 1 := by
  rw [abs_neg, abs_inv, abs_of_pos (by linarith : 0 < x)]
  exact inv_lt_one_of_one_lt₀ hx

private theorem natCast_ne_pos_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (n : ℕ) :
    (n : ℝ) ≠ t := by
  cases n with
  | zero => norm_num; linarith
  | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      linarith

private theorem natCast_ne_neg_of_pos {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (n : ℝ) ≠ -t := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The first transformed `₂F₁` has radius exactly one in the paper's parameter range. -/
theorem gaussPhiPlus_radius_eq_one {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    (ordinaryHypergeometricSeries ℝ (-alpha / 2) (-alpha / 2) (1 - alpha)).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro n
  have hhalf : (n : ℝ) ≠ alpha / 2 :=
    natCast_ne_pos_lt_one (by linarith) (by linarith) n
  have honeSub : (n : ℝ) ≠ -(1 - alpha) :=
    natCast_ne_neg_of_pos (by linarith) n
  simpa only [neg_div, neg_neg] using ⟨hhalf, hhalf, honeSub⟩

/-- The second transformed `₂F₁` also has radius exactly one. -/
theorem gaussPhiMinus_radius_eq_one {alpha : ℝ} (hα : 0 < alpha) :
    (ordinaryHypergeometricSeries ℝ (alpha / 2) (alpha / 2) (1 + alpha)).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro n
  have hhalf : (n : ℝ) ≠ -(alpha / 2) :=
    natCast_ne_neg_of_pos (by linarith) n
  have honeAdd : (n : ℝ) ≠ -(1 + alpha) :=
    natCast_ne_neg_of_pos (by linarith) n
  exact ⟨hhalf, hhalf, honeAdd⟩

/-- Explicit convergence certificate for the growing-branch Gauss series on the negative axis. -/
theorem gaussPhiPlus_hasSum {alpha x : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1)
    (hx : 1 < x) :
    HasSum
      (fun n => ordinaryHypergeometricSeries ℝ (-alpha / 2) (-alpha / 2) (1 - alpha) n
        (fun _ => -(x⁻¹)))
      (gaussPhiPlus alpha (-(x⁻¹))) := by
  unfold gaussPhiPlus ordinaryHypergeometric
  apply FormalMultilinearSeries.hasSum
  rw [Metric.mem_eball, edist_dist,
    gaussPhiPlus_radius_eq_one hα hα1, ENNReal.ofReal_lt_one]
  simpa [Real.dist_eq] using negativeAxis_inverse_mem_unitDisk hx

/-- Explicit convergence certificate for the decaying-branch Gauss series on the negative axis. -/
theorem gaussPhiMinus_hasSum {alpha x : ℝ} (hα : 0 < alpha) (hx : 1 < x) :
    HasSum
      (fun n => ordinaryHypergeometricSeries ℝ (alpha / 2) (alpha / 2) (1 + alpha) n
        (fun _ => -(x⁻¹)))
      (gaussPhiMinus alpha (-(x⁻¹))) := by
  unfold gaussPhiMinus ordinaryHypergeometric
  apply FormalMultilinearSeries.hasSum
  rw [Metric.mem_eball, edist_dist,
    gaussPhiMinus_radius_eq_one hα, ENNReal.ofReal_lt_one]
  simpa [Real.dist_eq] using negativeAxis_inverse_mem_unitDisk hx

private theorem Gamma_neg_ne_zero_of_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Real.Gamma (-t) ≠ 0 := by
  intro hzero
  have hrec := Real.Gamma_add_one (s := -t) (by linarith : -t ≠ 0)
  have hpos : 0 < Real.Gamma (-t + 1) := Real.Gamma_pos_of_pos (by linarith)
  rw [hrec, hzero, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

private theorem Gamma_neg_neg_of_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Real.Gamma (-t) < 0 := by
  have hrec := Real.Gamma_add_one (s := -t) (by linarith : -t ≠ 0)
  have hproduct : 0 < -t * Real.Gamma (-t) := by
    rw [← hrec]
    exact Real.Gamma_pos_of_pos (by linarith)
  rcases (mul_pos_iff.mp hproduct) with h | h
  · linarith [h.1]
  · exact h.2

/-- The leading connection coefficient is positive throughout the paper's range. -/
theorem gaussConnectionA_pos {alpha : ℝ} (hα : 0 < alpha) :
    0 < gaussConnectionA alpha := by
  unfold gaussConnectionA
  exact div_pos (Real.Gamma_pos_of_pos hα)
    (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith)))

theorem gaussConnectionA_ne_zero {alpha : ℝ} (hα : 0 < alpha) :
    gaussConnectionA alpha ≠ 0 :=
  (gaussConnectionA_pos hα).ne'

/-- The second connection coefficient also cannot vanish for `0 < alpha < 1`. -/
theorem gaussConnectionB_ne_zero {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    gaussConnectionB alpha ≠ 0 := by
  have hhalf : Real.Gamma (-alpha / 2) ≠ 0 := by
    simpa only [neg_div] using
      (Gamma_neg_ne_zero_of_lt_one (t := alpha / 2) (by linarith) (by linarith))
  unfold gaussConnectionB
  exact div_ne_zero
    (Gamma_neg_ne_zero_of_lt_one hα hα1)
    (mul_ne_zero
      hhalf
      (Real.Gamma_pos_of_pos (by linarith)).ne')

/-- In fact the second coefficient has the same positive sign as the leading coefficient. -/
theorem gaussConnectionB_pos {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    0 < gaussConnectionB alpha := by
  unfold gaussConnectionB
  exact div_pos_of_neg_of_neg
    (Gamma_neg_neg_of_lt_one hα hα1)
    (mul_neg_of_neg_of_pos
      (by
        simpa only [neg_div] using
          (Gamma_neg_neg_of_lt_one (t := alpha / 2) (by linarith) (by linarith)))
      (Real.Gamma_pos_of_pos (by linarith)))

/-- The coefficient produced directly by DLMF 15.8.2 after converting its regularized first
right-hand `₂F₁` to Mathlib's ordinary normalization. -/
noncomputable def dlmfConnectionA (alpha : ℝ) : ℝ :=
  (Real.pi / Real.sin (Real.pi * alpha)) /
    (Real.Gamma (alpha / 2) * Real.Gamma (1 + alpha / 2) *
      Real.Gamma (1 - alpha))

/-- The corresponding raw DLMF coefficient of the second branch; the minus sign is the one in
DLMF 15.8.2. -/
noncomputable def dlmfConnectionB (alpha : ℝ) : ℝ :=
  -(Real.pi / Real.sin (Real.pi * alpha)) /
    (Real.Gamma (-alpha / 2) * Real.Gamma (1 - alpha / 2) *
      Real.Gamma (1 + alpha))

/-- Euler's reflection formula reduces the first raw DLMF coefficient to the paper's `A_alpha`. -/
theorem dlmfConnectionA_eq {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    dlmfConnectionA alpha = gaussConnectionA alpha := by
  unfold dlmfConnectionA gaussConnectionA
  rw [← Real.Gamma_mul_Gamma_one_sub alpha]
  field_simp [(Real.Gamma_pos_of_pos hα).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < alpha / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + alpha / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - alpha)).ne']

/-- Euler's reflection formula at `-alpha` reduces the signed second DLMF coefficient to the
paper's `B_alpha`. -/
theorem dlmfConnectionB_eq {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    dlmfConnectionB alpha = gaussConnectionB alpha := by
  have hreflection :
      Real.Gamma (-alpha) * Real.Gamma (1 + alpha) =
        -(Real.pi / Real.sin (Real.pi * alpha)) := by
    calc
      Real.Gamma (-alpha) * Real.Gamma (1 + alpha) =
          Real.pi / -Real.sin (Real.pi * alpha) := by
        simpa [Real.sin_neg] using Real.Gamma_mul_Gamma_one_sub (-alpha)
      _ = -(Real.pi / Real.sin (Real.pi * alpha)) := by ring
  have hhalf : Real.Gamma (-alpha / 2) ≠ 0 := by
    simpa only [neg_div] using
      (Gamma_neg_ne_zero_of_lt_one (t := alpha / 2) (by linarith) (by linarith))
  unfold dlmfConnectionB gaussConnectionB
  rw [← hreflection]
  field_simp [Gamma_neg_ne_zero_of_lt_one hα hα1,
    hhalf,
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - alpha / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + alpha)).ne']

end Hilbert16.Spikes
