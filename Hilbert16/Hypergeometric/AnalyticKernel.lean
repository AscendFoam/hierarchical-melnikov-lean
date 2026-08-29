import Hilbert16.Hypergeometric.CartesianRank
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

namespace Hilbert16

open Finset
open Spikes

/-! ### Convergence and analytic realization of Paper Eq. (3.12) -/

/-- An absolute majorant obtained by evaluating the Borel `₂F₁` series at radius `1/2`. -/
noncomputable def borelMajorant (alpha : ℝ) (m : ℕ) : ℝ :=
  |formalTwoFZeroCoefficient alpha m| / (m.factorial : ℝ) * (1 / 2 : ℝ) ^ m

theorem borelMajorant_summable {alpha : ℝ} (halpha_pos : 0 < alpha)
    (halpha_one : alpha < 1) : Summable (borelMajorant alpha) := by
  let p := ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1
  have hradius : p.radius = 1 := by
    simpa [p] using gaussBorelSeries_radius_eq_one halpha_pos halpha_one
  let r : NNReal := ⟨1 / 2, by norm_num⟩
  have hr : (r : ENNReal) < p.radius := by
    rw [hradius]
    exact_mod_cast (show (1 / 2 : ℝ) < 1 by norm_num)
  have hs := p.summable_norm_mul_pow hr
  simp only [p, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_norm, ← formalTwoFZeroCoefficient_borel,
    Real.norm_eq_abs, norm_div] at hs
  have hrcoe : (r : ℝ) = 1 / 2 := rfl
  rw [hrcoe] at hs
  have hfac : ∀ n : ℕ, |(n.factorial : ℝ)| = (n.factorial : ℝ) := fun n => by
    rw [abs_of_nonneg]
    positivity
  simp_rw [hfac, one_div, inv_pow] at hs
  exact hs.congr fun n => by simp [borelMajorant, one_div, inv_pow]

theorem borelMajorant_nonneg (alpha : ℝ) (m : ℕ) :
    0 ≤ borelMajorant alpha m := by
  unfold borelMajorant
  positivity

/-- The factorial denominator in Eq. (3.12) dominates every antidiagonal product denominator. -/
theorem factorial_mul_factorial_le_factorial_succ (p m : ℕ) (hp : p ≤ m) :
    (p.factorial : ℝ) * ((m - p).factorial : ℝ) ≤ ((m + 1).factorial : ℝ) := by
  have hdiv : p.factorial * (m - p).factorial ∣ m.factorial :=
    Nat.factorial_mul_factorial_dvd_factorial hp
  have hle : p.factorial * (m - p).factorial ≤ m.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos m) hdiv
  have hle' : p.factorial * (m - p).factorial ≤ (m + 1).factorial :=
    hle.trans (Nat.factorial_le (Nat.le_succ m))
  exact_mod_cast hle'

/-- The Cauchy product of the two Borel majorants. -/
noncomputable def analyticKernelMajorant (alpha beta : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (m + 1),
    borelMajorant alpha p * borelMajorant beta (m - p)

theorem analyticKernelMajorant_summable {alpha beta : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1) :
    Summable (analyticKernelMajorant alpha beta) := by
  have ha := borelMajorant_summable halpha_pos halpha_one
  have hb := borelMajorant_summable hbeta_pos hbeta_one
  have ha_norm : Summable (fun m => ‖borelMajorant alpha m‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (borelMajorant_nonneg alpha _)] using ha
  have hb_norm : Summable (fun m => ‖borelMajorant beta m‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (borelMajorant_nonneg beta _)] using hb
  change Summable (fun m => ∑ p ∈ Finset.range (m + 1),
    borelMajorant alpha p * borelMajorant beta (m - p))
  exact summable_sum_mul_range_of_summable_norm' ha_norm ha hb_norm hb

theorem abs_inv_pow_le_one {lambda : ℝ} (hlambda : 1 ≤ lambda) (m : ℕ) :
    |lambda⁻¹| ^ m ≤ 1 := by
  apply pow_le_one₀ (abs_nonneg _)
  rw [abs_inv, abs_of_nonneg (le_trans zero_le_one hlambda)]
  exact inv_le_one_of_one_le₀ hlambda

theorem analyticKernelTerm_le_majorant {alpha beta lambda : ℝ}
    (hlambda : 1 ≤ lambda) (m p : ℕ) (hp : p ≤ m) :
    ‖((2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) *
        (formalTwoFZeroCoefficient alpha p *
          formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p))‖ *
        (1 / 4 : ℝ) ^ m ≤
      borelMajorant alpha p * borelMajorant beta (m - p) := by
  have hfac := factorial_mul_factorial_le_factorial_succ p m hp
  have hinvfac : (((m + 1).factorial : ℝ))⁻¹ ≤
      (((p.factorial : ℝ) * ((m - p).factorial : ℝ)))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hfac
  have hpow := abs_inv_pow_le_one hlambda (m - p)
  have hadd : p + (m - p) = m := Nat.add_sub_of_le hp
  have hhalf : (1 / 2 : ℝ) ^ m =
      (1 / 2 : ℝ) ^ p * (1 / 2 : ℝ) ^ (m - p) := by
    rw [← pow_add, hadd]
  have hscale : (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  have hdenom : (1 / 2 : ℝ) ^ m / ((m + 1).factorial : ℝ) ≤
      (1 / 2 : ℝ) ^ m /
        ((p.factorial : ℝ) * ((m - p).factorial : ℝ)) := by
    simp only [div_eq_mul_inv]
    gcongr
  simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
    abs_of_nonneg (show 0 ≤ ((m + 1).factorial : ℝ) by positivity),
    borelMajorant]
  calc
    ((2 : ℝ) ^ m / ((m + 1).factorial : ℝ) *
          (|formalTwoFZeroCoefficient alpha p| *
            |formalTwoFZeroCoefficient beta (m - p)| * |lambda⁻¹| ^ (m - p))) *
        (1 / 4 : ℝ) ^ m =
      (|formalTwoFZeroCoefficient alpha p| *
          |formalTwoFZeroCoefficient beta (m - p)| * |lambda⁻¹| ^ (m - p)) *
        ((1 / 2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← hscale]
          ring
    _ ≤ (|formalTwoFZeroCoefficient alpha p| *
          |formalTwoFZeroCoefficient beta (m - p)|) *
        ((1 / 2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) := by
          have hfirst :
              |formalTwoFZeroCoefficient alpha p| *
                  |formalTwoFZeroCoefficient beta (m - p)| * |lambda⁻¹| ^ (m - p) ≤
                |formalTwoFZeroCoefficient alpha p| *
                  |formalTwoFZeroCoefficient beta (m - p)| := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hpow
                (mul_nonneg
                  (abs_nonneg (formalTwoFZeroCoefficient alpha p))
                  (abs_nonneg (formalTwoFZeroCoefficient beta (m - p)))))
          exact mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ ≤ (|formalTwoFZeroCoefficient alpha p| *
          |formalTwoFZeroCoefficient beta (m - p)|) *
        ((1 / 2 : ℝ) ^ m /
          ((p.factorial : ℝ) * ((m - p).factorial : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hdenom
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (|formalTwoFZeroCoefficient alpha p| / (p.factorial : ℝ) *
          (1 / 2 : ℝ) ^ p) *
        (|formalTwoFZeroCoefficient beta (m - p)| /
          ((m - p).factorial : ℝ) * (1 / 2 : ℝ) ^ (m - p)) := by
          rw [hhalf]
          field_simp

theorem analyticKernelTaylorCoefficient_quarter_majorized
    {alpha beta lambda : ℝ} (hlambda : 1 ≤ lambda) (m : ℕ) :
    ‖analyticKernelTaylorCoefficient alpha beta lambda m‖ * (1 / 4 : ℝ) ^ m ≤
      analyticKernelMajorant alpha beta m := by
  rw [analyticKernelTaylorCoefficient, formalProductRow, Finset.mul_sum]
  calc
    ‖∑ p ∈ Finset.range (m + 1),
        ((2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) *
          (formalTwoFZeroCoefficient alpha p *
            formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p))‖ *
        (1 / 4 : ℝ) ^ m ≤
      (∑ p ∈ Finset.range (m + 1),
        ‖((2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) *
          (formalTwoFZeroCoefficient alpha p *
            formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p))‖) *
        (1 / 4 : ℝ) ^ m := by
          gcongr
          exact norm_sum_le _ _
    _ = ∑ p ∈ Finset.range (m + 1),
        ‖((2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) *
          (formalTwoFZeroCoefficient alpha p *
            formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p))‖ *
          (1 / 4 : ℝ) ^ m := by
            rw [Finset.sum_mul]
    _ ≤ analyticKernelMajorant alpha beta m := by
      unfold analyticKernelMajorant
      apply Finset.sum_le_sum
      intro p hp
      apply analyticKernelTerm_le_majorant hlambda m p
      have hp' := Finset.mem_range.mp hp
      omega

theorem analyticKernelTaylorCoefficient_summable_quarter
    {alpha beta lambda : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) :
    Summable (fun m =>
      ‖analyticKernelTaylorCoefficient alpha beta lambda m‖ * (1 / 4 : ℝ) ^ m) := by
  exact (analyticKernelMajorant_summable halpha_pos halpha_one hbeta_pos hbeta_one).of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (by positivity))
    (analyticKernelTaylorCoefficient_quarter_majorized hlambda)

/-- The scalar formal power series whose coefficients are exactly Paper Eq. (3.12). -/
noncomputable def analyticKernelSeries (alpha beta lambda : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (analyticKernelTaylorCoefficient alpha beta lambda)

@[simp]
theorem analyticKernelSeries_coeff (alpha beta lambda : ℝ) (m : ℕ) :
    (analyticKernelSeries alpha beta lambda).coeff m =
      analyticKernelTaylorCoefficient alpha beta lambda m := by
  simp [analyticKernelSeries, FormalMultilinearSeries.coeff_ofScalars]

theorem analyticKernelSeries_radius_pos {alpha beta lambda : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) :
    0 < (analyticKernelSeries alpha beta lambda).radius := by
  let r : NNReal := ⟨1 / 4, by norm_num⟩
  have hs : Summable (fun m =>
      ‖analyticKernelSeries alpha beta lambda m‖ * (r : ℝ) ^ m) := by
    have hraw := analyticKernelTaylorCoefficient_summable_quarter
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda
    have hrcoe : (r : ℝ) = 1 / 4 := rfl
    rw [hrcoe]
    simpa [analyticKernelSeries, FormalMultilinearSeries.ofScalars_norm] using hraw
  have hrle : (r : ENNReal) ≤ (analyticKernelSeries alpha beta lambda).radius :=
    (analyticKernelSeries alpha beta lambda).le_radius_of_summable hs
  exact lt_of_lt_of_le (by
    exact_mod_cast (show (0 : ℝ) < 1 / 4 by norm_num)) hrle

/-- The convergent analytic kernel in Paper Eq. (3.12), defined as the sum of its certified
positive-radius Taylor series. -/
noncomputable def analyticKernel (alpha beta lambda h : ℝ) : ℝ :=
  (analyticKernelSeries alpha beta lambda).sum h

theorem analyticKernel_hasFPowerSeriesAt {alpha beta lambda : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) :
    HasFPowerSeriesAt (analyticKernel alpha beta lambda)
      (analyticKernelSeries alpha beta lambda) 0 := by
  exact ((analyticKernelSeries alpha beta lambda).hasFPowerSeriesOnBall
    (analyticKernelSeries_radius_pos halpha_pos halpha_one hbeta_pos hbeta_one hlambda)).hasFPowerSeriesAt

theorem analyticKernel_analyticAt {alpha beta lambda : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) :
    AnalyticAt ℝ (analyticKernel alpha beta lambda) 0 :=
  (analyticKernel_hasFPowerSeriesAt halpha_pos halpha_one hbeta_pos hbeta_one hlambda).analyticAt

/-- The explicit quarter-radius majorant gives the concrete local `C¹`
domain used by the finite hierarchy. -/
theorem analyticKernel_contDiffOn_Ioo_quarter {alpha beta lambda : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) :
    ContDiffOn ℝ 1 (analyticKernel alpha beta lambda) (Set.Ioo 0 (1 / 4)) := by
  let r : NNReal := ⟨1 / 4, by norm_num⟩
  have hs : Summable (fun m =>
      ‖analyticKernelSeries alpha beta lambda m‖ * (r : ℝ) ^ m) := by
    have hraw := analyticKernelTaylorCoefficient_summable_quarter
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda
    have hrcoe : (r : ℝ) = 1 / 4 := rfl
    rw [hrcoe]
    simpa [analyticKernelSeries, FormalMultilinearSeries.ofScalars_norm] using hraw
  have hrle : (r : ENNReal) ≤ (analyticKernelSeries alpha beta lambda).radius :=
    (analyticKernelSeries alpha beta lambda).le_radius_of_summable hs
  have hball := (analyticKernelSeries alpha beta lambda).hasFPowerSeriesOnBall
    (analyticKernelSeries_radius_pos
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda)
  apply AnalyticOnNhd.contDiffOn_of_completeSpace
  intro h hh
  apply hball.analyticAt_of_mem
  have hhr : ‖h‖ₑ < (r : ENNReal) := by
    rw [← ofReal_norm, Real.norm_of_nonneg hh.1.le]
    rw [ENNReal.ofReal_lt_coe_iff hh.1.le]
    exact hh.2
  simpa [Metric.mem_eball] using hhr.trans_le hrle

theorem coeff_finset_sum_smul
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p : ι → FormalMultilinearSeries ℝ ℝ ℝ) (m : ℕ) :
    (∑ i ∈ s, c i • p i).coeff m = ∑ i ∈ s, c i * (p i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (0 : ℝ) = 0
      rfl
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change c i * (p i).coeff m + (∑ x ∈ s, c x • p x).coeff m =
        c i * (p i).coeff m + ∑ x ∈ s, c x * (p x).coeff m
      rw [ih]

/-- Linear independence of scalar Taylor coefficient sequences lifts to linear independence of
the represented analytic functions. -/
theorem linearIndependent_of_hasFPowerSeriesAt_coeff
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (p : ι → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ i, HasFPowerSeriesAt (f i) (p i) 0)
    (hcoeff : LinearIndependent ℝ (fun i => fun m => (p i).coeff m)) :
    LinearIndependent ℝ f := by
  classical
  rw [Fintype.linearIndependent_iff] at hcoeff ⊢
  intro c hrelation
  apply hcoeff c
  have hseries : HasFPowerSeriesAt
      (∑ i, c i • f i) (∑ i, c i • p i) 0 := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty =>
        have hz :=
          (hasFPowerSeriesAt_const (𝕜 := ℝ) (E := ℝ) (c := (0 : ℝ)) (e := (0 : ℝ)))
        convert hz using 1
        · funext x
          rfl
        · rw [Finset.sum_empty, constFormalMultilinearSeries_zero]
    | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact (hp i).const_smul.add ih
  rw [hrelation] at hseries
  have hzero : (∑ i, c i • p i) = 0 := hseries.eq_zero
  funext m
  have hm := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q.coeff m) hzero
  rw [show (∑ i, c i • p i) = ∑ i ∈ (Finset.univ : Finset ι), c i • p i by simp,
    coeff_finset_sum_smul] at hm
  change (∑ i ∈ (Finset.univ : Finset ι), c i * (p i).coeff m) = 0 at hm
  rw [Fintype.sum_apply]
  change (∑ i, c i * (p i).coeff m) = 0
  exact hm

/-- **Paper Proposition 5.2, convergent-germ conclusion.**  For sufficiently large anisotropy,
the actual positive-radius analytic kernels form a linearly independent Cartesian family. -/
theorem anisotropicAnalyticKernelRank
    {d e : ℕ} (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_one : ∀ j, beta j < 1)
    (hbeta_injective : Function.Injective beta) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      LinearIndependent ℝ
        (fun ij : Fin d × Fin e =>
          analyticKernel (alpha ij.1) (beta ij.2) lambda) := by
  obtain ⟨Lambda, hLambda_one, hLambda⟩ :=
    anisotropicAnalyticKernelTaylorRank alpha beta
      halpha_pos halpha_one halpha_injective
      hbeta_pos hbeta_one hbeta_injective
  refine ⟨Lambda, hLambda_one, fun lambda hlambda => ?_⟩
  have hlambda_one : 1 ≤ lambda :=
    hLambda_one.trans (le_of_lt hlambda)
  apply linearIndependent_of_hasFPowerSeriesAt_coeff
    (fun ij : Fin d × Fin e =>
      analyticKernel (alpha ij.1) (beta ij.2) lambda)
    (fun ij : Fin d × Fin e =>
      analyticKernelSeries (alpha ij.1) (beta ij.2) lambda)
  · intro ij
    exact analyticKernel_hasFPowerSeriesAt
      (halpha_pos ij.1) (halpha_one ij.1)
      (hbeta_pos ij.2) (hbeta_one ij.2) hlambda_one
  · simpa only [analyticKernelSeries_coeff] using hLambda lambda hlambda

/-- For fixed construction size, all finitely many block-dependent analytic-kernel families share
one anisotropy threshold, as used immediately after Paper Proposition 5.2. -/
theorem finiteBlockCommonAnisotropicKernelRank
    {κ : Type*} [Fintype κ] (d e : κ → ℕ)
    (alpha : ∀ k, Fin (d k) → ℝ) (beta : ∀ k, Fin (e k) → ℝ)
    (halpha_pos : ∀ k i, 0 < alpha k i)
    (halpha_one : ∀ k i, alpha k i < 1)
    (halpha_injective : ∀ k, Function.Injective (alpha k))
    (hbeta_pos : ∀ k j, 0 < beta k j)
    (hbeta_one : ∀ k j, beta k j < 1)
    (hbeta_injective : ∀ k, Function.Injective (beta k)) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda, ∀ k,
      LinearIndependent ℝ
        (fun ij : Fin (d k) × Fin (e k) =>
          analyticKernel (alpha k ij.1) (beta k ij.2) lambda) := by
  obtain ⟨Lambda, hLambda_one, hLambda⟩ :=
    finiteBlockCommonAnisotropicTaylorRank d e alpha beta
      halpha_pos halpha_one halpha_injective
      hbeta_pos hbeta_one hbeta_injective
  refine ⟨Lambda, hLambda_one, fun lambda hlambda k => ?_⟩
  have hlambda_one : 1 ≤ lambda :=
    hLambda_one.trans (le_of_lt hlambda)
  apply linearIndependent_of_hasFPowerSeriesAt_coeff
    (fun ij : Fin (d k) × Fin (e k) =>
      analyticKernel (alpha k ij.1) (beta k ij.2) lambda)
    (fun ij : Fin (d k) × Fin (e k) =>
      analyticKernelSeries (alpha k ij.1) (beta k ij.2) lambda)
  · intro ij
    exact analyticKernel_hasFPowerSeriesAt
      (halpha_pos k ij.1) (halpha_one k ij.1)
      (hbeta_pos k ij.2) (hbeta_one k ij.2) hlambda_one
  · simpa only [analyticKernelSeries_coeff] using hLambda lambda hlambda k

end Hilbert16
