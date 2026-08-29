import Hilbert16.Hypergeometric.AnalyticKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Hilbert16

open Finset MeasureTheory
open Spikes

/-! ### Exact integration of the convergent cosine--arcsine mode -/

/-- The actual normalized disk integral before identifying it with the analytic kernel. -/
noncomputable def normalizedModeDiskIntegral
    (alpha beta lambda h : ℝ) : ℝ :=
  (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
    Real.cos (alpha * Real.arcsin z.2) *
      Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) /
    (2 * Real.pi * h)

theorem modeTaylorAntidiagonal_integrableOn
    (alpha beta lambda : ℝ) (m : ℕ) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (modeTaylorAntidiagonal alpha beta lambda m)
      (cartesianEnergyDisk h) := by
  unfold modeTaylorAntidiagonal
  apply integrable_finsetSum
  intro p hp
  exact (monomial_integrableOn_cartesianEnergyDisk p (m - p) hh).const_mul
    (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
      (lambda⁻¹) ^ (m - p))

private theorem modeTaylorTerm_integral_norm_le
    {alpha beta lambda h : ℝ} (m p : ℕ) (hp : p ≤ m)
    (hh : 0 < h) (hhq : h ≤ 1 / 4) (hlambda : 1 ≤ lambda) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      ‖(cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
          (lambda⁻¹) ^ (m - p)) *
        (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))‖) ≤
      (2 * Real.pi * h) *
        (borelMajorant alpha p * borelMajorant beta (m - p)) := by
  let c := cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
    (lambda⁻¹) ^ (m - p)
  let T := ((2 : ℝ) ^ m / ((m + 1).factorial : ℝ)) *
    (formalTwoFZeroCoefficient alpha p *
      formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p))
  have hCpos : 0 < 2 * Real.pi * h := by positivity
  have hnormalized := normalizedModeMonomialIntegral_eq_taylorTerm
    alpha beta lambda p (m - p) hh
  rw [Nat.add_sub_of_le hp] at hnormalized
  have hI :
      (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        c * (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))) =
        T * h ^ m * (2 * Real.pi * h) := by
    exact (div_eq_iff hCpos.ne').mp hnormalized
  have hT : ‖T * h ^ m‖ ≤
      borelMajorant alpha p * borelMajorant beta (m - p) := by
    calc
      ‖T * h ^ m‖ = ‖T‖ * h ^ m := by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg hh.le]
      _ ≤ ‖T‖ * (1 / 4 : ℝ) ^ m := by
        gcongr
      _ ≤ borelMajorant alpha p * borelMajorant beta (m - p) := by
        exact analyticKernelTerm_le_majorant hlambda m p hp
  rw [integral_norm_const_evenMonomial_eq_norm_integral c p (m - p) hh, hI,
    norm_mul, Real.norm_of_nonneg hCpos.le]
  nlinarith [hT]

theorem integral_norm_modeTaylorAntidiagonal_le
    {alpha beta lambda h : ℝ} (m : ℕ)
    (hh : 0 < h) (hhq : h ≤ 1 / 4) (hlambda : 1 ≤ lambda) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      ‖modeTaylorAntidiagonal alpha beta lambda m z‖) ≤
      (2 * Real.pi * h) * analyticKernelMajorant alpha beta m := by
  have htermInt : ∀ p ∈ Finset.range (m + 1),
      IntegrableOn (fun z : ℝ × ℝ =>
        ‖(cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
            (lambda⁻¹) ^ (m - p)) *
          (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))‖)
        (cartesianEnergyDisk h) := by
    intro p hp
    exact ((monomial_integrableOn_cartesianEnergyDisk p (m - p) hh).const_mul
      (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
        (lambda⁻¹) ^ (m - p))).norm
  have hsumInt := integrable_finsetSum (Finset.range (m + 1)) htermInt
  have hmodeNormInt := (modeTaylorAntidiagonal_integrableOn
    alpha beta lambda m hh).norm
  calc
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        ‖modeTaylorAntidiagonal alpha beta lambda m z‖) ≤
      ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        ∑ p ∈ Finset.range (m + 1),
          ‖(cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
              (lambda⁻¹) ^ (m - p)) *
            (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))‖ := by
          apply integral_mono hmodeNormInt hsumInt
          intro z
          unfold modeTaylorAntidiagonal
          exact norm_sum_le _ _
    _ = ∑ p ∈ Finset.range (m + 1),
        ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
          ‖(cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
              (lambda⁻¹) ^ (m - p)) *
            (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))‖ := by
          rw [integral_finsetSum]
          exact htermInt
    _ ≤ ∑ p ∈ Finset.range (m + 1),
        (2 * Real.pi * h) *
          (borelMajorant alpha p * borelMajorant beta (m - p)) := by
          apply Finset.sum_le_sum
          intro p hp
          exact modeTaylorTerm_integral_norm_le m p
            (Finset.mem_range_succ_iff.mp hp) hh hhq hlambda
    _ = (2 * Real.pi * h) * analyticKernelMajorant alpha beta m := by
          rw [analyticKernelMajorant, Finset.mul_sum]

theorem summable_integral_norm_modeTaylorAntidiagonal
    {alpha beta lambda h : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hh : 0 < h) (hhq : h ≤ 1 / 4) (hlambda : 1 ≤ lambda) :
    Summable (fun m =>
      ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        ‖modeTaylorAntidiagonal alpha beta lambda m z‖) := by
  have hmajorant := (analyticKernelMajorant_summable
    halpha_pos halpha_one hbeta_pos hbeta_one).mul_left (2 * Real.pi * h)
  exact hmajorant.of_nonneg_of_le
    (fun m => integral_nonneg (fun _ => norm_nonneg _))
    (fun m => integral_norm_modeTaylorAntidiagonal_le m hh hhq hlambda)

/-- Inside the certified radius, the analytic kernel is the sum of its explicit Taylor rows. -/
theorem analyticKernel_hasSum_taylor
    {alpha beta lambda h : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhq : h < 1 / 4) :
    HasSum (fun m => analyticKernelTaylorCoefficient alpha beta lambda m * h ^ m)
      (analyticKernel alpha beta lambda h) := by
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
  have hhr : ‖h‖ₑ < (r : ENNReal) := by
    rw [← ofReal_norm, Real.norm_of_nonneg hh]
    rw [ENNReal.ofReal_lt_coe_iff hh]
    exact hhq
  have H := (analyticKernelSeries alpha beta lambda).hasSum
    (show h ∈ Metric.eball (0 : ℝ) (analyticKernelSeries alpha beta lambda).radius by
      simpa [Metric.mem_eball] using hhr.trans_le hrle)
  simpa [analyticKernel, analyticKernelSeries,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using H

/-- Paper Eq. (3.12): the actual normalized disk integral of the two cosine--arcsine modes
is exactly the convergent analytic kernel. -/
theorem normalizedModeDiskIntegral_eq_analyticKernel
    {alpha beta lambda h : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    normalizedModeDiskIntegral alpha beta lambda h =
      analyticKernel alpha beta lambda h := by
  let F : ℕ → (ℝ × ℝ) → ℝ :=
    fun m => modeTaylorAntidiagonal alpha beta lambda m
  have hFint : ∀ m, IntegrableOn (F m) (cartesianEnergyDisk h) := by
    intro m
    exact modeTaylorAntidiagonal_integrableOn alpha beta lambda m hh
  have hFnorm : Summable (fun m =>
      ∫ z : ℝ × ℝ in cartesianEnergyDisk h, ‖F m z‖) := by
    exact summable_integral_norm_modeTaylorAntidiagonal
      halpha_pos halpha_one hbeta_pos hbeta_one hh hhq.le hlambda
  have hactualEq :
      (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        Real.cos (alpha * Real.arcsin z.2) *
          Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) =
      ∫ z : ℝ × ℝ in cartesianEnergyDisk h, ∑' m, F m z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_cartesianEnergyDisk h)] with z hz
    exact (modeTaylorAntidiagonal_hasSum_on_disk z
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda (by linarith) hz).tsum_eq.symm
  have hIntegralSum := hasSum_integral_of_summable_integral_norm hFint hFnorm
  rw [← hactualEq] at hIntegralSum
  have hNormalizedIntegral := hIntegralSum.div_const (2 * Real.pi * h)
  have hKernel := analyticKernel_hasSum_taylor
    halpha_pos halpha_one hbeta_pos hbeta_one hlambda hh.le hhq
  have hNormalizedKernel : HasSum (fun m =>
      (∫ z : ℝ × ℝ in cartesianEnergyDisk h, F m z) /
        (2 * Real.pi * h)) (analyticKernel alpha beta lambda h) := by
    refine HasSum.congr_fun hKernel ?_
    intro m
    simpa only [F, analyticKernelTaylorCoefficient] using
      normalizedModeAntidiagonalIntegral alpha beta lambda m hh
  exact hNormalizedIntegral.unique hNormalizedKernel

end Hilbert16
