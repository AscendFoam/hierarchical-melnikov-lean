import Hilbert16.Spikes.BorelGauss
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Nat Polynomial MeasureTheory Filter intervalIntegral Set

namespace Hilbert16.Spikes

theorem betaMobius_interval_identity {u x : ℝ} (_hu : 0 < u) (hx : 0 < x) :
    x ^ u * ∫ t : ℝ in 0..1,
      t ^ (u - 1) * (1 - t) ^ (-u) * (1 + x * t) ^ (u - 1) =
    (x / (1 + x)) ^ u * ∫ y : ℝ in 0..1,
      y ^ (u - 1) * (1 - y) ^ (-u) *
        (1 - (x / (1 + x)) * y) ^ (-u) := by
  let d : ℝ → ℝ := fun y => 1 + x * (1 - y)
  let m : ℝ → ℝ := fun y => y / d y
  let m' : ℝ → ℝ := fun y => (1 + x) / (d y) ^ 2
  let g : ℝ → ℝ := fun t =>
    t ^ (u - 1) * (1 - t) ^ (-u) * (1 + x * t) ^ (u - 1)
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hd_pos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, 0 < d y := by
    intro y hy
    rw [Set.uIcc_of_le h01] at hy
    dsimp [d]
    have hmul : 0 ≤ x * (1 - y) := mul_nonneg hx.le (sub_nonneg.mpr hy.2)
    linarith
  have hm_cont : ContinuousOn m (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_id
      (continuous_const.add (continuous_const.mul
        (continuous_const.sub continuous_id))).continuousOn
    intro y hy
    exact (hd_pos y hy).ne'
  have hm_deriv : ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt m (m' y) y := by
    intro y hy
    have hyd : d y ≠ 0 := by
      apply (hd_pos y ?_).ne'
      rw [Set.uIcc_of_le h01]
      norm_num at hy
      exact ⟨hy.1.le, hy.2.le⟩
    dsimp [m, m', d]
    have hden : HasDerivAt (fun z : ℝ => 1 + x * (1 - z)) (-x) y := by
      have hden0 := (hasDerivAt_const y 1).add
        ((hasDerivAt_const y x).mul
          ((hasDerivAt_const y 1).sub (hasDerivAt_id y)))
      change HasDerivAt (fun z : ℝ => 1 + x * (1 - z))
        (0 + (0 * (1 - y) + x * (0 - 1))) y at hden0
      apply hden0.congr_deriv
      ring
    have hraw := (hasDerivAt_id y).div hden hyd
    change HasDerivAt (fun z : ℝ => z / (1 + x * (1 - z)))
      ((1 * (1 + x * (1 - y)) - y * (-x)) / (1 + x * (1 - y)) ^ 2) y at hraw
    apply hraw.congr_deriv
    congr 1
    ring
  have hm'_nonneg : ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      0 ≤ m' y := by
    intro y hy
    dsimp [m']
    positivity
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := m) (f' := m') (g := g)
    hm_cont hm_deriv hm'_nonneg
  have hm0 : m 0 = 0 := by simp [m]
  have hm1 : m 1 = 1 := by simp [m, d]
  rw [hm0, hm1] at hsubst
  rw [← hsubst]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ), Measure.ae_ne volume (1 : ℝ)] with y hy0 hy1 hy
  have hypos : 0 < y := by
    rw [Set.uIoc_of_le h01] at hy
    exact hy.1
  have hylt : y < 1 := by
    rw [Set.uIoc_of_le h01] at hy
    exact lt_of_le_of_ne hy.2 hy1
  have hyd : 0 < d y := hd_pos y (by
    rw [Set.uIcc_of_le h01]
    exact ⟨hypos.le, hylt.le⟩)
  have hxp : 0 < 1 + x := by linarith
  have hq : 0 < x / (1 + x) := div_pos hx hxp
  have hq1 : x / (1 + x) < 1 := (div_lt_one hxp).mpr (by linarith)
  dsimp [g, m, m', d]
  have hD : 0 < 1 + x * (1 - y) := by simpa [d] using hyd
  have hone_sub : 0 < 1 - y := sub_pos.mpr hylt
  have hbase1 :
      1 - y / (1 + x * (1 - y)) =
        (1 + x) * (1 - y) / (1 + x * (1 - y)) := by
    field_simp [hD.ne']
    ring
  have hbase2 :
      1 + x * (y / (1 + x * (1 - y))) =
        (1 + x) / (1 + x * (1 - y)) := by
    field_simp [hD.ne']
    ring
  have hbase3 :
      1 - x / (1 + x) * y =
        (1 + x * (1 - y)) / (1 + x) := by
    field_simp [hxp.ne']
    ring
  rw [hbase1, hbase2, hbase3]
  rw [Real.div_rpow hypos.le hD.le,
    Real.div_rpow (mul_pos hxp hone_sub).le hD.le,
    Real.mul_rpow hxp.le hone_sub.le,
    Real.div_rpow hxp.le hD.le,
    Real.div_rpow hx.le hxp.le,
    Real.div_rpow hD.le hxp.le]
  rw [Real.rpow_sub hD u 1, Real.rpow_one,
    Real.rpow_sub hxp u 1, Real.rpow_one,
    Real.rpow_neg hD.le u, Real.rpow_neg hxp.le u]
  field_simp [hD.ne', hxp.ne', (Real.rpow_pos_of_pos hD u).ne',
    (Real.rpow_pos_of_pos hxp u).ne']

theorem betaMobius_expectation_identity {u x : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hx : 0 < x) :
    x ^ u * ∫ t : ℝ, (1 + x * t) ^ (u - 1)
        ∂ProbabilityTheory.betaMeasure u (1 - u) =
      (x / (1 + x)) ^ u *
        ∫ y : ℝ, (1 - (x / (1 + x)) * y) ^ (-u)
          ∂ProbabilityTheory.betaMeasure u (1 - u) := by
  rw [betaMeasure_integral_eq_intervalIntegral hu (sub_pos.mpr hu1),
    betaMeasure_integral_eq_intervalIntegral hu (sub_pos.mpr hu1)]
  have h := congrArg
    (fun z : ℝ => (ProbabilityTheory.beta u (1 - u))⁻¹ * z)
    (betaMobius_interval_identity hu hx)
  convert h using 1 <;> ring_nf <;> simp [mul_comm]

theorem gauss_mobius_tendsto_atTop :
    Tendsto (fun x : ℝ => x / (1 + x)) atTop (nhds 1) := by
  have hden : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hinv : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (nhds 0) :=
    hden.inv_tendsto_atTop
  have hlim : Tendsto (fun x : ℝ => (1 : ℝ) - (1 + x)⁻¹)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hinv)
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

theorem betaMobius_kernel_tendsto {u : ℝ} (hu : 0 < u) (hu2 : 2 * u < 1) :
    Tendsto
      (fun x : ℝ => ∫ y : ℝ,
        (1 - (x / (1 + x)) * y) ^ (-u)
          ∂ProbabilityTheory.betaMeasure u (1 - u))
      atTop
      (nhds (ProbabilityTheory.beta u (1 - 2 * u) /
        ProbabilityTheory.beta u (1 - u))) := by
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hu1 : u < 1 := by linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (sub_pos.mpr hu1)
  have hq_tendsto := gauss_mobius_tendsto_atTop
  have hDCT :
      Tendsto
        (fun x : ℝ => ∫ y : ℝ, (1 - (x / (1 + x)) * y) ^ (-u) ∂μ)
        atTop (nhds (∫ y : ℝ, (1 - y) ^ (-u) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => (1 - y) ^ (-u))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hxp : 0 < 1 + x := by linarith
      have hq : 0 < x / (1 + x) := div_pos hx hxp
      have hq1 : x / (1 + x) < 1 := (div_lt_one hxp).mpr (by linarith)
      have hcont : Continuous
          (fun y : ℝ => (1 - (x / (1 + x)) * min y 1) ^ (-u)) := by
        apply Continuous.rpow_const
          (continuous_const.sub (continuous_const.mul (continuous_id.min continuous_const)))
        intro y
        left
        have hmul : (x / (1 + x)) * min y 1 ≤ x / (1 + x) :=
          by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (min_le_right y 1) hq.le
        have hbase : 0 < 1 - (x / (1 + x)) * min y 1 := by linarith
        change 1 - (x / (1 + x)) * min y 1 ≠ 0
        exact hbase.ne'
      refine hcont.aestronglyMeasurable.congr ?_
      filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with y hy
      rw [min_eq_left hy.2.le]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hxp : 0 < 1 + x := by linarith
      have hq : 0 < x / (1 + x) := div_pos hx hxp
      have hq1 : x / (1 + x) < 1 := (div_lt_one hxp).mpr (by linarith)
      filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with y hy
      have hone : 0 < 1 - y := sub_pos.mpr hy.2
      have hmul : (x / (1 + x)) * y < y :=
        mul_lt_of_lt_one_left hy.1 hq1
      have hbase : 0 < 1 - (x / (1 + x)) * y := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hbase.le (-u))]
      exact Real.rpow_le_rpow_of_nonpos hone (by linarith) (by linarith)
    · dsimp [μ]
      exact betaMeasure_one_sub_rpow_integrable hu (sub_pos.mpr hu1)
        (by linarith : 0 < (1 - u) + (-u))
    · filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with y hy
      have hbase : 1 - y ≠ 0 := (sub_pos.mpr hy.2).ne'
      simpa only [one_mul] using
        (tendsto_const_nhds.sub (hq_tendsto.mul_const y)).rpow_const
          (.inl (by simpa only [one_mul] using hbase))
  convert hDCT using 1
  dsimp [μ]
  rw [betaMeasure_one_sub_rpow_moment hu (sub_pos.mpr hu1)
    (by linarith : 0 < (1 - u) + (-u))]
  congr 2 <;> ring

theorem betaMobius_weighted_kernel_tendsto {u : ℝ} (hu : 0 < u) (hu2 : 2 * u < 1) :
    Tendsto
      (fun x : ℝ => x ^ u *
        ∫ t : ℝ, (1 + x * t) ^ (u - 1)
          ∂ProbabilityTheory.betaMeasure u (1 - u))
      atTop
      (nhds (ProbabilityTheory.beta u (1 - 2 * u) /
        ProbabilityTheory.beta u (1 - u))) := by
  have hu1 : u < 1 := by linarith
  have hqpow : Tendsto (fun x : ℝ => (x / (1 + x)) ^ u) atTop (nhds 1) := by
    simpa using gauss_mobius_tendsto_atTop.rpow_const (.inl one_ne_zero)
  have hprod := hqpow.mul (betaMobius_kernel_tendsto hu hu2)
  have hprod' : Tendsto
      (fun x : ℝ => (x / (1 + x)) ^ u *
        ∫ t : ℝ, (1 - (x / (1 + x)) * t) ^ (-u)
          ∂ProbabilityTheory.betaMeasure u (1 - u))
      atTop
      (nhds (ProbabilityTheory.beta u (1 - 2 * u) /
        ProbabilityTheory.beta u (1 - u))) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (betaMobius_expectation_identity hu hu1 hx).symm

theorem gaussBetaDecayRatio_eq_two_connectionB {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    ProbabilityTheory.beta (alpha / 2) (1 - alpha) /
        ProbabilityTheory.beta (alpha / 2) (1 - alpha / 2) =
      2 * gaussConnectionB alpha := by
  have hrecα := Real.Gamma_add_one (s := -alpha) (by linarith : -alpha ≠ 0)
  have hrecu := Real.Gamma_add_one (s := -alpha / 2) (by linarith : -alpha / 2 ≠ 0)
  have hGnegα : Real.Gamma (-alpha) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hrecα
    have : Real.Gamma (-alpha + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    exact this hrecα
  have hGnegu : Real.Gamma (-alpha / 2) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hrecu
    have : Real.Gamma (-alpha / 2 + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith)).ne'
    exact this hrecu
  unfold ProbabilityTheory.beta gaussConnectionB
  rw [show alpha / 2 + (1 - alpha) = 1 - alpha / 2 by ring,
    show alpha / 2 + (1 - alpha / 2) = 1 by ring,
    Real.Gamma_one]
  rw [show 1 - alpha = -alpha + 1 by ring,
    show 1 - alpha / 2 = -alpha / 2 + 1 by ring,
    hrecα, hrecu]
  field_simp [hGnegα, hGnegu,
    (Real.Gamma_pos_of_pos (by linarith : 0 < alpha / 2)).ne']

theorem gaussEulerNegativeKernel_integrable {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    Integrable (fun t : ℝ => (1 + x * t) ^ (alpha / 2 - 1))
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (sub_pos.mpr hu1)
  have hcont : Continuous (fun t : ℝ => (1 + x * max t 0) ^ (u - 1)) := by
    apply Continuous.rpow_const
      (continuous_const.add (continuous_const.mul (continuous_id.max continuous_const)))
    intro t
    left
    have : 0 ≤ x * max t 0 := mul_nonneg hx.le (le_max_right t 0)
    change 1 + x * max t 0 ≠ 0
    exact (by linarith : 0 < 1 + x * max t 0).ne'
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (1 + x * t) ^ (u - 1)) μ := by
    refine hcont.aestronglyMeasurable.congr ?_
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    rw [max_eq_left ht.1.le]
  have hbound : ∀ᵐ t ∂μ, ‖(1 + x * t) ^ (u - 1)‖ ≤ (1 : ℝ) := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 1 ≤ 1 + x * t := by nlinarith [mul_pos hx ht.1]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hbase) (u - 1))]
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  change Integrable (fun t : ℝ => (1 + x * t) ^ (u - 1)) μ
  exact (integrable_const (1 : ℝ)).mono' hmeas hbound

theorem gaussEulerNegativeDerivativeIntegrable {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    Integrable (fun t : ℝ => (alpha / 2) * t *
      (1 + x * t) ^ (alpha / 2 - 1))
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (sub_pos.mpr hu1)
  have hk : Integrable (fun t : ℝ => (1 + x * t) ^ (u - 1)) μ := by
    simpa [u, μ] using gaussEulerNegativeKernel_integrable hα hα1 hx
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => u * t * (1 + x * t) ^ (u - 1)) μ :=
    ((continuous_const.mul continuous_id).aestronglyMeasurable.mul hk.1)
  have hbound : ∀ᵐ t ∂μ,
      ‖u * t * (1 + x * t) ^ (u - 1)‖ ≤ u := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 1 ≤ 1 + x * t := by nlinarith [mul_pos hx ht.1]
    have hk0 : 0 ≤ (1 + x * t) ^ (u - 1) :=
      Real.rpow_nonneg (zero_le_one.trans hbase) _
    have hk1 : (1 + x * t) ^ (u - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hu.le ht.1.le) hk0)]
    calc
      u * t * (1 + x * t) ^ (u - 1) ≤ u * t * 1 :=
        mul_le_mul_of_nonneg_left hk1 (mul_nonneg hu.le ht.1.le)
      _ ≤ u := by
        simpa only [mul_one] using mul_le_of_le_one_right hu.le ht.2.le
  change Integrable (fun t : ℝ => u * t * (1 + x * t) ^ (u - 1)) μ
  exact (integrable_const u).mono' hmeas hbound

theorem gaussEulerNegative_decay_operator_eq {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    x ^ (alpha / 2) *
        (x * (∫ t : ℝ, (alpha / 2) * t * (1 + x * t) ^ (alpha / 2 - 1)
          ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) -
          (alpha / 2) * gaussEulerContinuation alpha (-x)) =
      -(alpha / 2) *
        (x ^ (alpha / 2) *
          ∫ t : ℝ, (1 + x * t) ^ (alpha / 2 - 1)
            ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hderiv : Integrable (fun t : ℝ => u * t * (1 + x * t) ^ (u - 1)) μ := by
    simpa [u, μ] using gaussEulerNegativeDerivativeIntegrable hα hα1 hx
  have heuler : Integrable (fun t : ℝ => (1 + x * t) ^ u) μ := by
    simpa [u, μ, sub_eq_add_neg] using
      gaussEulerIntegrand_integrable hα hα1 (show -x < 1 by linarith)
  have hkernel : Integrable (fun t : ℝ => (1 + x * t) ^ (u - 1)) μ := by
    simpa [u, μ] using gaussEulerNegativeKernel_integrable hα hα1 hx
  have hpoint : ∀ᵐ t ∂μ,
      x * (u * t * (1 + x * t) ^ (u - 1)) - u * (1 + x * t) ^ u =
        -u * (1 + x * t) ^ (u - 1) := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 0 < 1 + x * t := by nlinarith [mul_pos hx ht.1]
    have hpow : (1 + x * t) ^ u =
        (1 + x * t) ^ (u - 1) * (1 + x * t) := by
      calc
        (1 + x * t) ^ u = (1 + x * t) ^ ((u - 1) + 1) := by
          congr 1
          ring
        _ = (1 + x * t) ^ (u - 1) * (1 + x * t) ^ (1 : ℝ) :=
          Real.rpow_add hbase (u - 1) 1
        _ = (1 + x * t) ^ (u - 1) * (1 + x * t) := by rw [Real.rpow_one]
    rw [hpow]
    ring
  have hintegral :
      x * (∫ t : ℝ, u * t * (1 + x * t) ^ (u - 1) ∂μ) -
          u * (∫ t : ℝ, (1 + x * t) ^ u ∂μ) =
        -u * (∫ t : ℝ, (1 + x * t) ^ (u - 1) ∂μ) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub (hderiv.const_mul x) (heuler.const_mul u),
      integral_congr_ae hpoint, MeasureTheory.integral_const_mul]
  unfold gaussEulerContinuation
  simp only [neg_mul, sub_neg_eq_add]
  dsimp [u, μ] at hintegral
  rw [hintegral]
  ring

theorem gaussEulerContinuation_decay_operator_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto
      (fun x : ℝ => x ^ (alpha / 2) *
        (x * (∫ t : ℝ, (alpha / 2) * t *
            (1 + x * t) ^ (alpha / 2 - 1)
            ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) -
          (alpha / 2) * gaussEulerContinuation alpha (-x)))
      atTop (nhds (-alpha * gaussConnectionB alpha)) := by
  let u : ℝ := alpha / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hu2 : 2 * u < 1 := by dsimp [u]; linarith
  have hk := betaMobius_weighted_kernel_tendsto hu hu2
  have hs := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => -u) atTop (nhds (-u))).mul hk
  have hs' : Tendsto
      (fun x : ℝ => -u *
        (x ^ u * ∫ t : ℝ, (1 + x * t) ^ (u - 1)
          ∂ProbabilityTheory.betaMeasure u (1 - u)))
      atTop (nhds (-alpha * gaussConnectionB alpha)) := by
    convert hs using 1
    dsimp [u]
    rw [show 1 - 2 * (alpha / 2) = 1 - alpha by ring]
    rw [gaussBetaDecayRatio_eq_two_connectionB hα hα1]
    ring
  apply hs'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gaussEulerNegative_decay_operator_eq hα hα1 hx).symm

end Hilbert16.Spikes
