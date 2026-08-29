import Hilbert16.Spikes.BorelGaussConnection
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false

namespace Hilbert16.Spikes

open Nat Polynomial MeasureTheory Filter

/-! ### Real analyticity of the Euler continuation on the negative axis

The identity theorem needed for the shifted-independence argument requires more than the two
derivatives used by the connection-formula proof.  We obtain a local power series at every
`x > 0` by expanding the Euler kernel around `x`.  The expansion parameter is
`y * t / (1 + x * t)`, whose absolute value is uniformly smaller than `|y|` on the support of the
Beta law.
-/

/-- Taylor coefficient of `x ↦ gaussEulerContinuation alpha (-x)` about a positive base point. -/
noncomputable def gaussEulerNegativeTaylorCoefficient (alpha x : ℝ) (n : ℕ) : ℝ :=
  ∫ t : ℝ, Ring.choose (alpha / 2) n * (1 + x * t) ^ (alpha / 2) *
      (t / (1 + x * t)) ^ n
    ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)

/-- The Euler representative has a genuine local power series at every point of the negative
axis (written in the positive coordinate `x ↦ -x`). -/
theorem gaussEulerNegative_hasFPowerSeriesAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    HasFPowerSeriesAt (fun y : ℝ => gaussEulerContinuation alpha (-y))
      (FormalMultilinearSeries.ofScalars ℝ
        (gaussEulerNegativeTaylorCoefficient alpha x)) x := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let coeff : ℕ → ℝ := fun n =>
    ∫ t : ℝ, Ring.choose u n * (1 + x * t) ^ u * (t / (1 + x * t)) ^ n ∂μ
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with y hy
  have hyabs : |y| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using hy
  let F : ℕ → ℝ → ℝ := fun n t =>
    Ring.choose u n * (1 + x * t) ^ u * (y * t / (1 + x * t)) ^ n
  let C : ℝ := (1 + x) ^ u
  let bound : ℕ → ℝ → ℝ := fun n _ =>
    C * ‖binomialSeries ℝ u n (fun _ => |y|)‖
  have hbinomialSummable :
      Summable fun n => ‖binomialSeries ℝ u n (fun _ => |y|)‖ := by
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
    simpa [Real.dist_eq, abs_of_nonneg (abs_nonneg y)] using hyabs
  have hboundSummable : ∀ᵐ t ∂μ, Summable fun n => bound n t := by
    exact ae_of_all _ fun _ => hbinomialSummable.const_smul C
  have hboundIntegrable : Integrable (fun t => ∑' n, bound n t) μ := by
    simp [bound]
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (by fun_prop (disch := positivity) : Measurable (F n)).aestronglyMeasurable
  have hFbound : ∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ bound n t := by
    intro n
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 1 ≤ 1 + x * t := by nlinarith [mul_pos hx ht.1]
    have hbase0 : 0 ≤ 1 + x * t := le_trans zero_le_one hbase
    have hbaseC : (1 + x * t) ^ u ≤ C := by
      dsimp [C]
      apply Real.rpow_le_rpow hbase0
      · nlinarith [mul_lt_mul_of_pos_left ht.2 hx]
      · exact hu.le
    have hbasePow0 : 0 ≤ (1 + x * t) ^ u := Real.rpow_nonneg hbase0 _
    have hratio : |y * t / (1 + x * t)| ≤ |y| := by
      rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < 1 + x * t),
        abs_of_pos ht.1]
      have htbase : t / (1 + x * t) ≤ 1 := by
        rw [div_le_one (by linarith : 0 < 1 + x * t)]
        nlinarith [mul_pos hx ht.1, ht.2]
      calc
        |y| * t / (1 + x * t) = |y| * (t / (1 + x * t)) := by ring
        _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left htbase (abs_nonneg y)
        _ = |y| := mul_one _
    calc
      ‖F n t‖ = |Ring.choose u n| * (1 + x * t) ^ u *
          |y * t / (1 + x * t)| ^ n := by
        dsimp [F]
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hbasePow0]
      _ ≤ |Ring.choose u n| * C * |y| ^ n := by
        gcongr
      _ = bound n t := by
        simp [bound, C, binomialSeries, FormalMultilinearSeries.coeff_ofScalars]
        ring
  have hFlim : ∀ᵐ t ∂μ, HasSum (fun n => F n t) ((1 + (x + y) * t) ^ u) := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 0 < 1 + x * t := by nlinarith [mul_pos hx ht.1]
    have hratioAbs : |y * t / (1 + x * t)| < 1 := by
      have hratio : |y * t / (1 + x * t)| ≤ |y| := by
        rw [abs_div, abs_mul, abs_of_pos hbase, abs_of_pos ht.1]
        have htbase : t / (1 + x * t) ≤ 1 := by
          rw [div_le_one hbase]
          nlinarith [mul_pos hx ht.1, ht.2]
        calc
          |y| * t / (1 + x * t) = |y| * (t / (1 + x * t)) := by ring
          _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left htbase (abs_nonneg y)
          _ = |y| := mul_one _
      exact hratio.trans_lt hyabs
    have hmem : y * t / (1 + x * t) ∈ Metric.eball (0 : ℝ) 1 := by
      rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
      simpa only [Real.dist_eq, sub_zero] using hratioAbs
    have hbin := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := u)).hasSum hmem
    have hscaled := hbin.mul_left ((1 + x * t) ^ u)
    have hscaled' :
        HasSum
          (fun i => (1 + x * t) ^ u *
            binomialSeries ℝ u i (fun _ => y * t / (1 + x * t)))
          ((1 + x * t) ^ u * (1 + y * t / (1 + x * t)) ^ u) := by
      simpa only [zero_add] using hscaled
    have hsecond : 0 ≤ 1 + y * t / (1 + x * t) := by
      have : -1 < y * t / (1 + x * t) := neg_lt_of_abs_lt hratioAbs
      linarith
    have htarget :
        (1 + x * t) ^ u * (1 + y * t / (1 + x * t)) ^ u =
          (1 + (x + y) * t) ^ u := by
      rw [← Real.mul_rpow hbase.le hsecond]
      congr 1
      field_simp [hbase.ne']
      ring
    rw [← htarget]
    apply hscaled'.congr_fun
    intro n
    simp [F, binomialSeries, FormalMultilinearSeries.coeff_ofScalars]
    ring
  have hIntegrated :
      HasSum (fun n => ∫ t, F n t ∂μ)
        (gaussEulerContinuation alpha (-(x + y))) := by
    have h := MeasureTheory.hasSum_integral_of_dominated_convergence
      bound hFmeas hFbound hboundSummable hboundIntegrable hFlim
    have hIntEq :
        (∫ t, (1 + (x + y) * t) ^ u ∂μ) =
          gaussEulerContinuation alpha (-(x + y)) := by
      dsimp [μ, u, gaussEulerContinuation]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    rw [← hIntEq]
    exact h
  have hterm (n : ℕ) :
      (∫ t, F n t ∂μ) = y ^ n * coeff n := by
    dsimp [F, coeff]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [mul_div_assoc, mul_pow]
    ring
  have hseries : HasSum (fun n => y ^ n * coeff n)
      (gaussEulerContinuation alpha (-(x + y))) := by
    exact hIntegrated.congr_fun fun n => (hterm n).symm
  simpa [FormalMultilinearSeries.coeff_ofScalars, coeff, u, μ,
    gaussEulerNegativeTaylorCoefficient, add_comm] using hseries

/-- The negative-axis Euler continuation is real analytic on the whole positive `x` coordinate. -/
theorem gaussEulerNegative_analyticOnNhd {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    AnalyticOnNhd ℝ (fun x : ℝ => gaussEulerContinuation alpha (-x)) (Set.Ioi 0) := by
  intro x hx
  exact ⟨_, gaussEulerNegative_hasFPowerSeriesAt hα hα1 hx⟩

end Hilbert16.Spikes
