import Hilbert16.Spikes.BorelGaussAnalytic

set_option autoImplicit false

namespace Hilbert16

open Filter Finset MeasureTheory

open Spikes

/-! ### The formal family and its differentiated Borel coefficients -/

/-- Coefficient sequence of the formal shift `t ^ q * ℱ_alpha(t)`. -/
noncomputable def formalTwoFZeroShift (alpha : ℝ) (q : ℕ) : ℕ → ℝ :=
  fun n => if q ≤ n then formalTwoFZeroCoefficient alpha (n - q) else 0

@[simp]
theorem formalTwoFZeroShift_apply_of_le {alpha : ℝ} {q n : ℕ} (hqn : q ≤ n) :
    formalTwoFZeroShift alpha q n = formalTwoFZeroCoefficient alpha (n - q) := by
  simp [formalTwoFZeroShift, hqn]

@[simp]
theorem formalTwoFZeroShift_apply_of_lt {alpha : ℝ} {q n : ℕ} (hnq : n < q) :
    formalTwoFZeroShift alpha q n = 0 := by
  simp [formalTwoFZeroShift, Nat.not_le.mpr hnq]

/-- Coefficient of `s ^ m` after taking `r` derivatives of the Borel image. -/
noncomputable def gaussBorelDerivativeCoefficient (alpha : ℝ) (r m : ℕ) : ℝ :=
  formalTwoFZeroCoefficient alpha (m + r) / m.factorial

/-- Differentiating the Borel transform `e - 1` times converts the `q`-th formal shift into
derivative order `e - 1 - q`.  This is the coefficientwise content of Paper Eq. (5.4), using the
uniform order `e - 1` instead of the largest nonzero shift. -/
theorem formalShift_relation_borelDerivativeCoefficients
    {d e : ℕ} (alpha : Fin d → ℝ) (c : Fin e × Fin d → ℝ)
    (hrelation :
      ∑ iq, c iq • formalTwoFZeroShift (alpha iq.2) iq.1.val = 0) :
    ∀ m : ℕ,
      ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
        (e.pred - iq.1.val) m = 0 := by
  intro m
  have hpoint := congrFun hrelation (m + e.pred)
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpoint
  have hraw :
      ∑ iq, c iq * formalTwoFZeroCoefficient (alpha iq.2)
        (m + (e.pred - iq.1.val)) = 0 := by
    rw [← hpoint]
    apply Finset.sum_congr rfl
    intro iq _
    have hqpred : iq.1.val ≤ e.pred := Nat.le_pred_of_lt iq.1.isLt
    have hqn : iq.1.val ≤ m + e.pred := hqpred.trans (Nat.le_add_left _ _)
    rw [formalTwoFZeroShift_apply_of_le hqn]
    congr 2
    omega
  calc
    ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m =
        (∑ iq, c iq * formalTwoFZeroCoefficient (alpha iq.2)
          (m + (e.pred - iq.1.val))) / m.factorial := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro iq _
            simp [gaussBorelDerivativeCoefficient]
            ring
    _ = 0 := by rw [hraw, zero_div]

/-! ### Arbitrary derivatives of the Borel power series -/

/-- One derivative of a scalar formal multilinear series, evaluated in the unit direction so that
the result is again scalar-valued. -/
noncomputable def scalarDerivSeries
    (p : FormalMultilinearSeries ℝ ℝ ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries p.derivSeries

/-- The scalar coefficient of the differentiated series has the usual `(n + 1)` factor. -/
theorem scalarDerivSeries_coeff (p : FormalMultilinearSeries ℝ ℝ ℝ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = (n + 1 : ℝ) * p.coeff (n + 1) := by
  change (p.derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp

/-- A scalar power-series expansion differentiates without shrinking its certified ball. -/
theorem HasFPowerSeriesOnBall.scalarDeriv
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x : ℝ} {r : ENNReal} (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (deriv f) (scalarDerivSeries p) x r := by
  have hf := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesOnBall h.fderiv
  unfold scalarDerivSeries
  apply hf.congr
  intro z _
  simp [Function.comp_apply, fderiv_eq_smul_deriv]

/-- The scalar series after `r` successive differentiations. -/
noncomputable def scalarIteratedDerivSeries
    (p : FormalMultilinearSeries ℝ ℝ ℝ) (r : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (scalarDerivSeries^[r]) p

/-- Iterating the preceding construction gives the power series of `iteratedDeriv`. -/
theorem HasFPowerSeriesOnBall.scalarIteratedDeriv
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x : ℝ} {R : ENNReal} (h : HasFPowerSeriesOnBall f p x R) (r : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv r f) (scalarIteratedDerivSeries p r) x R := by
  induction r with
  | zero => simpa [scalarIteratedDerivSeries, iteratedDeriv]
  | succ r ih =>
      rw [iteratedDeriv_succ]
      simpa [scalarIteratedDerivSeries, Function.iterate_succ_apply'] using
        (HasFPowerSeriesOnBall.scalarDeriv ih)

/-- In the paper's parameter range, the original Borel hypergeometric series has radius one. -/
theorem gaussBorelSeries_radius_eq_one {alpha : ℝ} (hα : 0 < alpha) (hα1 : alpha < 1) :
    (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro n
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhalf : (n : ℝ) ≠ alpha / 2 := by
    intro hn
    by_cases hnzero : n = 0
    · subst n
      norm_num at hn
      linarith
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnzero
      linarith
  constructor
  · simpa only [neg_div, neg_neg] using hhalf
  constructor <;> linarith

/-- The formal scalar series representing the `r`-th derivative of the Borel image. -/
noncomputable def gaussBorelDerivativeSeries (alpha : ℝ) (r : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  scalarIteratedDerivSeries
    (ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1) r

/-- Its coefficient is exactly `U_(m+r)(alpha) / m!`. -/
theorem gaussBorelDerivativeSeries_coeff (alpha : ℝ) (r m : ℕ) :
    (gaussBorelDerivativeSeries alpha r).coeff m =
      gaussBorelDerivativeCoefficient alpha r m := by
  induction r generalizing m with
  | zero =>
      simp [gaussBorelDerivativeSeries, scalarIteratedDerivSeries,
        gaussBorelDerivativeCoefficient, ordinaryHypergeometricSeries,
        FormalMultilinearSeries.coeff_ofScalars,
        ← formalTwoFZeroCoefficient_borel]
  | succ r ih =>
      rw [gaussBorelDerivativeSeries, scalarIteratedDerivSeries,
        Function.iterate_succ_apply', scalarDerivSeries_coeff]
      change (m + 1 : ℝ) *
          (gaussBorelDerivativeSeries alpha r).coeff (m + 1) = _
      rw [ih]
      simp only [gaussBorelDerivativeCoefficient, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      rw [show m + 1 + r = m + (r + 1) by omega]
      have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hfac]

/-- On the unit ball, the preceding formal series is the actual `r`-th derivative of the Borel
hypergeometric function. -/
theorem gaussBorelDerivative_hasFPowerSeriesOnBall {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (r : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv r (gaussBorelImage alpha))
      (gaussBorelDerivativeSeries alpha r) 0 1 := by
  let p := ordinaryHypergeometricSeries ℝ (-alpha / 2) (alpha / 2) 1
  have hp : HasFPowerSeriesOnBall (gaussBorelImage alpha) p 0 1 := by
    have hpRadius : p.radius = 1 := by
      simpa [p] using gaussBorelSeries_radius_eq_one hα hα1
    have hraw := p.hasFPowerSeriesOnBall (by
      rw [hpRadius]
      norm_num)
    change HasFPowerSeriesOnBall p.sum p 0 1
    rw [hpRadius] at hraw
    exact hraw
  simpa [gaussBorelDerivativeSeries, p] using
    (HasFPowerSeriesOnBall.scalarIteratedDeriv hp r)

/-- A formal shifted relation becomes the corresponding fixed-order derivative relation throughout
the open Borel unit disk. -/
theorem formalShift_relation_gaussBorelDerivatives
    {d e : ℕ} (alpha : Fin d → ℝ) (c : Fin e × Fin d → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i) (halpha_one : ∀ i, alpha i < 1)
    (hrelation :
      ∑ iq, c iq • formalTwoFZeroShift (alpha iq.2) iq.1.val = 0)
    {s : ℝ} (hs : |s| < 1) :
    ∑ iq, c iq * iteratedDeriv (e.pred - iq.1.val)
      (gaussBorelImage (alpha iq.2)) s = 0 := by
  have hmem : s ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    simpa [Real.dist_eq] using hs
  have hcoeff := formalShift_relation_borelDerivativeCoefficients alpha c hrelation
  have hterm : ∀ iq : Fin e × Fin d,
      HasSum
        (fun m => c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m * s ^ m)
        (c iq * iteratedDeriv (e.pred - iq.1.val)
          (gaussBorelImage (alpha iq.2)) s) := by
    intro iq
    have hfps := gaussBorelDerivative_hasFPowerSeriesOnBall
      (halpha_pos iq.2) (halpha_one iq.2) (e.pred - iq.1.val)
    have hsum := hfps.hasSum hmem
    have hsum' :
        HasSum
          (fun m => gaussBorelDerivativeCoefficient (alpha iq.2)
            (e.pred - iq.1.val) m * s ^ m)
          (iteratedDeriv (e.pred - iq.1.val)
            (gaussBorelImage (alpha iq.2)) s) := by
      simpa [gaussBorelDerivativeSeries_coeff,
        FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm] using hsum
    simpa [mul_assoc] using hsum'.mul_left (c iq)
  have hsum :
      HasSum
        (fun m => ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m * s ^ m)
        (∑ iq, c iq * iteratedDeriv (e.pred - iq.1.val)
          (gaussBorelImage (alpha iq.2)) s) := by
    have hraw := tendsto_finsetSum Finset.univ (fun iq _ => hterm iq)
    change Tendsto _ _ _
    convert hraw using 1
    funext b
    rw [Finset.sum_comm]
  have hzeroTerms :
      (fun m => ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m * s ^ m) = fun _ => 0 := by
    funext m
    calc
      ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m * s ^ m =
        (∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
          (e.pred - iq.1.val) m) * s ^ m := by rw [Finset.sum_mul]
      _ = 0 * s ^ m := by rw [hcoeff m]
      _ = 0 := zero_mul _
  have hzero : HasSum
      (fun m => ∑ iq, c iq * gaussBorelDerivativeCoefficient (alpha iq.2)
        (e.pred - iq.1.val) m * s ^ m) 0 := by
    rw [hzeroTerms]
    exact hasSum_zero
  exact hsum.unique hzero

/-! ### Analytic continuation of the differentiated relation -/

/-- The continuation of the `r`-th Borel derivative, written in the positive coordinate on the
negative axis.  The sign compensates for differentiating `s = -x`. -/
noncomputable def gaussNegativeDerivative (alpha : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ r * iteratedDeriv r
    (fun y : ℝ => gaussEulerContinuation alpha (-y)) x

/-- On `0 < x < 1`, the continued derivative agrees with the derivative of the original Borel
power series evaluated at `-x`. -/
theorem gaussNegativeDerivative_eq_borelDerivative {alpha x : ℝ} (r : ℕ)
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    gaussNegativeDerivative alpha r x =
      iteratedDeriv r (gaussBorelImage alpha) (-x) := by
  let E : ℝ → ℝ := fun y => gaussEulerContinuation alpha (-y)
  let G : ℝ → ℝ := fun y => gaussBorelImage alpha (-y)
  have hEG : Set.EqOn E G (Set.Ioo 0 1) := by
    intro y hy
    dsimp [E, G]
    apply gaussEulerContinuation_eq_borelImage hα hα1
    rw [abs_neg]
    exact (abs_of_pos hy.1).trans_lt hy.2
  have hderiv := (hEG.iteratedDeriv_of_isOpen isOpen_Ioo r) ⟨hx0, hx1⟩
  have hcomp := iteratedDeriv_comp_neg r (gaussBorelImage alpha) x
  dsimp [E, G] at hderiv
  unfold gaussNegativeDerivative
  rw [hderiv, hcomp]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← pow_add]
  simp

/-- Every continued Borel derivative is analytic on the entire negative axis. -/
theorem gaussNegativeDerivative_analyticOnNhd {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (r : ℕ) :
    AnalyticOnNhd ℝ (gaussNegativeDerivative alpha r) (Set.Ioi 0) := by
  have hbase := Spikes.gaussEulerNegative_analyticOnNhd hα hα1
  have hderiv : AnalyticOnNhd ℝ
      (iteratedDeriv r (fun y : ℝ => gaussEulerContinuation alpha (-y))) (Set.Ioi 0) := by
    rw [iteratedDeriv_eq_iterate]
    exact hbase.iterated_deriv r
  have hc : AnalyticOnNhd ℝ (fun _ : ℝ => (-1 : ℝ) ^ r) (Set.Ioi 0) :=
    analyticOnNhd_const
  unfold gaussNegativeDerivative
  exact hc.mul hderiv

/-- The differentiated relation obtained in the unit disk continues to every `x > 0`. -/
theorem formalShift_relation_gaussNegativeDerivatives
    {d e : ℕ} (alpha : Fin d → ℝ) (c : Fin e × Fin d → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i) (halpha_one : ∀ i, alpha i < 1)
    (hrelation :
      ∑ iq, c iq • formalTwoFZeroShift (alpha iq.2) iq.1.val = 0) :
    ∀ x : ℝ, 0 < x →
      ∑ iq, c iq * gaussNegativeDerivative (alpha iq.2)
        (e.pred - iq.1.val) x = 0 := by
  let H : ℝ → ℝ := fun x =>
    ∑ iq, c iq * gaussNegativeDerivative (alpha iq.2) (e.pred - iq.1.val) x
  have hH : AnalyticOnNhd ℝ H (Set.Ioi 0) := by
    dsimp [H]
    have hterm : ∀ iq : Fin e × Fin d, AnalyticOnNhd ℝ
        (fun x => c iq * gaussNegativeDerivative (alpha iq.2)
          (e.pred - iq.1.val) x) (Set.Ioi 0) := by
      intro iq
      have hc : AnalyticOnNhd ℝ (fun _ : ℝ => c iq) (Set.Ioi 0) := analyticOnNhd_const
      exact hc.mul (gaussNegativeDerivative_analyticOnNhd
        (halpha_pos iq.2) (halpha_one iq.2) (e.pred - iq.1.val))
    have hsum := Finset.analyticOnNhd_sum Finset.univ (fun iq _ => hterm iq)
    have hfun :
        (∑ iq, fun x => c iq * gaussNegativeDerivative (alpha iq.2)
          (e.pred - iq.1.val) x) =
        (fun x => ∑ iq, c iq * gaussNegativeDerivative (alpha iq.2)
          (e.pred - iq.1.val) x) := by
      funext x
      simp only [Fintype.sum_apply]
    change AnalyticOnNhd ℝ
      (fun x => ∑ iq, c iq * gaussNegativeDerivative (alpha iq.2)
        (e.pred - iq.1.val) x) (Set.Ioi 0)
    rw [← hfun]
    exact hsum
  have hlocal : H =ᶠ[nhds (1 / 2 : ℝ)] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    dsimp [H]
    have hB := formalShift_relation_gaussBorelDerivatives alpha c
      halpha_pos halpha_one hrelation (s := -x) (by
        rw [abs_neg, abs_of_pos hx.1]
        exact hx.2)
    calc
      ∑ iq, c iq * gaussNegativeDerivative (alpha iq.2)
          (e.pred - iq.1.val) x =
        ∑ iq, c iq * iteratedDeriv (e.pred - iq.1.val)
          (gaussBorelImage (alpha iq.2)) (-x) := by
            apply Finset.sum_congr rfl
            intro iq _
            rw [gaussNegativeDerivative_eq_borelDerivative
              (e.pred - iq.1.val) (halpha_pos iq.2) (halpha_one iq.2) hx.1 hx.2]
      _ = 0 := hB
  have hglobal : Set.EqOn H (fun _ => 0) (Set.Ioi 0) :=
    hH.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      isPreconnected_Ioi (show (1 / 2 : ℝ) ∈ Set.Ioi 0 by norm_num) hlocal
  intro x hx
  exact hglobal hx

/-! ### Arbitrary-order negative-axis asymptotics -/

/-- The explicit Taylor coefficient constructed in the analytic-continuation proof gives every
iterated derivative. -/
theorem iteratedDeriv_gaussEulerNegative_eq_taylorCoefficient
    {alpha x : ℝ} (r : ℕ) (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    iteratedDeriv r (fun y : ℝ => gaussEulerContinuation alpha (-y)) x =
      (r.factorial : ℝ) * gaussEulerNegativeTaylorCoefficient alpha x r := by
  rcases gaussEulerNegative_hasFPowerSeriesAt hα hα1 hx with ⟨R, hR⟩
  have h := hR.factorial_smul (1 : ℝ) r
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, nsmul_eq_mul,
    gaussEulerNegativeTaylorCoefficient] using h.symm

/-- Algebraic normalization of the kernel occurring in the `r`-th derivative. -/
private theorem gaussDerivative_normalized_kernel {x t u : ℝ}
    (hx : 0 < x) (ht : 0 < t) (r : ℕ) :
    ((1 + x * t) ^ u * (t / (1 + x * t)) ^ r) /
        x ^ (u - (r : ℝ)) =
      t ^ r * (t + x⁻¹) ^ (u - (r : ℝ)) := by
  have hbase : 0 < 1 + x * t := by nlinarith [mul_pos hx ht]
  have hy : 0 < t + x⁻¹ := add_pos_of_pos_of_nonneg ht (inv_nonneg.mpr hx.le)
  have hbaseeq : 1 + x * t = x * (t + x⁻¹) := by
    field_simp [hx.ne']
    ring
  have hxpow : x ^ (u - (r : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hbasepow : (1 + x * t) ^ r = (1 + x * t) ^ (r : ℝ) :=
    (Real.rpow_natCast (1 + x * t) r).symm
  rw [show (t / (1 + x * t)) ^ r = t ^ r / (1 + x * t) ^ r by rw [div_pow]]
  rw [hbasepow]
  rw [show (1 + x * t) ^ u * (t ^ r / (1 + x * t) ^ (r : ℝ)) =
      t ^ r * ((1 + x * t) ^ u / (1 + x * t) ^ (r : ℝ)) by ring]
  rw [← Real.rpow_sub hbase u (r : ℝ)]
  rw [hbaseeq, Real.mul_rpow hx.le hy.le]
  field_simp [hxpow]

/-- The Beta moment that supplies the common leading connection coefficient. -/
theorem gaussBetaRpowMoment_eq_connectionA {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    (∫ t, t ^ (alpha / 2)
      ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) =
      gaussConnectionA alpha := by
  let u : ℝ := alpha / 2
  have hu : 0 < u := by dsimp [u]; linarith
  rw [betaMeasure_rpow_moment hu (by linarith) (by linarith : 0 < u + u)]
  dsimp [u]
  unfold gaussConnectionA ProbabilityTheory.beta
  rw [show alpha / 2 + alpha / 2 = alpha by ring,
    show alpha / 2 + (1 - alpha / 2) = 1 by ring,
    show alpha + (1 - alpha / 2) = 1 + alpha / 2 by ring,
    Real.Gamma_one]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < alpha / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - alpha / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + alpha / 2)).ne']
  rw [div_self (Real.Gamma_pos_of_pos (by linarith : 0 < (2 - alpha) / 2)).ne']

/-- Every Taylor coefficient has the power-law asymptotic predicted by termwise differentiation of
the growing connection branch. -/
theorem gaussEulerNegativeTaylorCoefficient_tendsto {alpha : ℝ} (r : ℕ)
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto
      (fun x : ℝ => gaussEulerNegativeTaylorCoefficient alpha x r /
        x ^ (alpha / 2 - (r : ℝ)))
      atTop
      (nhds (Ring.choose (alpha / 2) r * gaussConnectionA alpha)) := by
  cases r with
  | zero =>
      have hlead := gaussEulerContinuation_leading_tendsto hα hα1
      simpa [gaussEulerNegativeTaylorCoefficient, gaussEulerContinuation] using hlead
  | succ r =>
      let n : ℕ := r + 1
      let u : ℝ := alpha / 2
      let v : ℝ := u - n
      let μ : MeasureTheory.Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
      have hu : 0 < u := by dsimp [u]; linarith
      have hu1 : u < 1 := by dsimp [u]; linarith
      have hn : 1 ≤ n := by dsimp [n]; omega
      have hv : v < 0 := by
        dsimp [v]
        have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
      have hDCT :
          Tendsto
            (fun x : ℝ => ∫ t, t ^ n * (t + x⁻¹) ^ v ∂μ)
            atTop (nhds (∫ t, t ^ u ∂μ)) := by
        apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (fun _ : ℝ => (1 : ℝ))
        · filter_upwards with x
          exact (by fun_prop : AEStronglyMeasurable
            (fun t : ℝ => t ^ n * (t + x⁻¹) ^ v) μ)
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
          filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
          have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
          have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
          have hty : t ≤ t + x⁻¹ := le_add_of_nonneg_right hinv0
          have hpow := Real.rpow_le_rpow_of_nonpos ht.1 hty hv.le
          have hK0 : 0 ≤ t ^ n * (t + x⁻¹) ^ v :=
            mul_nonneg (pow_nonneg ht.1.le n)
              (Real.rpow_nonneg (add_nonneg ht.1.le hinv0) _)
          rw [Real.norm_eq_abs, abs_of_nonneg hK0]
          calc
            t ^ n * (t + x⁻¹) ^ v ≤ t ^ n * t ^ v :=
              mul_le_mul_of_nonneg_left hpow (pow_nonneg ht.1.le n)
            _ = t ^ u := by
              rw [← Real.rpow_natCast t n, ← Real.rpow_add ht.1]
              congr 2
              dsimp [v]
              ring
            _ ≤ 1 := Real.rpow_le_one ht.1.le ht.2.le hu.le
        · exact integrable_const _
        · filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
          have hbase :
              Tendsto (fun x : ℝ => t + x⁻¹) atTop (nhds t) := by
            have hconst : Tendsto (fun _ : ℝ => t) atTop (nhds t) := tendsto_const_nhds
            simpa using hconst.add tendsto_inv_atTop_zero
          have hpow := hbase.rpow_const (.inl ht.1.ne') (p := v)
          have hmul := hpow.const_mul (t ^ n)
          convert hmul using 1
          rw [← Real.rpow_natCast t n, ← Real.rpow_add ht.1]
          congr 2
          dsimp [v]
          ring
      have hrewrite : ∀ᶠ x : ℝ in atTop,
          gaussEulerNegativeTaylorCoefficient alpha x n / x ^ v =
            Ring.choose u n * (∫ t, t ^ n * (t + x⁻¹) ^ v ∂μ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp [gaussEulerNegativeTaylorCoefficient, u, n, v, μ]
        rw [← MeasureTheory.integral_div, ← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [betaMeasure_ae_mem_Ioo (alpha / 2) (1 - alpha / 2)] with t ht
        rw [mul_div_assoc]
        rw [show Ring.choose (alpha / 2) (r + 1) * (1 + x * t) ^ (alpha / 2) *
            ((t / (1 + x * t)) ^ (r + 1) / x ^ (alpha / 2 - ((r + 1 : ℕ) : ℝ))) =
          Ring.choose (alpha / 2) (r + 1) *
            (((1 + x * t) ^ (alpha / 2) * (t / (1 + x * t)) ^ (r + 1)) /
              x ^ (alpha / 2 - ((r + 1 : ℕ) : ℝ))) by ring]
        rw [gaussDerivative_normalized_kernel hx ht.1 (r + 1)]
      have hscaled := hDCT.const_mul (Ring.choose u n)
      have hmoment : (∫ t, t ^ u ∂μ) = gaussConnectionA alpha := by
        simpa [u, μ] using gaussBetaRpowMoment_eq_connectionA hα hα1
      rw [hmoment] at hscaled
      simpa [n, u, v] using hscaled.congr' (hrewrite.mono fun _ h => h.symm)

/-- The leading coefficient of the continued `r`-th Borel derivative. -/
noncomputable def gaussNegativeDerivativeLeading (alpha : ℝ) (r : ℕ) : ℝ :=
  (-1 : ℝ) ^ r * (r.factorial : ℝ) * Ring.choose (alpha / 2) r *
    gaussConnectionA alpha

/-- Arbitrary-order version of Paper Eq. (5.7). -/
theorem gaussNegativeDerivative_tendsto {alpha : ℝ} (r : ℕ)
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto
      (fun x : ℝ => gaussNegativeDerivative alpha r x /
        x ^ (alpha / 2 - (r : ℝ)))
      atTop (nhds (gaussNegativeDerivativeLeading alpha r)) := by
  have hTaylor := gaussEulerNegativeTaylorCoefficient_tendsto r hα hα1
  have hscaled := hTaylor.const_mul ((-1 : ℝ) ^ r * (r.factorial : ℝ))
  have heq :
      (fun x : ℝ => (-1 : ℝ) ^ r * (r.factorial : ℝ) *
        (gaussEulerNegativeTaylorCoefficient alpha x r /
          x ^ (alpha / 2 - (r : ℝ)))) =ᶠ[atTop]
        (fun x : ℝ => gaussNegativeDerivative alpha r x /
          x ^ (alpha / 2 - (r : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [gaussNegativeDerivative]
    rw [iteratedDeriv_gaussEulerNegative_eq_taylorCoefficient r hα hα1 hx]
    ring
  simpa only [gaussNegativeDerivativeLeading, mul_assoc] using hscaled.congr' heq

/-- Integer and real versions of the descending Pochhammer polynomial agree under evaluation. -/
private theorem descPochhammer_smeval_real_eq_eval (u : ℝ) (r : ℕ) :
    (descPochhammer ℤ r).smeval u = (descPochhammer ℝ r).eval u := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [descPochhammer_succ_right, descPochhammer_succ_right,
        Polynomial.smeval_mul, Polynomial.eval_mul, ih]
      simp [Polynomial.smeval_natCast, Polynomial.eval_natCast]

/-- Generalized binomial coefficients do not vanish for `0 < u < 1`. -/
theorem ringChoose_ne_zero_of_pos_of_lt_one {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (r : ℕ) : Ring.choose u r ≠ 0 := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  apply mul_ne_zero
  · exact inv_ne_zero (by positivity)
  rw [descPochhammer_smeval_real_eq_eval,
    descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [Finset.mem_range] at hj
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  by_cases hjzero : j = 0
  · subst j
    simpa using hu.ne'
  · have hj1 : (1 : ℝ) ≤ j := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hjzero
    linarith

/-- The leading coefficient in every differentiated connection asymptotic is nonzero. -/
theorem gaussNegativeDerivativeLeading_ne_zero {alpha : ℝ} (r : ℕ)
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    gaussNegativeDerivativeLeading alpha r ≠ 0 := by
  unfold gaussNegativeDerivativeLeading
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
      (ringChoose_ne_zero_of_pos_of_lt_one (by linarith) (by linarith) r))
    (gaussConnectionA_ne_zero hα)

/-! ### Finite asymptotic separation

This file is the responsibility module for Paper Lemma 5.1.  The analytic input will be the
negative-axis asymptotic of the continued Borel transforms.  We first isolate the finite-dimensional
argument: nonzero, pairwise distinct real-power leading terms cannot satisfy a linear relation.
-/

/-- A finite family of real-valued functions is linearly independent if its members have nonzero
leading coefficients at pairwise distinct real powers at positive infinity. -/
theorem linearIndependent_of_tendsto_div_rpow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (exponent leading : ι → ℝ)
    (hexponent : Function.Injective exponent)
    (hleading : ∀ i, leading i ≠ 0)
    (hasLeading : ∀ i,
      Tendsto (fun x : ℝ => f i x / x ^ exponent i) atTop (nhds (leading i))) :
    LinearIndependent ℝ f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrelation
  by_contra hc
  push Not at hc
  obtain ⟨i0, hi0⟩ := hc
  let support : Finset ι := Finset.univ.filter fun i => c i ≠ 0
  have hsupport_nonempty : support.Nonempty := by
    exact ⟨i0, by simp [support, hi0]⟩
  obtain ⟨imax, himax_mem, himax⟩ :=
    support.exists_max_image exponent hsupport_nonempty
  have hcmax : c imax ≠ 0 := by
    simpa [support] using himax_mem
  have hterm : ∀ j ∈ support,
      Tendsto
        (fun x : ℝ => c j * f j x / x ^ exponent imax)
        atTop
        (nhds (if j = imax then c imax * leading imax else 0)) := by
    intro j hj
    by_cases hji : j = imax
    · subst j
      simpa [mul_div_assoc] using (hasLeading imax).const_mul (c imax)
    · have hle : exponent j ≤ exponent imax := himax j hj
      have hne : exponent j ≠ exponent imax := fun h => hji (hexponent h)
      have hlt : exponent j < exponent imax := lt_of_le_of_ne hle hne
      have hpow :
          Tendsto (fun x : ℝ => x ^ (exponent j - exponent imax)) atTop (nhds 0) := by
        simpa [sub_eq_add_neg, add_comm] using
          (tendsto_rpow_neg_atTop (sub_pos.mpr hlt))
      have hprod := ((hasLeading j).const_mul (c j)).mul hpow
      rw [if_neg hji]
      simpa only [mul_zero] using hprod.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [Real.rpow_sub hx]
        have hjpow : x ^ exponent j ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
        have himaxpow : x ^ exponent imax ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
        field_simp)
  have hsum_limit :
      Tendsto
        (fun x : ℝ => ∑ j ∈ support, c j * f j x / x ^ exponent imax)
        atTop (nhds (c imax * leading imax)) := by
    have hsum := tendsto_finsetSum support hterm
    simpa [himax_mem] using hsum
  have hsum_zero :
      Tendsto
        (fun x : ℝ => ∑ j ∈ support, c j * f j x / x ^ exponent imax)
        atTop (nhds 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)).congr'
    filter_upwards with x
    have hpoint := congrFun hrelation x
    simp only [Pi.zero_apply, Finset.sum_apply] at hpoint
    have hsupport_point : ∑ j ∈ support, c j * f j x = 0 := by
      rw [← hpoint]
      apply Finset.sum_subset
      · simp [support]
      · intro j _ hj
        have hcj : c j = 0 := by simpa [support] using hj
        simp [hcj]
    rw [← Finset.sum_div, hsupport_point, zero_div]
  have hzero : c imax * leading imax = 0 := tendsto_nhds_unique hsum_limit hsum_zero
  exact mul_ne_zero hcmax (hleading imax) hzero

/-! ### The exponent bookkeeping in Lemma 5.1 -/

/-- The real power attached to the `q`-th Borel shift of parameter `alpha i`. -/
noncomputable def borelGaussShiftExponent {d e : ℕ} (alpha : Fin d → ℝ)
    (iq : Fin e × Fin d) : ℝ :=
  iq.1.val + alpha iq.2 / 2

/-- In the paper's parameter strip, an integer shift plus `alpha / 2` determines both the shift and
the parameter index.  This is the exact distinct-exponent calculation in Paper Eq. (5.8). -/
theorem borelGaussShiftExponent_injective {d e : ℕ} {alpha : Fin d → ℝ}
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha) :
    Function.Injective (borelGaussShiftExponent alpha : Fin e × Fin d → ℝ) := by
  intro iq jq hij
  rcases iq with ⟨q, i⟩
  rcases jq with ⟨r, j⟩
  simp only [borelGaussShiftExponent] at hij
  have hq : q = r := by
    apply Fin.ext
    by_contra hne
    have hlt_or_gt : q.val < r.val ∨ r.val < q.val := Nat.lt_or_gt_of_ne hne
    rcases hlt_or_gt with hqr | hrq
    · have hqr' : (q.val : ℝ) + 1 ≤ r.val := by exact_mod_cast (Nat.succ_le_iff.mpr hqr)
      have hi1 := halpha_one i
      have hj0 := halpha_pos j
      nlinarith
    · have hrq' : (r.val : ℝ) + 1 ≤ q.val := by exact_mod_cast (Nat.succ_le_iff.mpr hrq)
      have hj1 := halpha_one j
      have hi0 := halpha_pos i
      nlinarith
  subst r
  have ha : alpha i = alpha j := by linarith
  have hi : i = j := halpha_injective ha
  subst j
  rfl

/-! ### Paper Lemma 5.1 -/

/-- **Paper Lemma 5.1.**  If the parameters lie strictly between zero and one and are pairwise
distinct (in particular, if they are strictly increasing), then the finite family of shifted formal
hypergeometric series `t ^ q * ℱ_{alpha i}`, `0 ≤ q < e`, is linearly independent over `ℝ`.

The proof applies the Borel transform and differentiates uniformly `e - 1` times.  Analytic
continuation carries the resulting relation to the whole negative axis, where the pair `(q,i)` has
the nonzero leading term with exponent `q + alpha i / 2 - (e - 1)`. -/
theorem formalTwoFZeroShift_linearIndependent
    {d e : ℕ} (alpha : Fin d → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha) :
    LinearIndependent ℝ
      (fun iq : Fin e × Fin d =>
        formalTwoFZeroShift (alpha iq.2) iq.1.val) := by
  classical
  let f : Fin e × Fin d → ℝ → ℝ := fun iq x =>
    if 0 < x then
      gaussNegativeDerivative (alpha iq.2) (e.pred - iq.1.val) x
    else 0
  let exponent : Fin e × Fin d → ℝ := fun iq =>
    borelGaussShiftExponent alpha iq - (e.pred : ℝ)
  let leading : Fin e × Fin d → ℝ := fun iq =>
    gaussNegativeDerivativeLeading (alpha iq.2) (e.pred - iq.1.val)
  have hexponent : Function.Injective exponent := by
    intro iq jq hij
    apply borelGaussShiftExponent_injective halpha_pos halpha_one halpha_injective
    dsimp only [exponent] at hij ⊢
    linarith
  have hleading : ∀ iq, leading iq ≠ 0 := by
    intro iq
    exact gaussNegativeDerivativeLeading_ne_zero
      (e.pred - iq.1.val) (halpha_pos iq.2) (halpha_one iq.2)
  have hasLeading : ∀ iq,
      Tendsto (fun x : ℝ => f iq x / x ^ exponent iq) atTop
        (nhds (leading iq)) := by
    intro iq
    have hq : iq.1.val ≤ e.pred := Nat.le_pred_of_lt iq.1.isLt
    have hexponent_eq :
        alpha iq.2 / 2 - ((e.pred - iq.1.val : ℕ) : ℝ) = exponent iq := by
      dsimp only [exponent, borelGaussShiftExponent]
      rw [Nat.cast_sub hq]
      ring
    have hlim := gaussNegativeDerivative_tendsto
      (e.pred - iq.1.val) (halpha_pos iq.2) (halpha_one iq.2)
    have heq :
        (fun x : ℝ => gaussNegativeDerivative (alpha iq.2)
          (e.pred - iq.1.val) x /
            x ^ (alpha iq.2 / 2 - ((e.pred - iq.1.val : ℕ) : ℝ))) =ᶠ[atTop]
          (fun x : ℝ => f iq x / x ^ exponent iq) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [f, hx, if_pos, hexponent_eq]
    simpa only [leading] using hlim.congr' heq
  have hf_independent : LinearIndependent ℝ f :=
    linearIndependent_of_tendsto_div_rpow f exponent leading
      hexponent hleading hasLeading
  rw [Fintype.linearIndependent_iff]
  intro c hrelation
  have hglobal := formalShift_relation_gaussNegativeDerivatives alpha c
    halpha_pos halpha_one hrelation
  have hf_relation : ∑ iq, c iq • f iq = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : 0 < x
    · simpa only [f, hx, if_pos] using hglobal x hx
    · simp only [f, hx, if_false, mul_zero, Finset.sum_const_zero]
  exact Fintype.linearIndependent_iff.mp hf_independent c hf_relation

/-- Paper-facing strictly ordered form of `formalTwoFZeroShift_linearIndependent`. -/
theorem borelGaussShiftIndependent
    {d e : ℕ} (alpha : Fin d → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_strict : StrictMono alpha) :
    LinearIndependent ℝ
      (fun iq : Fin e × Fin d =>
        formalTwoFZeroShift (alpha iq.2) iq.1.val) :=
  formalTwoFZeroShift_linearIndependent alpha halpha_pos halpha_one
    halpha_strict.injective

end Hilbert16
