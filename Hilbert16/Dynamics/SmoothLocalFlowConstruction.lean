import Hilbert16.Dynamics.SmoothLocalFlowDynamics

set_option autoImplicit false

namespace Hilbert16

open Filter Set Metric MeasureTheory
open scoped Interval Topology

/-- A radius on which one implicit Picard chart is simultaneously a genuine
zero-residual solution chart and `C¹` at every point. -/
theorem LocalPicardCurveBranch.exists_good_radius
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    ∃ r > (0 : ℝ), ∀ p ∈ Metric.ball ((0 : ℝ), z₀) r,
      chebyshevPicardResidual n lambda S (p, C.curve p) = 0 ∧
        ContDiffAt ℝ 1 C.endpoint p := by
  have hsmooth : ∀ᶠ p in nhds ((0 : ℝ), z₀), ContDiffAt ℝ 1 C.endpoint p :=
    C.contDiffAt_endpoint.eventually (by norm_num)
  have hgood : {p : ℝ × ParameterPhaseSpace |
      chebyshevPicardResidual n lambda S (p, C.curve p) = 0 ∧
        ContDiffAt ℝ 1 C.endpoint p} ∈ nhds ((0 : ℝ), z₀) :=
    Filter.inter_mem C.eventually_residual_zero hsmooth
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  exact ⟨r, hr, fun p hp => hball hp⟩

noncomputable def LocalPicardCurveBranch.goodRadius
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) : ℝ :=
  Classical.choose C.exists_good_radius

theorem LocalPicardCurveBranch.goodRadius_pos
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    0 < C.goodRadius :=
  (Classical.choose_spec C.exists_good_radius).1

theorem LocalPicardCurveBranch.good_of_mem_ball
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀)
    {p : ℝ × ParameterPhaseSpace}
    (hp : p ∈ Metric.ball ((0 : ℝ), z₀) C.goodRadius) :
    chebyshevPicardResidual n lambda S (p, C.curve p) = 0 ∧
      ContDiffAt ℝ 1 C.endpoint p :=
  (Classical.choose_spec C.exists_good_radius).2 p hp

/-- The union of all centered Picard balls.  Every lifted initial state occurs
at time zero, and every chart in the union is a genuine smooth solution chart. -/
def smoothPicardDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    Set (ℝ × ParameterPhaseSpace) :=
  ⋃ z₀ : ParameterPhaseSpace,
    Metric.ball ((0 : ℝ), z₀)
      (localPicardCurveBranch n lambda S z₀).goodRadius

theorem isOpen_smoothPicardDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    IsOpen (smoothPicardDomain n lambda S) := by
  unfold smoothPicardDomain
  exact isOpen_iUnion fun _ => isOpen_ball

theorem smoothPicardDomain_zero_mem
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) :
    ((0 : ℝ), z) ∈ smoothPicardDomain n lambda S := by
  apply Set.mem_iUnion.mpr
  refine ⟨z, ?_⟩
  simpa [Metric.mem_ball] using
    (localPicardCurveBranch n lambda S z).goodRadius_pos

/-- Select one Picard chart containing a point of the common domain.  Outside
the domain its value is immaterial. -/
noncomputable def smoothPicardChartCenter
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (p : ℝ × ParameterPhaseSpace) : ParameterPhaseSpace := by
  classical
  exact if hp : p ∈ smoothPicardDomain n lambda S then
      Classical.choose (Set.mem_iUnion.mp hp)
    else p.2

theorem smoothPicardChartCenter_mem_ball
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {p : ℝ × ParameterPhaseSpace}
    (hp : p ∈ smoothPicardDomain n lambda S) :
    p ∈ Metric.ball ((0 : ℝ), smoothPicardChartCenter n lambda S p)
      (localPicardCurveBranch n lambda S
        (smoothPicardChartCenter n lambda S p)).goodRadius := by
  rw [smoothPicardChartCenter, dif_pos hp]
  exact Classical.choose_spec (Set.mem_iUnion.mp hp)

/-- The chart-independent lifted endpoint map on the common Picard domain. -/
noncomputable def smoothPicardLiftedFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    (ℝ × ParameterPhaseSpace) → ParameterPhaseSpace :=
  fun p => (localPicardCurveBranch n lambda S
    (smoothPicardChartCenter n lambda S p)).endpoint p

/-- On every chart ball, the selected global endpoint is exactly that chart's
endpoint.  This is the overlap/gluing theorem. -/
theorem smoothPicardLiftedFlow_eq_endpoint_of_mem_ball
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} {p : ℝ × ParameterPhaseSpace}
    (hp : p ∈ Metric.ball ((0 : ℝ), z₀)
      (localPicardCurveBranch n lambda S z₀).goodRadius) :
    smoothPicardLiftedFlow n lambda S p =
      (localPicardCurveBranch n lambda S z₀).endpoint p := by
  let C := localPicardCurveBranch n lambda S z₀
  have hpDomain : p ∈ smoothPicardDomain n lambda S := by
    exact Set.mem_iUnion.mpr ⟨z₀, hp⟩
  let z₁ := smoothPicardChartCenter n lambda S p
  let D := localPicardCurveBranch n lambda S z₁
  have hpD : p ∈ Metric.ball ((0 : ℝ), z₁) D.goodRadius := by
    exact smoothPicardChartCenter_mem_ball hpDomain
  have hDzero := (D.good_of_mem_ball hpD).1
  have hCzero := (C.good_of_mem_ball hp).1
  change D.endpoint p = C.endpoint p
  unfold LocalPicardCurveBranch.endpoint
  exact chebyshevPicardResidual_endpoint_unique hDzero hCzero

theorem contDiffOn_smoothPicardLiftedFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ContDiffOn ℝ 1 (smoothPicardLiftedFlow n lambda S)
      (smoothPicardDomain n lambda S) := by
  intro p hp
  let z₀ := smoothPicardChartCenter n lambda S p
  let C := localPicardCurveBranch n lambda S z₀
  have hpC : p ∈ Metric.ball ((0 : ℝ), z₀) C.goodRadius := by
    exact smoothPicardChartCenter_mem_ball hp
  have hlocal : smoothPicardLiftedFlow n lambda S =ᶠ[nhds p] C.endpoint := by
    filter_upwards [isOpen_ball.mem_nhds hpC] with q hq
    exact smoothPicardLiftedFlow_eq_endpoint_of_mem_ball hq
  exact ((C.good_of_mem_ball hpC).2.congr_of_eventuallyEq hlocal).contDiffWithinAt

theorem chebyshevPicardResidual_eq_zero_clamp_zero
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0) :
    gamma.clamp 0 = z := by
  have hinitial := chebyshevPicardResidual_eq_zero_initial hzero
  simpa [ODECurve.clamp,
    Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)] using hinitial

/-- A larger normalized Picard solution determines every smaller-time endpoint.
This comparison is the local semigroup statement needed to differentiate the
implicit endpoint with respect to physical time. -/
theorem chebyshevPicardResidual_endpoint_eq_rescale
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {sigma tau : ℝ} (hsigma : sigma ≠ 0) (hlt : |tau| < |sigma|)
    {z : ParameterPhaseSpace} {gamma eta : ODECurve ParameterPhaseSpace}
    (hgamma : chebyshevPicardResidual n lambda S ((sigma, z), gamma) = 0)
    (heta : chebyshevPicardResidual n lambda S ((tau, z), eta) = 0) :
    eta ⟨1, by norm_num⟩ = gamma.clamp (tau / sigma) := by
  rcases eq_or_ne tau 0 with rfl | htau
  · have he := chebyshevPicardResidual_eq_zero_apply heta
      (⟨1, by norm_num⟩ : ODEUnitInterval)
    have hez : eta ⟨1, by norm_num⟩ = z := by
      simpa [unitVolterraCLM_apply] using he
    simpa using hez.trans
      (chebyshevPicardResidual_eq_zero_clamp_zero hgamma).symm
  · let f : ℝ → ParameterPhaseSpace := fun r => eta.clamp (r / tau)
    let g : ℝ → ParameterPhaseSpace := fun r => gamma.clamp (r / sigma)
    have ht₀ : (0 : ℝ) ∈ Set.Ioo (-|tau|) |tau| := by
      simpa using abs_pos.mpr htau
    have hfcont : ContinuousOn f (Set.Icc (-|tau|) |tau|) :=
      (eta.continuous_clamp.comp (continuous_id.div_const tau)).continuousOn
    have hgcont : ContinuousOn g (Set.Icc (-|tau|) |tau|) :=
      (gamma.continuous_clamp.comp (continuous_id.div_const sigma)).continuousOn
    have htNormalized {r : ℝ} (hr : r ∈ Set.Ioo (-|tau|) |tau|) :
        r / tau ∈ Set.Ioo (-1 : ℝ) 1 := by
      change -(1 : ℝ) < r / tau ∧ r / tau < 1
      rw [← abs_lt, abs_div, div_lt_one (abs_pos.mpr htau)]
      simpa [abs_lt] using hr
    have hsNormalized {r : ℝ} (hr : r ∈ Set.Ioo (-|tau|) |tau|) :
        r / sigma ∈ Set.Ioo (-1 : ℝ) 1 := by
      change -(1 : ℝ) < r / sigma ∧ r / sigma < 1
      rw [← abs_lt, abs_div, div_lt_one (abs_pos.mpr hsigma)]
      exact lt_trans (by simpa [abs_lt] using hr) hlt
    have hf : ∀ r ∈ Set.Ioo (-|tau|) |tau|,
        HasDerivAt f (chebyshevLiftedField n lambda S (f r)) r := by
      intro r hr
      simpa [f, chebyshevLiftedField] using
        (chebyshevPicardResidual_eq_zero_rescale_hasDerivAt htau heta
          (htNormalized hr))
    have hg : ∀ r ∈ Set.Ioo (-|tau|) |tau|,
        HasDerivAt g (chebyshevLiftedField n lambda S (g r)) r := by
      intro r hr
      simpa [g, chebyshevLiftedField] using
        (chebyshevPicardResidual_eq_zero_rescale_hasDerivAt hsigma hgamma
          (hsNormalized hr))
    have hinitial : f 0 = g 0 := by
      dsimp [f, g]
      rw [zero_div, zero_div]
      exact (chebyshevPicardResidual_eq_zero_clamp_zero heta).trans
        (chebyshevPicardResidual_eq_zero_clamp_zero hgamma).symm
    have heq := chebyshevLifted_integralCurve_unique_on_Icc
      (n := n) (lambda := lambda) (S := S) ht₀ hfcont hf hgcont hg hinitial
    have htauMem : tau ∈ Set.Icc (-|tau|) |tau| :=
      ⟨neg_abs_le tau, le_abs_self tau⟩
    simpa [f, g, ODECurve.clamp, htau] using heq htauMem

/-- On its good ball, an implicit Picard endpoint chart satisfies the lifted
ODE in the physical-time variable. -/
theorem LocalPicardCurveBranch.endpoint_time_hasDerivAt_of_mem_ball
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀)
    {tau : ℝ} {z : ParameterPhaseSpace}
    (hp : (tau, z) ∈ Metric.ball ((0 : ℝ), z₀) C.goodRadius) :
    HasDerivAt (fun t : ℝ => C.endpoint (t, z))
      (chebyshevLiftedField n lambda S (C.endpoint (tau, z))) tau := by
  let d := max |tau| (dist z z₀)
  let sigma := (d + C.goodRadius) / 2
  have hd : d < C.goodRadius := by
    simpa [d, Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using hp
  have hd_nonneg : 0 ≤ d := le_trans (abs_nonneg tau) (le_max_left _ _)
  have hdsigma : d < sigma := by
    dsimp [sigma]
    linarith
  have hsigma_lt : sigma < C.goodRadius := by
    dsimp [sigma]
    linarith
  have hsigma_pos : 0 < sigma := lt_of_le_of_lt hd_nonneg hdsigma
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma_pos
  have htauSigma : |tau| < |sigma| := by
    rw [abs_of_pos hsigma_pos]
    exact lt_of_le_of_lt (le_max_left _ _) hdsigma
  have hsigmaBall : (sigma, z) ∈
      Metric.ball ((0 : ℝ), z₀) C.goodRadius := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, abs_of_pos hsigma_pos]
    exact max_lt hsigma_lt
      (lt_of_le_of_lt (le_max_right |tau| (dist z z₀)) hd)
  have hzeroSigma := (C.good_of_mem_ball hsigmaBall).1
  let gamma := C.curve (sigma, z)
  have hnormalized : tau / sigma ∈ Set.Ioo (-1 : ℝ) 1 := by
    change -(1 : ℝ) < tau / sigma ∧ tau / sigma < 1
    rw [← abs_lt, abs_div, div_lt_one (abs_pos.mpr hsigma_ne)]
    exact htauSigma
  have hraw : HasDerivAt (fun t : ℝ => gamma.clamp (t / sigma))
      (chebyshevLiftedField n lambda S (gamma.clamp (tau / sigma))) tau := by
    simpa [gamma, chebyshevLiftedField] using
      (chebyshevPicardResidual_eq_zero_rescale_hasDerivAt hsigma_ne
        hzeroSigma hnormalized)
  have htauAbs : tau ∈ Set.Ioo (-|sigma|) |sigma| := by
    simpa [abs_lt] using htauSigma
  have htimeNhds : Set.Ioo (-|sigma|) |sigma| ∈ nhds tau :=
    isOpen_Ioo.mem_nhds htauAbs
  have hballNhds : {t : ℝ | (t, z) ∈
      Metric.ball ((0 : ℝ), z₀) C.goodRadius} ∈ nhds tau := by
    exact (isOpen_ball.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
  have hevent : (fun t : ℝ => C.endpoint (t, z)) =ᶠ[nhds tau]
      (fun t : ℝ => gamma.clamp (t / sigma)) := by
    filter_upwards [hballNhds, htimeNhds] with t htBall htSigma
    have hzeroT := (C.good_of_mem_ball htBall).1
    exact chebyshevPicardResidual_endpoint_eq_rescale hsigma_ne
      (by simpa [abs_lt] using htSigma) hzeroSigma hzeroT
  have hresult := hraw.congr_of_eventuallyEq hevent
  apply hresult.congr_deriv
  have hzeroTau := (C.good_of_mem_ball hp).1
  exact congrArg (chebyshevLiftedField n lambda S)
    (chebyshevPicardResidual_endpoint_eq_rescale hsigma_ne htauSigma
      hzeroSigma hzeroTau).symm

theorem smoothPicardLiftedFlow_time_hasDerivAt
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    (hp : (tau, z) ∈ smoothPicardDomain n lambda S) :
    HasDerivAt (fun t : ℝ => smoothPicardLiftedFlow n lambda S (t, z))
      (chebyshevLiftedField n lambda S
        (smoothPicardLiftedFlow n lambda S (tau, z))) tau := by
  let z₀ := smoothPicardChartCenter n lambda S (tau, z)
  let C := localPicardCurveBranch n lambda S z₀
  have hpC : (tau, z) ∈ Metric.ball ((0 : ℝ), z₀) C.goodRadius := by
    exact smoothPicardChartCenter_mem_ball hp
  have hraw := C.endpoint_time_hasDerivAt_of_mem_ball hpC
  have hballNhds : {t : ℝ | (t, z) ∈
      Metric.ball ((0 : ℝ), z₀) C.goodRadius} ∈ nhds tau := by
    exact (isOpen_ball.preimage (continuous_id.prodMk continuous_const)).mem_nhds hpC
  have hevent : (fun t : ℝ => smoothPicardLiftedFlow n lambda S (t, z))
      =ᶠ[nhds tau] (fun t : ℝ => C.endpoint (t, z)) := by
    filter_upwards [hballNhds] with t ht
    exact smoothPicardLiftedFlow_eq_endpoint_of_mem_ball ht
  have hresult := hraw.congr_of_eventuallyEq hevent
  apply hresult.congr_deriv
  exact congrArg (chebyshevLiftedField n lambda S)
    (smoothPicardLiftedFlow_eq_endpoint_of_mem_ball hpC).symm

theorem smoothPicardDomain_time_segment_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    (z : ParameterPhaseSpace) {a b : ℝ} (hab : a ≤ b)
    (ha : (a, z) ∈ smoothPicardDomain n lambda S)
    (hb : (b, z) ∈ smoothPicardDomain n lambda S) :
    ∀ t ∈ Set.Icc a b, (t, z) ∈ smoothPicardDomain n lambda S := by
  intro t ht
  have htAbs : |t| ≤ max |a| |b| := abs_le_max_abs_abs ht.1 ht.2
  have ball_mono_time {c : ℝ} {z₀ : ParameterPhaseSpace} {r : ℝ}
      (hc : (c, z) ∈ Metric.ball ((0 : ℝ), z₀) r)
      (htc : |t| ≤ |c|) :
      (t, z) ∈ Metric.ball ((0 : ℝ), z₀) r := by
    rw [Metric.mem_ball, Prod.dist_eq] at hc ⊢
    have hcc : max |c| (dist z z₀) < r := by
      simpa [Real.dist_eq] using hc
    simpa [Real.dist_eq] using lt_of_le_of_lt (max_le_max htc le_rfl) hcc
  rcases le_total |a| |b| with habs | hbas
  · obtain ⟨z₀, hz₀⟩ := Set.mem_iUnion.mp hb
    apply Set.mem_iUnion.mpr
    refine ⟨z₀, ball_mono_time hz₀ ?_⟩
    simpa [max_eq_right habs] using htAbs
  · obtain ⟨z₀, hz₀⟩ := Set.mem_iUnion.mp ha
    apply Set.mem_iUnion.mpr
    refine ⟨z₀, ball_mono_time hz₀ ?_⟩
    simpa [max_eq_left hbas] using htAbs

/-- The lifted Picard endpoint preserves the frozen parameter coordinate. -/
theorem chebyshevPicardResidual_eq_zero_endpoint_fst
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0) :
    (gamma ⟨1, by norm_num⟩).1 = z.1 := by
  let F := chebyshevLiftedODECurveField n lambda S gamma
  let L : ParameterPhaseSpace →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ PhaseSpace
  have hFfirst : ∀ r : ℝ, L (F.clamp r) = 0 := by
    intro r
    simp [L, F, ODECurve.clamp, chebyshevLiftedODECurveField_apply,
      Spikes.parameterLift]
  have hFint : IntervalIntegrable F.clamp volume (0 : ℝ) 1 :=
    F.continuous_clamp.intervalIntegrable _ _
  have hintegral : L (∫ r : ℝ in 0..1, F.clamp r) = 0 := by
    rw [← L.intervalIntegral_comp_comm hFint]
    simp only [hFfirst, intervalIntegral.integral_zero]
  have hintegral' : (∫ r : ℝ in 0..1, F.clamp r).1 = 0 := by
    simpa [L] using hintegral
  have hpoint := chebyshevPicardResidual_eq_zero_apply hzero
    (⟨1, by norm_num⟩ : ODEUnitInterval)
  have hfst := congrArg Prod.fst hpoint
  have hvolterra :
      (unitVolterraCLM (chebyshevLiftedODECurveField n lambda S gamma)
        ⟨1, by norm_num⟩).1 = 0 := by
    change (unitVolterraCLM F ⟨1, by norm_num⟩).1 = 0
    simpa [unitVolterraCLM_apply] using hintegral'
  calc
    (gamma ⟨1, by norm_num⟩).1 =
        (z + tau • unitVolterraCLM
          (chebyshevLiftedODECurveField n lambda S gamma)
            ⟨1, by norm_num⟩).1 := hfst
    _ = z.1 + tau * (unitVolterraCLM
          (chebyshevLiftedODECurveField n lambda S gamma)
            ⟨1, by norm_num⟩).1 := rfl
    _ = z.1 := by rw [hvolterra]; ring

theorem chebyshevPicardResidual_eq_zero_endpoint_of_zero_scale
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z : ParameterPhaseSpace} {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S (((0 : ℝ), z), gamma) = 0) :
    gamma ⟨1, by norm_num⟩ = z := by
  have hpoint := chebyshevPicardResidual_eq_zero_apply hzero
    (⟨1, by norm_num⟩ : ODEUnitInterval)
  simpa [unitVolterraCLM_apply] using hpoint

theorem smoothPicardLiftedFlow_fst
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {p : ℝ × ParameterPhaseSpace}
    (hp : p ∈ smoothPicardDomain n lambda S) :
    (smoothPicardLiftedFlow n lambda S p).1 = p.2.1 := by
  let z₀ := smoothPicardChartCenter n lambda S p
  let C := localPicardCurveBranch n lambda S z₀
  have hpC : p ∈ Metric.ball ((0 : ℝ), z₀) C.goodRadius := by
    exact smoothPicardChartCenter_mem_ball hp
  have hzero := (C.good_of_mem_ball hpC).1
  rw [smoothPicardLiftedFlow_eq_endpoint_of_mem_ball hpC]
  exact chebyshevPicardResidual_eq_zero_endpoint_fst hzero

theorem smoothPicardLiftedFlow_zero
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) :
    smoothPicardLiftedFlow n lambda S ((0 : ℝ), z) = z := by
  have hp := smoothPicardDomain_zero_mem n lambda S z
  let z₀ := smoothPicardChartCenter n lambda S ((0 : ℝ), z)
  let C := localPicardCurveBranch n lambda S z₀
  have hpC : ((0 : ℝ), z) ∈
      Metric.ball ((0 : ℝ), z₀) C.goodRadius := by
    exact smoothPicardChartCenter_mem_ball hp
  have hzero := (C.good_of_mem_ball hpC).1
  rw [smoothPicardLiftedFlow_eq_endpoint_of_mem_ball hpC]
  exact chebyshevPicardResidual_eq_zero_endpoint_of_zero_scale hzero

/-- The same common Picard domain in the argument order used by `C1LocalFlow`. -/
def chebyshevSmoothFlowDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    Set (ParameterPhaseSpace × ℝ) :=
  {p | (p.2, p.1) ∈ smoothPicardDomain n lambda S}

/-- The planar component of the glued lifted Picard endpoint. -/
noncomputable def chebyshevSmoothPlanarFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ParameterPhaseSpace × ℝ → PhaseSpace :=
  fun p => (smoothPicardLiftedFlow n lambda S (p.2, p.1)).2

/-- A genuine jointly `C¹` local flow for the actual degree-audited Chebyshev
polynomial perturbation.  It is constructed from the Banach-space implicit
Picard equation and finite-dimensional ODE uniqueness. -/
noncomputable def chebyshevPolynomialC1LocalFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    C1LocalFlow (fun mu x => chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x) where
  flow := chebyshevSmoothPlanarFlow n lambda S
  domain := chebyshevSmoothFlowDomain n lambda S
  isOpen_domain := by
    exact (isOpen_smoothPicardDomain n lambda S).preimage
      (continuous_snd.prodMk continuous_fst)
  zero_mem := by
    intro mu x
    exact smoothPicardDomain_zero_mem n lambda S (mu, x)
  time_segment_mem := by
    intro mu x a b hab ha hb t ht
    exact smoothPicardDomain_time_segment_mem (mu, x) hab ha hb t ht
  contDiffOn_flow := by
    intro p hp
    have hinput : ContDiffAt ℝ 1 (fun q : ParameterPhaseSpace × ℝ => (q.2, q.1)) p := by
      fun_prop
    have hlift : ContDiffAt ℝ 1 (smoothPicardLiftedFlow n lambda S) (p.2, p.1) :=
      (contDiffOn_smoothPicardLiftedFlow n lambda S _ hp).contDiffAt
        ((isOpen_smoothPicardDomain n lambda S).mem_nhds hp)
    have hcomp : ContDiffAt ℝ 1
        (smoothPicardLiftedFlow n lambda S ∘
          fun q : ParameterPhaseSpace × ℝ => (q.2, q.1)) p :=
      hlift.comp p hinput
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ PhaseSpace).contDiff.contDiffAt.comp p hcomp
    change ContDiffWithinAt ℝ 1
      (fun q : ParameterPhaseSpace × ℝ =>
        (smoothPicardLiftedFlow n lambda S (q.2, q.1)).2)
      (chebyshevSmoothFlowDomain n lambda S) p
    simpa [Function.comp_def] using hsnd.contDiffWithinAt
  initial := by
    intro mu x _
    exact congrArg Prod.snd (smoothPicardLiftedFlow_zero n lambda S (mu, x))
  ode := by
    intro mu x t hp
    have hlift := smoothPicardLiftedFlow_time_hasDerivAt
      (n := n) (lambda := lambda) (S := S) hp
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ PhaseSpace).hasFDerivAt.comp_hasDerivAt
      t hlift
    have hmu : (smoothPicardLiftedFlow n lambda S (t, (mu, x))).1 = mu :=
      smoothPicardLiftedFlow_fst hp
    simpa [chebyshevSmoothPlanarFlow, chebyshevLiftedField,
      Spikes.parameterLift, Function.comp_def, hmu] using hsnd

end Hilbert16
