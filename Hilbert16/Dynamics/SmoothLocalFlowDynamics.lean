import Hilbert16.Dynamics.SmoothLocalFlow

set_option autoImplicit false

namespace Hilbert16

open Filter Set Metric
open scoped Interval Topology

/-- A zero-residual normalized Picard curve satisfies the rescaled ODE at every interior
normalized time. -/
theorem chebyshevPicardResidual_eq_zero_clamp_hasDerivAt
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt gamma.clamp
      (tau • chebyshevLiftedODECurveField n lambda S gamma
        ⟨t, ht.1.le, ht.2.le⟩) t := by
  let F := chebyshevLiftedODECurveField n lambda S gamma
  have hrawIntegral := (F.continuous_clamp.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hraw : HasDerivAt
      (fun s : ℝ => z + tau • ∫ r : ℝ in 0..s, F.clamp r)
      (tau • F.clamp t) t := by
    exact (hrawIntegral.const_smul tau).const_add z
  have heq : gamma.clamp =ᶠ[𝓝 t]
      (fun s : ℝ => z + tau • ∫ r : ℝ in 0..s, F.clamp r) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hsIcc : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
    have heqPoint := chebyshevPicardResidual_eq_zero_apply hzero
      (⟨s, hsIcc⟩ : ODEUnitInterval)
    simpa [ODECurve.clamp, F, Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hsIcc,
      unitVolterraCLM_apply] using heqPoint
  have hresult := hraw.congr_of_eventuallyEq heq
  apply hresult.congr_deriv
  simp [F, ODECurve.clamp,
    Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) ⟨ht.1.le, ht.2.le⟩]

/-- Rescaling a nonzero normalized Picard curve gives an actual physical-time integral curve. -/
theorem chebyshevPicardResidual_eq_zero_rescale_hasDerivAt
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} (htau : tau ≠ 0) {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0)
    {s : ℝ} (hs : s / tau ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => gamma.clamp (r / tau))
      (Spikes.parameterLift
        (fun mu x => chebyshevPerturbedPhaseVector n lambda
          (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x)
        (gamma.clamp (s / tau))) s := by
  have houter := chebyshevPicardResidual_eq_zero_clamp_hasDerivAt
    hzero hs
  have hinner : HasDerivAt (fun r : ℝ => r / tau) tau⁻¹ s := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id s).mul_const tau⁻¹
  have hcomp := houter.hasFDerivAt.comp_hasDerivAt s hinner
  have hfieldApply := chebyshevLiftedODECurveField_apply n lambda S gamma
    (⟨s / tau, hs.1.le, hs.2.le⟩ : ODEUnitInterval)
  apply (by simpa [Function.comp_def] using hcomp :
    HasDerivAt (fun r : ℝ => gamma.clamp (r / tau))
      (tau⁻¹ • (tau • chebyshevLiftedODECurveField n lambda S gamma
        ⟨s / tau, hs.1.le, hs.2.le⟩)) s).congr_deriv
  rw [smul_smul, inv_mul_cancel₀ htau, one_smul]
  simpa [ODECurve.clamp,
    Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) ⟨hs.1.le, hs.2.le⟩] using
      hfieldApply

/-- The endpoint of the implicit Picard curve branch. -/
noncomputable def LocalPicardCurveBranch.endpoint
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    (ℝ × ParameterPhaseSpace) → ParameterPhaseSpace :=
  fun p => C.curve p ⟨1, by norm_num⟩

@[simp]
theorem LocalPicardCurveBranch.endpoint_base
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    C.endpoint (0, z₀) = z₀ := by
  rw [LocalPicardCurveBranch.endpoint, C.curve_at_base]
  rfl

/-- The local endpoint solution map is `C¹` in physical time and lifted initial state. -/
theorem LocalPicardCurveBranch.contDiffAt_endpoint
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    ContDiffAt ℝ 1 C.endpoint (0, z₀) := by
  unfold LocalPicardCurveBranch.endpoint
  exact (evalODECurveCLM (E := ParameterPhaseSpace) ⟨1, by norm_num⟩).contDiff.contDiffAt.comp
    (0, z₀) C.contDiffAt_curve

/-- Near the base parameter, the selected implicit curve starts at the prescribed state. -/
theorem LocalPicardCurveBranch.eventually_curve_initial
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {z₀ : ParameterPhaseSpace} (C : LocalPicardCurveBranch n lambda S z₀) :
    ∀ᶠ p in 𝓝 (0, z₀), C.curve p ⟨0, by norm_num⟩ = p.2 := by
  filter_upwards [C.eventually_residual_zero] with p hp
  exact chebyshevPicardResidual_eq_zero_initial hp

/-- The finite-dimensional lifted field whose normalized Picard equation was solved above. -/
noncomputable def chebyshevLiftedField
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ParameterPhaseSpace → ParameterPhaseSpace :=
  Spikes.parameterLift
    (fun mu x => chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x)

theorem contDiff_chebyshevLiftedField
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ 1 (chebyshevLiftedField n lambda S) := by
  have hphase : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      chebyshevPerturbedPhaseVector n lambda
        (mvPolynomialProdEval (chebyshevPPolynomial n S)) z.1 z.2) :=
    contDiff_chebyshevPerturbedParameter
      (contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S) 1) n lambda
  change ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
    ((0 : ℝ), chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S)) z.1 z.2))
  exact contDiff_const.prodMk hphase

/-- Two solutions of the lifted Chebyshev polynomial ODE with a common value at an
interior time agree on the whole compact time interval. -/
theorem chebyshevLifted_integralCurve_unique_on_Icc
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {a b t₀ : ℝ} {f g : ℝ → ParameterPhaseSpace}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Ioo a b,
      HasDerivAt f (chebyshevLiftedField n lambda S (f t)) t)
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt g (chebyshevLiftedField n lambda S (g t)) t)
    (hinitial : f t₀ = g t₀) :
    Set.EqOn f g (Set.Icc a b) := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hfcompact : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hfcont
  have hgcompact : IsCompact (g '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hgcont
  obtain ⟨Rf, hRf⟩ :=
    hfcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  obtain ⟨Rg, hRg⟩ :=
    hgcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  let R := max Rf Rg
  have hfmem : ∀ t ∈ Set.Ioo a b,
      f t ∈ closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRf ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩) (le_max_left Rf Rg)
  have hgmem : ∀ t ∈ Set.Ioo a b,
      g t ∈ closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRg ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩) (le_max_right Rf Rg)
  obtain ⟨K, hK⟩ :=
    (contDiff_chebyshevLiftedField n lambda S).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0 : ParameterPhaseSpace) R)
        (isCompact_closedBall _ _)
  exact ODE_solution_unique_of_mem_Icc
    (v := fun _ => chebyshevLiftedField n lambda S)
    (s := fun _ => closedBall (0 : ParameterPhaseSpace) R)
    (K := K) (fun _ _ => hK) ht₀ hfcont hf hfmem hgcont hg hgmem hinitial

/-- At a fixed nonzero physical time scale, a normalized Picard curve has a unique
endpoint.  Thus overlapping implicit-function charts define the same flow germ. -/
theorem chebyshevPicardResidual_endpoint_unique
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma eta : ODECurve ParameterPhaseSpace}
    (hgamma : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0)
    (heta : chebyshevPicardResidual n lambda S ((tau, z), eta) = 0) :
    gamma ⟨1, by norm_num⟩ = eta ⟨1, by norm_num⟩ := by
  rcases eq_or_ne tau 0 with rfl | htau
  · have hg := chebyshevPicardResidual_eq_zero_apply hgamma
      (⟨1, by norm_num⟩ : ODEUnitInterval)
    have he := chebyshevPicardResidual_eq_zero_apply heta
      (⟨1, by norm_num⟩ : ODEUnitInterval)
    have hg' : gamma ⟨1, by norm_num⟩ = z := by
      simpa [unitVolterraCLM_apply] using hg
    have he' : eta ⟨1, by norm_num⟩ = z := by
      simpa [unitVolterraCLM_apply] using he
    exact hg'.trans he'.symm
  · let f : ℝ → ParameterPhaseSpace := fun r => gamma.clamp (r / tau)
    let g : ℝ → ParameterPhaseSpace := fun r => eta.clamp (r / tau)
    have ht₀ : (0 : ℝ) ∈ Set.Ioo (-|tau|) |tau| := by
      simpa using abs_pos.mpr htau
    have hfcont : ContinuousOn f (Set.Icc (-|tau|) |tau|) :=
      (gamma.continuous_clamp.comp (continuous_id.div_const tau)).continuousOn
    have hgcont : ContinuousOn g (Set.Icc (-|tau|) |tau|) :=
      (eta.continuous_clamp.comp (continuous_id.div_const tau)).continuousOn
    have hnormalized {r : ℝ} (hr : r ∈ Set.Ioo (-|tau|) |tau|) :
        r / tau ∈ Set.Ioo (-1 : ℝ) 1 := by
      change -(1 : ℝ) < r / tau ∧ r / tau < 1
      rw [← abs_lt, abs_div, div_lt_one (abs_pos.mpr htau)]
      simpa [abs_lt] using hr
    have hf : ∀ r ∈ Set.Ioo (-|tau|) |tau|,
        HasDerivAt f (chebyshevLiftedField n lambda S (f r)) r := by
      intro r hr
      simpa [f, chebyshevLiftedField] using
        (chebyshevPicardResidual_eq_zero_rescale_hasDerivAt htau hgamma
          (hnormalized hr))
    have hg : ∀ r ∈ Set.Ioo (-|tau|) |tau|,
        HasDerivAt g (chebyshevLiftedField n lambda S (g r)) r := by
      intro r hr
      simpa [g, chebyshevLiftedField] using
        (chebyshevPicardResidual_eq_zero_rescale_hasDerivAt htau heta
          (hnormalized hr))
    have hinitial : f 0 = g 0 := by
      have hgi := chebyshevPicardResidual_eq_zero_initial hgamma
      have hei := chebyshevPicardResidual_eq_zero_initial heta
      dsimp [f, g]
      rw [zero_div]
      have hgclamp : gamma.clamp 0 = z := by
        simpa [ODECurve.clamp,
          Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)] using hgi
      have heclamp : eta.clamp 0 = z := by
        simpa [ODECurve.clamp,
          Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)] using hei
      exact hgclamp.trans heclamp.symm
    have heq := chebyshevLifted_integralCurve_unique_on_Icc
      (n := n) (lambda := lambda) (S := S) ht₀ hfcont hf hgcont hg hinitial
    have htauMem : tau ∈ Set.Icc (-|tau|) |tau| :=
      ⟨neg_abs_le tau, le_abs_self tau⟩
    simpa [f, g, ODECurve.clamp, htau] using heq htauMem

end Hilbert16
