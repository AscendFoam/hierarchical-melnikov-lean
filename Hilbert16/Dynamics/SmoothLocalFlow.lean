import Hilbert16.Dynamics.PolynomialPerturbation
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open Hilbert16.Spikes
open scoped Interval Topology

/-- The fixed normalized time interval used for the Banach-space Picard equation. -/
abbrev ODEUnitInterval := Set.Icc (-1 : ℝ) 1

/-- Continuous curves on the fixed normalized time interval, with the uniform norm. -/
abbrev ODECurve (E : Type*) [TopologicalSpace E] :=
  ContinuousMap ODEUnitInterval E

instance : Nonempty ODEUnitInterval := ⟨⟨0, by norm_num⟩⟩

section CurveOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Apply a continuous linear map pointwise to a normalized-time curve. -/
noncomputable def mapODECurveCLM
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) : ODECurve E →L[ℝ] ODECurve F :=
  LinearMap.mkContinuous
    { toFun := fun gamma =>
        ⟨fun t => L (gamma t), L.continuous.comp gamma.continuous⟩
      map_add' := by intro gamma eta; ext t; simp
      map_smul' := by intro c gamma; ext t; simp }
    ‖L‖ (by
      intro gamma
      rw [ContinuousMap.norm_le_of_nonempty]
      intro t
      exact (L.le_opNorm (gamma t)).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousMap.norm_coe_le_norm gamma t) (norm_nonneg L)))

@[simp]
theorem mapODECurveCLM_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (gamma : ODECurve E) (t : ODEUnitInterval) :
    mapODECurveCLM L gamma t = L (gamma t) := rfl

/-- Pair two normalized-time curves pointwise. -/
noncomputable def pairODECurveCLM
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    (ODECurve E × ODECurve F) →L[ℝ] ODECurve (E × F) :=
  LinearMap.mkContinuous
    { toFun := fun gamma =>
        ⟨fun t => (gamma.1 t, gamma.2 t), gamma.1.continuous.prodMk gamma.2.continuous⟩
      map_add' := by intro gamma eta; ext t <;> rfl
      map_smul' := by intro c gamma; ext t <;> rfl }
    1 (by
      intro gamma
      rw [ContinuousMap.norm_le_of_nonempty]
      intro t
      change max ‖gamma.1 t‖ ‖gamma.2 t‖ ≤ 1 * max ‖gamma.1‖ ‖gamma.2‖
      simp only [one_mul]
      exact max_le_max (ContinuousMap.norm_coe_le_norm gamma.1 t)
        (ContinuousMap.norm_coe_le_norm gamma.2 t))

@[simp]
theorem pairODECurveCLM_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (gamma : ODECurve E × ODECurve F) (t : ODEUnitInterval) :
    pairODECurveCLM gamma t = (gamma.1 t, gamma.2 t) := rfl

/-- Embed a state as the corresponding constant normalized-time curve. -/
noncomputable def constantODECurveCLM : E →L[ℝ] ODECurve E :=
  LinearMap.mkContinuous
    { toFun := fun x => ContinuousMap.const ODEUnitInterval x
      map_add' := by intro x y; ext t; simp
      map_smul' := by intro c x; ext t; simp }
    1 (by
      intro x
      rw [ContinuousMap.norm_le_of_nonempty]
      intro t
      simp)

@[simp]
theorem constantODECurveCLM_apply (x : E) (t : ODEUnitInterval) :
    constantODECurveCLM x t = x := rfl

/-- Evaluation at a fixed normalized time is a continuous linear map. -/
noncomputable def evalODECurveCLM (t : ODEUnitInterval) : ODECurve E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun gamma => gamma t
      map_add' := by intro gamma eta; rfl
      map_smul' := by intro c gamma; rfl }
    1 (fun gamma => by
      change ‖gamma t‖ ≤ 1 * ‖gamma‖
      simpa only [one_mul] using ContinuousMap.norm_coe_le_norm gamma t)

@[simp]
theorem evalODECurveCLM_apply (t : ODEUnitInterval) (gamma : ODECurve E) :
    evalODECurveCLM t gamma = gamma t := rfl

/-- Extend a normalized-time curve constantly outside `[-1,1]`. -/
noncomputable def ODECurve.clamp (gamma : ODECurve E) : ℝ → E :=
  fun t => gamma (Set.projIcc (-1 : ℝ) 1 (by norm_num) t)

theorem ODECurve.continuous_clamp (gamma : ODECurve E) :
    Continuous gamma.clamp :=
  gamma.continuous.comp continuous_projIcc

/-- The Volterra integral of a normalized-time curve. -/
noncomputable def unitVolterraCurve (gamma : ODECurve E) : ODECurve E where
  toFun t := ∫ s : ℝ in 0..(t : ℝ), gamma.clamp s
  continuous_toFun :=
    ((intervalIntegral.differentiable_integral_of_continuous
      gamma.continuous_clamp).continuous).comp
      continuous_subtype_val

@[simp]
theorem unitVolterraCurve_apply (gamma : ODECurve E) (t : ODEUnitInterval) :
    unitVolterraCurve gamma t = ∫ s : ℝ in 0..(t : ℝ), gamma.clamp s := rfl

theorem unitVolterraCurve_add (gamma eta : ODECurve E) :
    unitVolterraCurve (gamma + eta) = unitVolterraCurve gamma + unitVolterraCurve eta := by
  ext t
  simp only [unitVolterraCurve_apply, ODECurve.clamp, ContinuousMap.add_apply]
  exact intervalIntegral.integral_add
    (gamma.continuous_clamp.intervalIntegrable _ _)
    (eta.continuous_clamp.intervalIntegrable _ _)

theorem unitVolterraCurve_smul (c : ℝ) (gamma : ODECurve E) :
    unitVolterraCurve (c • gamma) = c • unitVolterraCurve gamma := by
  ext t
  simp only [unitVolterraCurve_apply, ODECurve.clamp, ContinuousMap.smul_apply]
  exact intervalIntegral.integral_smul c gamma.clamp

/-- Uniform bound for the Volterra operator on the normalized interval. -/
theorem norm_unitVolterraCurve_le (gamma : ODECurve E) :
    ‖unitVolterraCurve gamma‖ ≤ ‖gamma‖ := by
  rw [ContinuousMap.norm_le_of_nonempty]
  intro t
  calc
    ‖unitVolterraCurve gamma t‖
        ≤ ‖gamma‖ * |(t : ℝ) - 0| := by
          rw [unitVolterraCurve_apply]
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          exact ContinuousMap.norm_coe_le_norm gamma _
    _ ≤ ‖gamma‖ := by
      have ht : |(t : ℝ)| ≤ 1 := abs_le.mpr t.2
      simpa only [sub_zero, mul_one] using
        mul_le_mul_of_nonneg_left ht (norm_nonneg gamma)

/-- Continuous linear Volterra integration on normalized-time curves. -/
noncomputable def unitVolterraCLM : ODECurve E →L[ℝ] ODECurve E :=
  LinearMap.mkContinuous
    { toFun := unitVolterraCurve
      map_add' := unitVolterraCurve_add
      map_smul' := unitVolterraCurve_smul }
    1 (by
      intro gamma
      change ‖unitVolterraCurve gamma‖ ≤ 1 * ‖gamma‖
      simpa only [one_mul] using norm_unitVolterraCurve_le gamma)

@[simp]
theorem unitVolterraCLM_apply (gamma : ODECurve E) (t : ODEUnitInterval) :
    unitVolterraCLM gamma t = ∫ s : ℝ in 0..(t : ℝ), gamma.clamp s := rfl

theorem unitVolterraCLM_zero (gamma : ODECurve E) :
    unitVolterraCLM gamma ⟨0, by norm_num⟩ = 0 := by simp

end CurveOperators

section PolynomialCurveField

/-- Evaluate a real polynomial pointwise on a scalar normalized-time curve. -/
noncomputable def polynomialODECurveEval (p : Polynomial ℝ)
    (gamma : ODECurve ℝ) : ODECurve ℝ :=
  p.eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma

@[simp]
theorem polynomialODECurveEval_apply (p : Polynomial ℝ)
    (gamma : ODECurve ℝ) (t : ODEUnitInterval) :
    polynomialODECurveEval p gamma t = p.eval (gamma t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      change (p.eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma) t =
        p.eval (gamma t) at hp
      change (q.eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma) t =
        q.eval (gamma t) at hq
      change ((p + q).eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma) t =
        (p + q).eval (gamma t)
      rw [Polynomial.eval₂_add, ContinuousMap.add_apply,
        Polynomial.eval_add, hp, hq]
  | monomial n a =>
      change ((Polynomial.monomial n a).eval₂
        (algebraMap ℝ (ODECurve ℝ)) gamma) t =
          (Polynomial.monomial n a).eval (gamma t)
      simp

/-- Pointwise polynomial evaluation is smooth on the Banach algebra of scalar curves. -/
theorem contDiff_polynomialODECurveEval (p : Polynomial ℝ) :
    ContDiff ℝ 1 (polynomialODECurveEval p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      change ContDiff ℝ 1 (fun gamma : ODECurve ℝ =>
        p.eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma) at hp
      change ContDiff ℝ 1 (fun gamma : ODECurve ℝ =>
        q.eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma) at hq
      change ContDiff ℝ 1 (fun gamma : ODECurve ℝ =>
        (p + q).eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma)
      simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial n a =>
      change ContDiff ℝ 1 (fun gamma : ODECurve ℝ =>
        (Polynomial.monomial n a).eval₂ (algebraMap ℝ (ODECurve ℝ)) gamma)
      simpa only [Polynomial.eval₂_monomial] using
        (contDiff_const.mul (contDiff_id.pow n) :
          ContDiff ℝ 1 (fun gamma : ODECurve ℝ =>
            algebraMap ℝ (ODECurve ℝ) a * gamma ^ n))

/-- The parameter component of a lifted-state curve. -/
noncomputable def parameterODECurveCLM :
    ODECurve ParameterPhaseSpace →L[ℝ] ODECurve ℝ :=
  mapODECurveCLM (ContinuousLinearMap.fst ℝ ℝ PhaseSpace)

/-- First physical phase coordinate of a lifted-state curve. -/
noncomputable def phaseXODECurveCLM :
    ODECurve ParameterPhaseSpace →L[ℝ] ODECurve ℝ :=
  mapODECurveCLM
    ((ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L
      phaseSpaceProdEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.snd ℝ ℝ PhaseSpace))

/-- Second physical phase coordinate of a lifted-state curve. -/
noncomputable def phaseYODECurveCLM :
    ODECurve ParameterPhaseSpace →L[ℝ] ODECurve ℝ :=
  mapODECurveCLM
    ((ContinuousLinearMap.snd ℝ ℝ ℝ) ∘L
      phaseSpaceProdEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.snd ℝ ℝ PhaseSpace))

@[simp]
theorem parameterODECurveCLM_apply (gamma : ODECurve ParameterPhaseSpace)
    (t : ODEUnitInterval) : parameterODECurveCLM gamma t = (gamma t).1 := rfl

@[simp]
theorem phaseXODECurveCLM_apply (gamma : ODECurve ParameterPhaseSpace)
    (t : ODEUnitInterval) :
    phaseXODECurveCLM gamma t = (phaseSpaceProdEquiv (gamma t).2).1 := rfl

@[simp]
theorem phaseYODECurveCLM_apply (gamma : ODECurve ParameterPhaseSpace)
    (t : ODEUnitInterval) :
    phaseYODECurveCLM gamma t = (phaseSpaceProdEquiv (gamma t).2).2 := rfl

/-- Evaluate a bivariate polynomial pointwise on the physical phase coordinates of a
lifted-state curve. -/
noncomputable def mvPolynomialODECurveEval (p : MvPolynomial (Fin 2) ℝ)
    (gamma : ODECurve ParameterPhaseSpace) : ODECurve ℝ :=
  p.eval₂ (algebraMap ℝ (ODECurve ℝ)) fun i =>
    if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma

@[simp]
theorem mvPolynomialODECurveEval_apply (p : MvPolynomial (Fin 2) ℝ)
    (gamma : ODECurve ParameterPhaseSpace) (t : ODEUnitInterval) :
    mvPolynomialODECurveEval p gamma t =
      mvPolynomialProdEval p (phaseSpaceProdEquiv (gamma t).2) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      change ((MvPolynomial.C a).eval₂ (algebraMap ℝ (ODECurve ℝ)) _) t = _
      simp [mvPolynomialProdEval]
  | add p q hp hq =>
      change (p.eval₂ (algebraMap ℝ (ODECurve ℝ))
        (fun i => if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)) t =
          mvPolynomialProdEval p (phaseSpaceProdEquiv (gamma t).2) at hp
      change (q.eval₂ (algebraMap ℝ (ODECurve ℝ))
        (fun i => if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)) t =
          mvPolynomialProdEval q (phaseSpaceProdEquiv (gamma t).2) at hq
      change ((p + q).eval₂ (algebraMap ℝ (ODECurve ℝ)) _) t =
        mvPolynomialProdEval (p + q) _
      rw [MvPolynomial.eval₂_add, ContinuousMap.add_apply,
        mvPolynomialProdEval_add, hp, hq]
  | mul_X p i hp =>
      change (p.eval₂ (algebraMap ℝ (ODECurve ℝ))
        (fun i => if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)) t =
          mvPolynomialProdEval p (phaseSpaceProdEquiv (gamma t).2) at hp
      change ((p * MvPolynomial.X i).eval₂
        (algebraMap ℝ (ODECurve ℝ)) _) t =
          mvPolynomialProdEval (p * MvPolynomial.X i) _
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        ContinuousMap.mul_apply, mvPolynomialProdEval_mul, hp]
      fin_cases i <;> simp [mvPolynomialProdEval]

/-- The pointwise bivariate polynomial operator on lifted-state curves is smooth. -/
theorem contDiff_mvPolynomialODECurveEval (p : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ 1 (mvPolynomialODECurveEval p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        (MvPolynomial.C a).eval₂ (algebraMap ℝ (ODECurve ℝ)) fun i =>
          if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)
      simpa only [MvPolynomial.eval₂_C] using
        (contDiff_const : ContDiff ℝ 1
          (fun _ : ODECurve ParameterPhaseSpace => algebraMap ℝ (ODECurve ℝ) a))
  | add p q hp hq =>
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        p.eval₂ (algebraMap ℝ (ODECurve ℝ)) fun i =>
          if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma) at hp
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        q.eval₂ (algebraMap ℝ (ODECurve ℝ)) fun i =>
          if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma) at hq
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        (p + q).eval₂ (algebraMap ℝ (ODECurve ℝ)) fun i =>
          if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)
      simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp =>
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        p.eval₂ (algebraMap ℝ (ODECurve ℝ)) fun j =>
          if j = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma) at hp
      have hi : ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
          if i = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma) := by
        split_ifs <;> fun_prop
      change ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
        (p * MvPolynomial.X i).eval₂ (algebraMap ℝ (ODECurve ℝ)) fun j =>
          if j = 0 then phaseXODECurveCLM gamma else phaseYODECurveCLM gamma)
      simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul hi

/-- Apply the actual parameter-lifted Chebyshev polynomial vector field pointwise to a
normalized-time curve. -/
noncomputable def chebyshevLiftedODECurveField
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (gamma : ODECurve ParameterPhaseSpace) : ODECurve ParameterPhaseSpace := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  let x := phaseXODECurveCLM gamma
  let y := phaseYODECurveCLM gamma
  let mu := parameterODECurveCLM gamma
  let P := mvPolynomialODECurveEval (chebyshevPPolynomial n S) gamma
  let vx := (algebraMap ℝ (ODECurve ℝ) lambda) *
      polynomialODECurveEval p y * polynomialODECurveEval p.derivative y + mu * P
  let vy := -(polynomialODECurveEval p x * polynomialODECurveEval p.derivative x)
  exact pairODECurveCLM
    (0, mapODECurveCLM phaseSpaceProdEquiv.symm.toContinuousLinearMap
      (pairODECurveCLM (vx, vy)))

@[simp]
theorem chebyshevLiftedODECurveField_apply
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (gamma : ODECurve ParameterPhaseSpace) (t : ODEUnitInterval) :
    chebyshevLiftedODECurveField n lambda S gamma t =
      Spikes.parameterLift
        (fun mu x => chebyshevPerturbedPhaseVector n lambda
          (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x) (gamma t) := by
  apply Prod.ext
  · rfl
  · apply phaseSpaceProdEquiv.injective
    simp [chebyshevLiftedODECurveField, Spikes.parameterLift,
      chebyshevPerturbedPhaseVector, chebyshevPerturbedVector,
      chebyshevHamiltonianDx, chebyshevHamiltonianDy]

/-- Smoothness of the actual polynomial Nemytskii operator on normalized-time curves. -/
theorem contDiff_chebyshevLiftedODECurveField
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ 1 (chebyshevLiftedODECurveField n lambda S) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx : ContDiff ℝ 1 (phaseXODECurveCLM :
      ODECurve ParameterPhaseSpace → ODECurve ℝ) := phaseXODECurveCLM.contDiff
  have hy : ContDiff ℝ 1 (phaseYODECurveCLM :
      ODECurve ParameterPhaseSpace → ODECurve ℝ) := phaseYODECurveCLM.contDiff
  have hmu : ContDiff ℝ 1 (parameterODECurveCLM :
      ODECurve ParameterPhaseSpace → ODECurve ℝ) := parameterODECurveCLM.contDiff
  have hpx := (contDiff_polynomialODECurveEval p).comp hx
  have hpy := (contDiff_polynomialODECurveEval p).comp hy
  have hpdx := (contDiff_polynomialODECurveEval p.derivative).comp hx
  have hpdy := (contDiff_polynomialODECurveEval p.derivative).comp hy
  have hP := contDiff_mvPolynomialODECurveEval (chebyshevPPolynomial n S)
  have hvx : ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
      (algebraMap ℝ (ODECurve ℝ) lambda) * polynomialODECurveEval p
          (phaseYODECurveCLM gamma) *
        polynomialODECurveEval p.derivative (phaseYODECurveCLM gamma) +
          parameterODECurveCLM gamma *
            mvPolynomialODECurveEval (chebyshevPPolynomial n S) gamma) :=
    ((contDiff_const.mul hpy).mul hpdy).add (hmu.mul hP)
  have hvy : ContDiff ℝ 1 (fun gamma : ODECurve ParameterPhaseSpace =>
      -(polynomialODECurveEval p (phaseXODECurveCLM gamma) *
        polynomialODECurveEval p.derivative (phaseXODECurveCLM gamma))) :=
    (hpx.mul hpdx).neg
  unfold chebyshevLiftedODECurveField
  dsimp only
  have hvpair :=
    (pairODECurveCLM (E := ℝ) (F := ℝ)).contDiff.comp (hvx.prodMk hvy)
  have hphase :=
    (mapODECurveCLM phaseSpaceProdEquiv.symm.toContinuousLinearMap).contDiff.comp hvpair
  have htotal := (pairODECurveCLM (E := ℝ) (F := PhaseSpace)).contDiff.comp
    ((contDiff_const : ContDiff ℝ 1
      (fun _ : ODECurve ParameterPhaseSpace => (0 : ODECurve ℝ))).prodMk hphase)
  convert htotal using 1
  funext gamma
  rfl

end PolynomialCurveField

section PicardImplicitBranch

/-- The normalized-time Picard residual.  The first parameter is the physical time scale,
the second is the lifted initial state, and the final variable is the normalized curve. -/
noncomputable def chebyshevPicardResidual
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ((ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace) →
      ODECurve ParameterPhaseSpace :=
  fun w => w.2 - constantODECurveCLM w.1.2 -
    w.1.1 • unitVolterraCLM (chebyshevLiftedODECurveField n lambda S w.2)

set_option maxHeartbeats 1600000 in
/-- The normalized Picard residual is `C¹` jointly in time scale, initial state, and curve. -/
theorem contDiff_chebyshevPicardResidual
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ 1 (chebyshevPicardResidual n lambda S) := by
  unfold chebyshevPicardResidual
  have hfield := contDiff_chebyshevLiftedODECurveField n lambda S
  have hcurve : ContDiff ℝ 1 (fun w :
      (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace => w.2) := by
    fun_prop
  have hstate : ContDiff ℝ 1 (fun w :
      (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace => w.1.2) := by
    fun_prop
  have hscale : ContDiff ℝ 1 (fun w :
      (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace => w.1.1) := by
    fun_prop
  have hint : ContDiff ℝ 1 (fun w :
      (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace =>
      unitVolterraCLM (chebyshevLiftedODECurveField n lambda S w.2)) :=
    by
      have hcomp := unitVolterraCLM.contDiff.comp (hfield.comp hcurve)
      convert hcomp using 1
      funext w
      rfl
  exact (hcurve.sub (constantODECurveCLM.contDiff.comp hstate)).sub
    (hscale.smul hint)

@[simp]
theorem chebyshevPicardResidual_zero_scale
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) (gamma : ODECurve ParameterPhaseSpace) :
    chebyshevPicardResidual n lambda S ((0, z), gamma) =
      gamma - constantODECurveCLM z := by
  simp [chebyshevPicardResidual]

@[simp]
theorem chebyshevPicardResidual_base
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) :
    chebyshevPicardResidual n lambda S
      ((0, z), constantODECurveCLM z) = 0 := by
  simp

/-- A zero Picard residual is the normalized integral equation, pointwise in time. -/
theorem chebyshevPicardResidual_eq_zero_apply
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0)
    (t : ODEUnitInterval) :
    gamma t = z + tau •
      unitVolterraCLM (chebyshevLiftedODECurveField n lambda S gamma) t := by
  have ht := DFunLike.congr_fun hzero t
  change gamma t - z - tau •
    unitVolterraCLM (chebyshevLiftedODECurveField n lambda S gamma) t = 0 at ht
  have hsub : gamma t - z = tau •
      unitVolterraCLM (chebyshevLiftedODECurveField n lambda S gamma) t :=
    sub_eq_zero.mp ht
  rw [sub_eq_iff_eq_add] at hsub
  simpa only [add_comm] using hsub

/-- Every zero-residual Picard curve starts at its prescribed lifted state. -/
theorem chebyshevPicardResidual_eq_zero_initial
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {tau : ℝ} {z : ParameterPhaseSpace}
    {gamma : ODECurve ParameterPhaseSpace}
    (hzero : chebyshevPicardResidual n lambda S ((tau, z), gamma) = 0) :
    gamma ⟨0, by norm_num⟩ = z := by
  simpa using chebyshevPicardResidual_eq_zero_apply hzero ⟨0, by norm_num⟩

/-- At zero time scale the curve-direction derivative of the Picard residual is the identity. -/
theorem chebyshevPicardResidual_partial_curve
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) :
    fderiv ℝ (chebyshevPicardResidual n lambda S)
        ((0, z), constantODECurveCLM z) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ParameterPhaseSpace)
        (ODECurve ParameterPhaseSpace) =
      ContinuousLinearMap.id ℝ (ODECurve ParameterPhaseSpace) := by
  let u : (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace :=
    ((0, z), constantODECurveCLM z)
  have hR : ContDiffAt ℝ 1 (chebyshevPicardResidual n lambda S) u :=
    (contDiff_chebyshevPicardResidual n lambda S).contDiffAt
  have hfromR : HasFDerivAt
      (fun gamma : ODECurve ParameterPhaseSpace =>
        chebyshevPicardResidual n lambda S ((0, z), gamma))
      (fderiv ℝ (chebyshevPicardResidual n lambda S) u ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ParameterPhaseSpace)
          (ODECurve ParameterPhaseSpace))
      (constantODECurveCLM z) := by
    have hcomp :=
      ((hR.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp
        (constantODECurveCLM z)
          (hasFDerivAt_prodMk_right (0, z) (constantODECurveCLM z)))
    change HasFDerivAt
      (fun gamma : ODECurve ParameterPhaseSpace =>
        chebyshevPicardResidual n lambda S ((0, z), gamma))
      (fderiv ℝ (chebyshevPicardResidual n lambda S)
          ((0, z), constantODECurveCLM z) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ParameterPhaseSpace)
          (ODECurve ParameterPhaseSpace))
      (constantODECurveCLM z) at hcomp
    exact hcomp
  have hid : HasFDerivAt
      (fun gamma : ODECurve ParameterPhaseSpace =>
        chebyshevPicardResidual n lambda S ((0, z), gamma))
      (ContinuousLinearMap.id ℝ (ODECurve ParameterPhaseSpace))
      (constantODECurveCLM z) := by
    simpa only [chebyshevPicardResidual, zero_smul, sub_zero, Function.id_def] using
      (hasFDerivAt_id (x := constantODECurveCLM z)).sub_const
        (constantODECurveCLM z)
  exact hfromR.unique hid

/-- The curve-direction derivative of the zero-scale Picard residual is invertible. -/
theorem chebyshevPicardResidual_partial_curve_isInvertible
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : ParameterPhaseSpace) :
    (fderiv ℝ (chebyshevPicardResidual n lambda S)
        ((0, z), constantODECurveCLM z) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ParameterPhaseSpace)
        (ODECurve ParameterPhaseSpace)).IsInvertible := by
  rw [chebyshevPicardResidual_partial_curve]
  exact ⟨ContinuousLinearEquiv.refl ℝ (ODECurve ParameterPhaseSpace), rfl⟩

/-- Local `C¹` family of normalized Picard curves through a lifted initial state. -/
structure LocalPicardCurveBranch
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z₀ : ParameterPhaseSpace) where
  curve : (ℝ × ParameterPhaseSpace) → ODECurve ParameterPhaseSpace
  curve_at_base : curve (0, z₀) = constantODECurveCLM z₀
  contDiffAt_curve : ContDiffAt ℝ 1 curve (0, z₀)
  eventually_residual_zero : ∀ᶠ p in 𝓝 (0, z₀),
    chebyshevPicardResidual n lambda S (p, curve p) = 0
  eventually_unique : ∀ᶠ w in 𝓝
      (((0, z₀), constantODECurveCLM z₀) :
        (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace),
    chebyshevPicardResidual n lambda S w = 0 ↔ curve w.1 = w.2

/-- Banach-space implicit-function construction of the local normalized Picard branch. -/
noncomputable def localPicardCurveBranch
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z₀ : ParameterPhaseSpace) : LocalPicardCurveBranch n lambda S z₀ := by
  let R := chebyshevPicardResidual n lambda S
  let u : (ℝ × ParameterPhaseSpace) × ODECurve ParameterPhaseSpace :=
    ((0, z₀), constantODECurveCLM z₀)
  have hR : ContDiffAt ℝ 1 R u :=
    (contDiff_chebyshevPicardResidual n lambda S).contDiffAt
  have hinv :
      (fderiv ℝ R u ∘L ContinuousLinearMap.inr ℝ
        (ℝ × ParameterPhaseSpace) (ODECurve ParameterPhaseSpace)).IsInvertible := by
    exact chebyshevPicardResidual_partial_curve_isInvertible n lambda S z₀
  let psi := hR.implicitFunction one_ne_zero hinv
  refine
    { curve := psi
      curve_at_base := ?_
      contDiffAt_curve := hR.contDiffAt_implicitFunction one_ne_zero hinv
      eventually_residual_zero := ?_
      eventually_unique := ?_ }
  · exact hR.implicitFunction_apply_self one_ne_zero hinv
  · filter_upwards [hR.eventually_apply_implicitFunction one_ne_zero hinv] with p hp
    simpa [R, u, chebyshevPicardResidual_base] using hp
  · simpa [R, u, psi, chebyshevPicardResidual_base] using
      hR.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv

end PicardImplicitBranch

end Hilbert16
