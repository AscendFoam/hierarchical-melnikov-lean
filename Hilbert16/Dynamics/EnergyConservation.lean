import Hilbert16.Dynamics.ChebyshevReturn
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace Hilbert16

open Hilbert16.Spikes Set
open scoped Topology

/-- Scalar derivative using the real module structure selected by Mathlib's polynomial calculus.
This is definitionally different, but mathematically identical, to the self-module structure that
some other imports select by default. Keeping the choice local prevents instance diamonds. -/
noncomputable abbrev RealInnerHasDerivAt
    (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  HasDerivAt f f' x

/-- Product-valued companion of `RealInnerHasDerivAt`. -/
noncomputable abbrev RealInnerProdHasDerivAt
    (f : ℝ → ℝ × ℝ) (f' : ℝ × ℝ) (x : ℝ) : Prop :=
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : AddCommGroup (ℝ × ℝ) := inferInstance
  letI : Module ℝ (ℝ × ℝ) := inferInstance
  HasDerivAt f f' x

/-- The numerator `2H` of the Chebyshev Hamiltonian. Using it avoids any scalar-instance
bookkeeping in the derivative-zero proof. -/
noncomputable def chebyshevHamiltonianNumerator
    (n : ℕ) (lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.1 ^ 2 +
    lambda * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.2 ^ 2

noncomputable def chebyshevPhaseEnergyNumerator
    (n : ℕ) (lambda : ℝ) (z : PhaseSpace) : ℝ :=
  chebyshevHamiltonianNumerator n lambda (phaseSpaceProdEquiv z)

/-- `2H` has zero derivative along the Chebyshev Hamiltonian vector field. -/
theorem chebyshevHamiltonianNumerator_comp_hasDerivAt_zero
    {n : ℕ} {lambda t : ℝ} {gamma : ℝ → ℝ × ℝ}
    (hgamma : RealInnerProdHasDerivAt gamma
      (chebyshevHamiltonianVector n lambda (gamma t)) t) :
    RealInnerHasDerivAt
      (fun s : ℝ => chebyshevHamiltonianNumerator n lambda (gamma s)) 0 t := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx := (p.hasDerivAt (gamma t).1).comp t hgamma.fst
  have hy := (p.hasDerivAt (gamma t).2).comp t hgamma.snd
  have hsum := (hx.pow 2).add ((hy.pow 2).const_mul lambda)
  have hsum' : RealInnerHasDerivAt
      (fun s : ℝ =>
        p.eval (gamma s).1 ^ 2 + lambda * p.eval (gamma s).2 ^ 2)
      (2 * p.eval (gamma t).1 *
          (p.derivative.eval (gamma t).1 *
            (chebyshevHamiltonianVector n lambda (gamma t)).1) +
        lambda * (2 * p.eval (gamma t).2 *
          (p.derivative.eval (gamma t).2 *
            (chebyshevHamiltonianVector n lambda (gamma t)).2))) t := by
    convert hsum using 1
    · funext s
      simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, pow_two]
    · simp only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        mul_assoc]
  have hzero :
      2 * p.eval (gamma t).1 *
          (p.derivative.eval (gamma t).1 *
            (chebyshevHamiltonianVector n lambda (gamma t)).1) +
        lambda * (2 * p.eval (gamma t).2 *
          (p.derivative.eval (gamma t).2 *
            (chebyshevHamiltonianVector n lambda (gamma t)).2)) = 0 := by
    simp [chebyshevHamiltonianVector, chebyshevHamiltonianDx,
      chebyshevHamiltonianDy, p]
    ring
  rw [hzero] at hsum'
  simpa only [chebyshevHamiltonianNumerator, p] using hsum'

/-- Phase-space version of numerator conservation at the derivative level. -/
theorem chebyshevPhaseEnergyNumerator_comp_hasDerivAt_zero
    {n : ℕ} {lambda t : ℝ} {gamma : ℝ → PhaseSpace}
    (hgamma : HasDerivAt gamma
      (chebyshevPhaseHamiltonianVector n lambda (gamma t)) t) :
    RealInnerHasDerivAt
      (fun s : ℝ => chebyshevPhaseEnergyNumerator n lambda (gamma s)) 0 t := by
  have hout : HasFDerivAt phaseSpaceProdEquiv
      phaseSpaceProdEquiv.toContinuousLinearMap (gamma t) :=
    phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
  have hprod : HasDerivAt (phaseSpaceProdEquiv ∘ gamma)
      (phaseSpaceProdEquiv.toContinuousLinearMap
        (chebyshevPhaseHamiltonianVector n lambda (gamma t))) t :=
    hout.comp_hasDerivAt t hgamma
  have hprod' : RealInnerProdHasDerivAt
      (fun s : ℝ => phaseSpaceProdEquiv (gamma s))
      (chebyshevHamiltonianVector n lambda (phaseSpaceProdEquiv (gamma t))) t := by
    simpa [chebyshevPhaseHamiltonianVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hprod
  exact chebyshevHamiltonianNumerator_comp_hasDerivAt_zero hprod'

theorem chebyshevPhaseEnergy_eq_of_numerator_eq
    {n : ℕ} {lambda : ℝ} {x y : PhaseSpace}
    (h : chebyshevPhaseEnergyNumerator n lambda x =
      chebyshevPhaseEnergyNumerator n lambda y) :
    chebyshevPhaseEnergy n lambda x = chebyshevPhaseEnergy n lambda y := by
  unfold chebyshevPhaseEnergy chebyshevHamiltonian
  apply congrArg (fun q : ℝ => q / 2)
  simpa only [chebyshevPhaseEnergyNumerator, chebyshevHamiltonianNumerator] using h

/-- A real-valued function with zero derivative at every point of `[a,b]` is constant there. -/
theorem eq_left_of_hasDerivAt_zero_on_Icc
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, RealInnerHasDerivAt f 0 t) : f b = f a := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  have hcont : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hright : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f 0 (Set.Ici t) t := by
    intro t ht
    exact (hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hright b ⟨hab, le_rfl⟩

/-- The unperturbed return has zero Hamiltonian-energy displacement whenever its complete time
segment lies in the local-flow domain. This is the exact conservation statement needed before
factoring the displacement by the perturbation parameter. -/
theorem ChebyshevReturnSetup.energyDisplacement_zero_of_unperturbed_segment
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    {h : ℝ} (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2)
    (hT : 0 ≤ S.returnTime.time (0, h))
    (hsegment : ∀ t ∈ Set.Icc 0 (S.returnTime.time (0, h)),
      ((0, chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h), t) ∈
        S.localFlow.domain) :
    S.energyDisplacement (0, h) = 0 := by
  let gamma : ℝ → PhaseSpace := fun t =>
    S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, h), t)
  have hderiv : ∀ t ∈ Set.Icc 0 (S.returnTime.time (0, h)),
      RealInnerHasDerivAt
        (fun s : ℝ => chebyshevPhaseEnergyNumerator S.n S.lambda (gamma s)) 0 t := by
    intro t ht
    apply chebyshevPhaseEnergyNumerator_comp_hasDerivAt_zero
    have hflow := S.localFlow.chebyshevByEnergy_hasDerivAt
      S.n S.i S.j S.lambda 0 h t (hsegment t ht)
    rw [S.unperturbed_eq] at hflow
    simpa [gamma] using hflow
  have hnum := eq_left_of_hasDerivAt_zero_on_Icc hT hderiv
  have henergy :
      chebyshevPhaseEnergy S.n S.lambda
          (gamma (S.returnTime.time (0, h))) =
        chebyshevPhaseEnergy S.n S.lambda (gamma 0) :=
    chebyshevPhaseEnergy_eq_of_numerator_eq hnum
  have hzeroMem :
      ((0, chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h), 0) ∈
        S.localFlow.domain :=
    hsegment 0 ⟨le_rfl, hT⟩
  have hinitial : gamma 0 =
      chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h := by
    exact S.localFlow.chebyshevByEnergy_initial
      S.n S.i S.j S.lambda 0 h hzeroMem
  have hinitialEnergy : chebyshevPhaseEnergy S.n S.lambda (gamma 0) = h := by
    rw [hinitial]
    exact chebyshevPhaseSectionPoint_energy_eq
      S.n_ne_zero S.lambda_ge_one hh hhHalf
  unfold ChebyshevReturnSetup.energyDisplacement
    LocalLevelTime.energyDisplacement LocalLevelTime.returnCoordinate
    LocalLevelTime.returnPoint
  change chebyshevPhaseEnergy S.n S.lambda
      (gamma (S.returnTime.time (0, h))) - h = 0
  rw [henergy, hinitialEnergy]
  ring

/-- At the base orbit, positivity of the genuine return period and interval-connectedness of the
local-flow time domain discharge all segment hypotheses automatically. -/
theorem ChebyshevReturnSetup.energyDisplacement_zero_at_base
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    S.energyDisplacement (0, S.h₀) = 0 := by
  have htime : S.returnTime.time (0, S.h₀) = S.T₀ := by
    simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
  apply S.energyDisplacement_zero_of_unperturbed_segment
    S.h₀_pos.le S.h₀_lt_half.le
  · rw [htime]
    exact S.T₀_pos.le
  · intro t ht
    rw [htime] at ht
    exact S.localFlow.time_segment_mem 0
      (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀)
      S.T₀_pos.le (S.localFlow.zero_mem 0 _) S.return_mem t ht

/-- Energy conservation holds for every nearby unperturbed energy, not just at the base orbit.
Openness supplies the nearby return endpoint, positivity persists by continuity of the IFT time,
and `time_segment_mem` fills the entire orbit segment. -/
theorem ChebyshevReturnSetup.eventually_energyDisplacement_zero_unperturbed
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ∀ᶠ h in 𝓝 S.h₀, S.energyDisplacement (0, h) = 0 := by
  let input : ℝ → ℝ × ℝ := fun h => (0, h)
  let endpoint : ℝ → ParameterPhaseSpace × ℝ := fun h =>
    ((0, chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h),
      S.returnTime.time (0, h))
  have hinput : ContDiffAt ℝ 1 input S.h₀ := by
    dsimp [input]
    fun_prop
  have htime : S.returnTime.time (0, S.h₀) = S.T₀ := by
    simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
  have htimeDiff : ContDiffAt ℝ 1
      (fun h : ℝ => S.returnTime.time (0, h)) S.h₀ :=
    S.returnTime.contDiffAt_time.comp S.h₀ hinput
  have hsectionDiff : ContDiffAt ℝ 1
      (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda) S.h₀ :=
    contDiffAt_chebyshevPhaseSectionPoint S.n S.i S.j S.lambda
      S.h₀_pos S.h₀_lt_half
  have hendpointDiff : ContDiffAt ℝ 1 endpoint S.h₀ := by
    dsimp [endpoint]
    exact (contDiffAt_const.prodMk hsectionDiff).prodMk htimeDiff
  have hendpointBase : endpoint S.h₀ ∈ S.localFlow.domain := by
    simpa [endpoint, htime] using S.return_mem
  have heventEndpoint : ∀ᶠ h in 𝓝 S.h₀,
      endpoint h ∈ S.localFlow.domain :=
    hendpointDiff.continuousAt.tendsto.eventually
      (S.localFlow.isOpen_domain.eventually_mem hendpointBase)
  have heventTime : ∀ᶠ h in 𝓝 S.h₀,
      0 < S.returnTime.time (0, h) := by
    apply continuousAt_const.eventually_lt htimeDiff.continuousAt
    rw [htime]
    exact S.T₀_pos
  have heventPos : ∀ᶠ h in 𝓝 S.h₀, 0 < h :=
    continuousAt_const.eventually_lt continuousAt_id S.h₀_pos
  have heventHalf : ∀ᶠ h in 𝓝 S.h₀, h < 1 / 2 :=
    continuousAt_id.eventually_lt continuousAt_const S.h₀_lt_half
  filter_upwards [heventEndpoint, heventTime, heventPos, heventHalf] with
      h hend hT hh hhHalf
  apply S.energyDisplacement_zero_of_unperturbed_segment hh.le hhHalf.le hT.le
  intro t ht
  exact S.localFlow.time_segment_mem 0
    (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h) hT.le
    (S.localFlow.zero_mem 0 _) hend t ht

end Hilbert16
