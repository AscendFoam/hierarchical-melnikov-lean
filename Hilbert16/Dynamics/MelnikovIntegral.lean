import Hilbert16.Dynamics.EnergyConservation
import Hilbert16.Dynamics.NormalizedDisplacement
import Hilbert16.Dynamics.ParametricIntegralC1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

set_option autoImplicit false

namespace Hilbert16

open Set
open scoped Interval

/-- The normalized displacement defined without division: integrate the
energy production rate with the perturbation parameter removed. -/
noncomputable def ChebyshevReturnSetup.melnikovIntegral
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (Q : PhaseSpace → ℝ) (muh : ℝ × ℝ) : ℝ :=
  ∫ t in 0..S.returnTime.time muh,
    Q (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda (muh, t))

/-- The scalar energy return map associated with the constructed hitting
time. -/
noncomputable def ChebyshevReturnSetup.energyReturnMap
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (mu h : ℝ) : ℝ :=
  h + S.energyDisplacement (mu, h)

theorem ChebyshevReturnSetup.energyReturnMap_eq_returnCoordinate
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (mu h : ℝ) :
    S.energyReturnMap mu h =
      S.returnTime.returnCoordinate
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
        (chebyshevPhaseEnergy S.n S.lambda) (mu, h) := by
  unfold ChebyshevReturnSetup.energyReturnMap ChebyshevReturnSetup.energyDisplacement
    LocalLevelTime.energyDisplacement
  ring

/-- Exact integral factorization of the genuine return displacement.
The hypothesis is the differential energy identity along the actual
perturbed flow; FTC then gives `Delta(mu,h)=mu*D(mu,h)` with no quotient or
remainder. -/
theorem ChebyshevReturnSetup.energyDisplacement_eq_mu_mul_melnikovIntegral
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (Q : PhaseSpace → ℝ) {mu h : ℝ}
    (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2)
    (hsegment : ∀ t ∈ Set.uIcc 0 (S.returnTime.time (mu, h)),
      ((mu, chebyshevPhaseSectionPoint
          S.n S.i S.j S.lambda h), t) ∈ S.localFlow.domain)
    (hQcont : ContinuousOn
      (fun t : ℝ => Q (S.localFlow.chebyshevByEnergy
        S.n S.i S.j S.lambda ((mu, h), t)))
      (Set.uIcc 0 (S.returnTime.time (mu, h))))
    (henergyDeriv : ∀ t ∈ Set.uIcc 0 (S.returnTime.time (mu, h)),
      HasDerivAt
        (fun s : ℝ => chebyshevPhaseEnergy S.n S.lambda
          (S.localFlow.chebyshevByEnergy
            S.n S.i S.j S.lambda ((mu, h), s)))
        (mu * Q (S.localFlow.chebyshevByEnergy
          S.n S.i S.j S.lambda ((mu, h), t))) t) :
    S.energyDisplacement (mu, h) =
      mu * S.melnikovIntegral Q (mu, h) := by
  let gamma : ℝ → PhaseSpace := fun t =>
    S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((mu, h), t)
  have hQint : IntervalIntegrable (fun t => Q (gamma t)) MeasureTheory.volume
      0 (S.returnTime.time (mu, h)) := by
    exact hQcont.intervalIntegrable
  have hmulInt : IntervalIntegrable (fun t => mu * Q (gamma t)) MeasureTheory.volume
      0 (S.returnTime.time (mu, h)) := hQint.const_mul mu
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt henergyDeriv hmulInt
  rw [intervalIntegral.integral_const_mul] at hftc
  have hzeroMem :
      ((mu, chebyshevPhaseSectionPoint
          S.n S.i S.j S.lambda h), 0) ∈ S.localFlow.domain :=
    hsegment 0 Set.left_mem_uIcc
  have hinitial : gamma 0 =
      chebyshevPhaseSectionPoint S.n S.i S.j S.lambda h := by
    exact S.localFlow.chebyshevByEnergy_initial
      S.n S.i S.j S.lambda mu h hzeroMem
  have hinitialEnergy : chebyshevPhaseEnergy S.n S.lambda (gamma 0) = h := by
    rw [hinitial]
    exact chebyshevPhaseSectionPoint_energy_eq
      S.n_ne_zero S.lambda_ge_one hh hhHalf
  unfold ChebyshevReturnSetup.energyDisplacement LocalLevelTime.energyDisplacement
    LocalLevelTime.returnCoordinate LocalLevelTime.returnPoint
    ChebyshevReturnSetup.melnikovIntegral
  change chebyshevPhaseEnergy S.n S.lambda
      (gamma (S.returnTime.time (mu, h))) - h =
    mu * ∫ t in 0..S.returnTime.time (mu, h), Q (gamma t)
  calc
    chebyshevPhaseEnergy S.n S.lambda
        (gamma (S.returnTime.time (mu, h))) - h =
      chebyshevPhaseEnergy S.n S.lambda
        (gamma (S.returnTime.time (mu, h))) -
          chebyshevPhaseEnergy S.n S.lambda (gamma 0) := by rw [hinitialEnergy]
    _ = mu * ∫ t in 0..S.returnTime.time (mu, h), Q (gamma t) := by
      simpa [gamma] using hftc.symm

/-- At zero perturbation the normalized integral is definitionally the
time integral along the unperturbed return orbit. -/
theorem ChebyshevReturnSetup.melnikovIntegral_zero
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (Q : PhaseSpace → ℝ) (h : ℝ) :
    S.melnikovIntegral Q (0, h) =
      ∫ t in 0..S.returnTime.time (0, h),
        Q (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, h), t)) := by
  rfl

/-- The normalized Melnikov displacement is jointly `C¹` at the base
parameter and energy.  Only the genuine local-flow domain along the compact
unperturbed return segment is used; no global smoothness or global existence
of the flow is required. -/
theorem ChebyshevReturnSetup.contDiffAt_melnikovIntegral
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (Q : PhaseSpace → ℝ) (hQ : ContDiff ℝ 1 Q) :
    ContDiffAt ℝ 1 (S.melnikovIntegral Q) (0, S.h₀) := by
  let input : ((ℝ × ℝ) × ℝ) → ParameterPhaseSpace × ℝ := fun z ↦
    ((z.1.1, chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda z.1.2), z.2)
  let U : Set ((ℝ × ℝ) × ℝ) :=
    ((fun z : ((ℝ × ℝ) × ℝ) ↦ z.1.2) ⁻¹' Set.Ioo 0 (1 / 2)) ∩
      input ⁻¹' S.localFlow.domain
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hh : 0 < z.1.2 := hz.1.1
    have hhHalf : z.1.2 < 1 / 2 := hz.1.2
    have hsection := contDiffAt_chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda hh hhHalf
    have hinput : ContDiffAt ℝ 1 input z := by
      exact (contDiffAt_fst.fst.prodMk
        (hsection.comp z (contDiffAt_fst.snd))).prodMk contDiffAt_snd
    exact Filter.inter_mem
      ((isOpen_Ioo.preimage (by fun_prop)).mem_nhds hz.1)
      (hinput.continuousAt (S.localFlow.isOpen_domain.mem_nhds hz.2))
  let f : (ℝ × ℝ) → ℝ → ℝ := fun muh t ↦
    Q (S.localFlow.chebyshevByEnergy
      S.n S.i S.j S.lambda (muh, t))
  have hf : ContDiffOn ℝ 1 f.uncurry U := by
    intro z hz
    have hflow := S.localFlow.contDiffAt_chebyshevByEnergy
      S.n S.i S.j S.lambda hz.1.1 hz.1.2 hz.2
    change ContDiffWithinAt ℝ 1
      (fun z : ((ℝ × ℝ) × ℝ) ↦
        Q (S.localFlow.chebyshevByEnergy
          S.n S.i S.j S.lambda z)) U z
    exact (hQ.contDiffAt.comp z hflow).contDiffWithinAt
  have htime : S.returnTime.time (0, S.h₀) = S.T₀ := by
    simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
  have hsegment : ({(0, S.h₀)} : Set (ℝ × ℝ)) ×ˢ
      Set.uIcc 0 (S.returnTime.time (0, S.h₀)) ⊆ U := by
    rintro ⟨muh, t⟩ ⟨hmuh, ht⟩
    have hmuh : muh = (0, S.h₀) := Set.mem_singleton_iff.mp hmuh
    subst muh
    have htIcc : t ∈ Set.Icc 0 S.T₀ := by
      rw [htime, uIcc_of_le S.T₀_pos.le] at ht
      exact ht
    have hzero : ((0, chebyshevPhaseSectionPoint
        S.n S.i S.j S.lambda S.h₀), 0) ∈ S.localFlow.domain :=
      S.localFlow.zero_mem 0 _
    have htDomain : ((0, chebyshevPhaseSectionPoint
        S.n S.i S.j S.lambda S.h₀), t) ∈ S.localFlow.domain :=
      S.localFlow.time_segment_mem 0 _ S.T₀_pos.le hzero S.return_mem t htIcc
    exact ⟨⟨S.h₀_pos, S.h₀_lt_half⟩, htDomain⟩
  change ContDiffAt ℝ 1
    (fun muh : ℝ × ℝ ↦ ∫ t in 0..S.returnTime.time muh, f muh t)
    (0, S.h₀)
  exact contDiffAt_parametricIntervalIntegral_of_contDiffOn
    f S.returnTime.time hU hf S.returnTime.contDiffAt_time hsegment

/-- Once the exact factorization holds, the genuine energy return map is
exactly the normalized return map already used by the simple-root theorem. -/
theorem ChebyshevReturnSetup.energyReturnMap_eq_normalizedReturnMap
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    {Q : PhaseSpace → ℝ} {mu h : ℝ}
    (hfactor : S.energyDisplacement (mu, h) =
      mu * S.melnikovIntegral Q (mu, h)) :
    S.energyReturnMap mu h = normalizedReturnMap (S.melnikovIntegral Q) mu h := by
  unfold ChebyshevReturnSetup.energyReturnMap normalizedReturnMap
  rw [hfactor]

end Hilbert16
