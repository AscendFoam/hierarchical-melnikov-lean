import Hilbert16.Dynamics.ChebyshevExplicitReturn
import Hilbert16.Dynamics.PerturbedEnergy
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false

namespace Hilbert16

open Set Metric
open Hilbert16.Spikes

theorem contDiff_chebyshevHamiltonianVector (n : ℕ) (lambda : ℝ) :
    ContDiff ℝ 1 (chebyshevHamiltonianVector n lambda) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hp : ContDiff ℝ 1 (fun x : ℝ => p.eval x) :=
    contDiff_realPolynomial_eval p
  have hpd : ContDiff ℝ 1 (fun x : ℝ => p.derivative.eval x) :=
    contDiff_realPolynomial_eval p.derivative
  have hx : ContDiff ℝ 1 (fun z : ℝ × ℝ => p.eval z.1) :=
    hp.comp contDiff_fst
  have hy : ContDiff ℝ 1 (fun z : ℝ × ℝ => p.eval z.2) :=
    hp.comp contDiff_snd
  have hxd : ContDiff ℝ 1 (fun z : ℝ × ℝ => p.derivative.eval z.1) :=
    hpd.comp contDiff_fst
  have hyd : ContDiff ℝ 1 (fun z : ℝ × ℝ => p.derivative.eval z.2) :=
    hpd.comp contDiff_snd
  unfold chebyshevHamiltonianVector chebyshevHamiltonianDx
    chebyshevHamiltonianDy
  exact ((contDiff_const.mul hy).mul hyd).prodMk (hx.mul hxd).neg

/-- Any genuine local flow for the unperturbed Chebyshev field agrees, over a
full section period contained in its domain, with the explicit section-clock
solution. -/
theorem C1LocalFlow.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain) :
    Set.EqOn
      (fun t => phaseSpaceProdEquiv
        (Phi.chebyshevByEnergy n i j lambda ((0, h), t)))
      (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh.le hhHalf)
      (Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h)) := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : AddCommGroup (ℝ × ℝ) := inferInstance
  letI : Module ℝ (ℝ × ℝ) := inferInstance
  let period := chebyshevHamiltonianSectionPeriod n i j lambda h
  let base := chebyshevPhaseSectionPoint n i j lambda h
  let gamma : ℝ → PhaseSpace := fun t => Phi.flow ((0, base), t)
  let f : ℝ → ℝ × ℝ := fun t => phaseSpaceProdEquiv (gamma t)
  let g : ℝ → ℝ × ℝ :=
    chebyshevHamiltonianSectionTimeOrbit
      hn hi hj hlambda hh.le hhHalf
  have hperiod : 0 < period :=
    chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh.le hhHalf
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) period,
      RealInnerProdHasDerivAt f
        (chebyshevHamiltonianVector n lambda (f t)) t := by
    intro t ht
    have hgamma : HasDerivAt gamma
        (chebyshevPhaseHamiltonianVector n lambda (gamma t)) t := by
      have hode := Phi.ode 0 base t (hsegment t (by simpa [period] using ht))
      rw [hX] at hode
      simpa [gamma, base] using hode
    have hout : HasFDerivAt phaseSpaceProdEquiv
        phaseSpaceProdEquiv.toContinuousLinearMap (gamma t) :=
      phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
    have hprod : HasDerivAt (phaseSpaceProdEquiv ∘ gamma)
        (phaseSpaceProdEquiv.toContinuousLinearMap
          (chebyshevPhaseHamiltonianVector n lambda (gamma t))) t :=
      hout.comp_hasDerivAt t hgamma
    simpa [f, chebyshevPhaseHamiltonianVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hprod
  have hgderiv : ∀ t ∈ Set.Icc (0 : ℝ) period,
      RealInnerProdHasDerivAt g
        (chebyshevHamiltonianVector n lambda (g t)) t := by
    intro t ht
    have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh.le hhHalf
    have htPadded : t ∈ Set.Ioo
        (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
        (chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1)) := by
      constructor
      · calc
          chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) < 0 := by
            rw [← chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
            exact hmono (by norm_num)
          _ ≤ t := ht.1
      · calc
          t ≤ period := ht.2
          _ = chebyshevHamiltonianSectionAngularTime n i j lambda h
              (2 * Real.pi) := rfl
          _ < chebyshevHamiltonianSectionAngularTime n i j lambda h
              (2 * Real.pi + 1) := hmono (by norm_num)
    exact (chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt_of_padded_mem
      hn hi hj hlambda hh.le hhHalf htPadded).prodMk
      (chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt_of_padded_mem
        hn hi hj hlambda hh.le hhHalf htPadded)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) period) :=
    HasDerivAt.continuousOn hfderiv
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) period) :=
    HasDerivAt.continuousOn hgderiv
  have hfcompact : IsCompact (f '' Set.Icc (0 : ℝ) period) :=
    isCompact_Icc.image_of_continuousOn hfcont
  have hgcompact : IsCompact (g '' Set.Icc (0 : ℝ) period) :=
    isCompact_Icc.image_of_continuousOn hgcont
  obtain ⟨Rf, hRf⟩ := hfcompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨Rg, hRg⟩ := hgcompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let R := max Rf Rg
  have hfmem : ∀ t ∈ Set.Icc (0 : ℝ) period, f t ∈ closedBall (0 : ℝ × ℝ) R := by
    intro t ht
    exact le_trans (hRf ⟨t, ht, rfl⟩) (le_max_left Rf Rg)
  have hgmem : ∀ t ∈ Set.Icc (0 : ℝ) period, g t ∈ closedBall (0 : ℝ × ℝ) R := by
    intro t ht
    exact le_trans (hRg ⟨t, ht, rfl⟩) (le_max_right Rf Rg)
  obtain ⟨K, hK⟩ :=
    (contDiff_chebyshevHamiltonianVector n lambda).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0 : ℝ × ℝ) R) (isCompact_closedBall _ _)
  have hinitial : f 0 = g 0 := by
    have hgamma0 : gamma 0 = base := by
      exact Phi.initial 0 base (Phi.zero_mem 0 base)
    rw [show f 0 = phaseSpaceProdEquiv base by simp [f, gamma, hgamma0]]
    simp [g, base, chebyshevPhaseSectionPoint, chebyshevPhaseOrbit]
  have heq : Set.EqOn f g (Set.Icc (0 : ℝ) period) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => chebyshevHamiltonianVector n lambda)
      (s := fun _ => closedBall (0 : ℝ × ℝ) R)
      (K := K)
      (fun _ _ => hK) hfcont
      (fun t ht => (hfderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hfmem t (Ico_subset_Icc_self ht)) hgcont
      (fun t ht => (hgderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hgmem t (Ico_subset_Icc_self ht)) hinitial
  intro t ht
  simpa [f, g, gamma, base, period, C1LocalFlow.chebyshevByEnergy] using heq ht

/-- Endpoint consequence of trajectory identification: the genuine flow
returns to the chosen section base after the explicit strictly positive
Hamiltonian period. -/
theorem C1LocalFlow.chebyshevUnperturbed_returns_after_sectionPeriod
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain) :
    Phi.chebyshevByEnergy n i j lambda
        ((0, h), chebyshevHamiltonianSectionPeriod n i j lambda h) =
      chebyshevPhaseSectionPoint n i j lambda h := by
  apply phaseSpaceProdEquiv.injective
  have htraj := Phi.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
    hn hi hj hlambda hh hhHalf hX hsegment
      ⟨(chebyshevHamiltonianSectionPeriod_pos
        hn hi hj hlambda hh.le hhHalf).le, le_rfl⟩
  calc
    phaseSpaceProdEquiv (Phi.chebyshevByEnergy n i j lambda
        ((0, h), chebyshevHamiltonianSectionPeriod n i j lambda h)) =
        chebyshevHamiltonianSectionTimeOrbit
          hn hi hj hlambda hh.le hhHalf
            (chebyshevHamiltonianSectionPeriod n i j lambda h) := htraj
    _ = phaseSpaceProdEquiv (chebyshevPhaseSectionPoint n i j lambda h) := by
      simp [chebyshevPhaseSectionPoint, chebyshevPhaseOrbit]

/-- Build the exact return-map setup from a genuine local flow once its domain
contains the explicit unperturbed section-period segment.  ODE uniqueness now
supplies the formerly separate return equality. -/
noncomputable def C1LocalFlow.chebyshevReturnSetupOfSectionPeriod
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain) :
    ChebyshevReturnSetup X where
  localFlow := Phi
  n := n
  i := i
  j := j
  lambda := lambda
  h₀ := h
  T₀ := chebyshevHamiltonianSectionPeriod n i j lambda h
  n_ne_zero := hn
  i_lt := hi
  j_lt := hj
  lambda_ge_one := hlambda
  h₀_pos := hh
  h₀_lt_half := hhHalf
  T₀_pos := chebyshevHamiltonianSectionPeriod_pos
    hn hi hj hlambda hh.le hhHalf
  return_mem := hsegment _ ⟨
    (chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh.le hhHalf).le, le_rfl⟩
  returns_to_base := Phi.chebyshevUnperturbed_returns_after_sectionPeriod
    hn hi hj hlambda hh hhHalf hX hsegment
  unperturbed_eq := hX

/-- For the automatically constructed return setup, the genuine flow trace
is exactly the explicit section-clock physical-time trace. -/
theorem C1LocalFlow.chebyshevReturnSetupOfSectionPeriod_unperturbedTimePdy_eq
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain)
    (P : ℝ × ℝ → ℝ) :
    (Phi.chebyshevReturnSetupOfSectionPeriod
      hn hi hj hlambda hh hhHalf hX hsegment).unperturbedTimePdy P h =
      chebyshevHamiltonianSectionTimePdy
        hn hi hj P hlambda hh.le hhHalf := by
  let S := Phi.chebyshevReturnSetupOfSectionPeriod
    hn hi hj hlambda hh hhHalf hX hsegment
  let period := chebyshevHamiltonianSectionPeriod n i j lambda h
  have hperiod : 0 < period :=
    chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh.le hhHalf
  have htime : S.returnTime.time (0, h) = period := by
    simpa [S, period, ChebyshevReturnSetup.base,
      C1LocalFlow.chebyshevReturnSetupOfSectionPeriod] using S.returnTime.time_at
  change S.unperturbedTimePdy P h =
    chebyshevHamiltonianSectionTimePdy
      hn hi hj P hlambda hh.le hhHalf
  unfold ChebyshevReturnSetup.unperturbedTimePdy
    chebyshevHamiltonianSectionTimePdy
  rw [htime]
  apply parameterizedPdy_congr
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) period := by
      simpa [Set.uIcc_of_le hperiod.le] using ht
    simpa [S, period, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod] using
      Phi.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
        hn hi hj hlambda hh hhHalf hX hsegment htIcc
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) period := by
      simpa [Set.uIcc_of_le hperiod.le] using ht
    have hcurve := Phi.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
      hn hi hj hlambda hh hhHalf hX hsegment htIcc
    simpa [S, period, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod,
      hcurve]

/-- The zero-parameter normalized energy displacement of the genuine return
setup is now directly identified with the already compiled W4 angular trace. -/
theorem C1LocalFlow.chebyshevReturnSetupOfSectionPeriod_melnikovIntegral_zero_eq_neg_angularPdy
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P) :
    let S := Phi.chebyshevReturnSetupOfSectionPeriod
      hn hi hj hlambda hh hhHalf hX hsegment
    S.melnikovIntegral (chebyshevEnergyProduction n P) (0, h) =
      -chebyshevHamiltonianAngularPdy n i j P lambda h := by
  dsimp only
  let S := Phi.chebyshevReturnSetupOfSectionPeriod
    hn hi hj hlambda hh hhHalf hX hsegment
  calc
    S.melnikovIntegral (chebyshevEnergyProduction n P) (0, h) =
        -S.unperturbedTimePdy P h := by
      simpa [S, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod] using
        S.melnikovIntegral_zero_eq_neg_unperturbedTimePdy P h
    _ = -chebyshevHamiltonianSectionTimePdy
          hn hi hj P hlambda hh.le hhHalf := by
      rw [Phi.chebyshevReturnSetupOfSectionPeriod_unperturbedTimePdy_eq
        hn hi hj hlambda hh hhHalf hX hsegment P]
    _ = -chebyshevHamiltonianAngularPdy n i j P lambda h := by
      rw [chebyshevHamiltonianSectionTimePdy_eq_angularPdy
        hn hi hj hP hlambda hh.le hhHalf]

end Hilbert16
