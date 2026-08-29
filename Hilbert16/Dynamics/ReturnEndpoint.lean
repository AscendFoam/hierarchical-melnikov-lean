import Hilbert16.Dynamics.PeriodicExtension
import Hilbert16.Dynamics.MelnikovIntegral
import Hilbert16.Spikes.ChebyshevChangeOfVariables
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

/-- The actual phase point selected by the local return-time branch. -/
noncomputable def ChebyshevReturnSetup.returnPoint
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (muh : ℝ × ℝ) : PhaseSpace :=
  S.returnTime.returnPoint
    (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda) muh

theorem ChebyshevReturnSetup.returnPoint_eq_flow
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (muh : ℝ × ℝ) :
    S.returnPoint muh =
      S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda
        (muh, S.returnTime.time muh) := rfl

theorem chebyshevPhaseSectionPoint_fst_eq_inverseBranch
    (n i j : ℕ) (lambda h : ℝ) :
    (phaseSpaceProdEquiv (chebyshevPhaseSectionPoint n i j lambda h)).1 =
      Spikes.chebyshevInverseBranch n i (Real.sqrt (2 * h)) := by
  simp [chebyshevPhaseSectionPoint, chebyshevPhaseOrbit,
    Spikes.chebyshevCellOrbit, Spikes.chebyshevCellInverseMap,
    Spikes.ellipticOrbitUV]

theorem chebyshevPhaseSectionPoint_forwardCoordinate_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (phaseSpaceProdEquiv (chebyshevPhaseSectionPoint n i j lambda h)).1 =
      Real.sqrt (2 * h) := by
  rw [chebyshevPhaseSectionPoint_fst_eq_inverseBranch]
  apply Spikes.eval_chebyshevInverseBranch hn
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsquare : (Real.sqrt (2 * h)) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  have hsqrtNonneg := Real.sqrt_nonneg (2 * h)
  nlinarith

/-- Near the base return, equality of the scalar energy-return coordinate
forces equality of the full phase point.  The proof uses the section equation,
positivity of the forward Chebyshev coordinate, and its local inverse. -/
theorem ChebyshevReturnSetup.eventually_returnPoint_eq_sectionPoint_of_energy_fixed
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      S.energyReturnMap muh.1 muh.2 = muh.2 →
        S.returnPoint muh =
          chebyshevPhaseSectionPoint S.n S.i S.j S.lambda muh.2 := by
  let p : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (S.n : ℤ)
  let basePoint : PhaseSpace :=
    chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀
  let x₀ : ℝ := (phaseSpaceProdEquiv basePoint).1
  let retX : ℝ × ℝ → ℝ := fun muh =>
    (phaseSpaceProdEquiv (S.returnPoint muh)).1
  let initX : ℝ × ℝ → ℝ := fun muh =>
    (phaseSpaceProdEquiv
      (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda muh.2)).1
  have hbaseFlow : S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda S.base =
      basePoint := by
    simpa [ChebyshevReturnSetup.base, basePoint] using S.returns_to_base
  have hretCont : Tendsto retX (𝓝 ((0 : ℝ), S.h₀)) (𝓝 x₀) := by
    have hreturn := S.returnTime.contDiffAt_returnPoint S.contDiffAt_flowByEnergy
    have hvalue : S.returnPoint (0, S.h₀) = basePoint := by
      change S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda
        ((0, S.h₀), S.returnTime.time (0, S.h₀)) = basePoint
      have htime : S.returnTime.time (0, S.h₀) = S.T₀ := by
        simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
      rw [htime]
      simpa [ChebyshevReturnSetup.base] using hbaseFlow
    have hreturnAt : ContDiffAt ℝ 1
        (S.returnTime.returnPoint
          (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda))
        (0, S.h₀) := by
      simpa [ChebyshevReturnSetup.base] using hreturn
    have hcomp : ContinuousAt retX (0, S.h₀) := by
      exact (phaseSpaceProdEquiv.continuous.continuousAt.fst.comp
        hreturnAt.continuousAt)
    simpa [retX, x₀, hvalue] using hcomp.tendsto
  have hinitCont : Tendsto initX (𝓝 ((0 : ℝ), S.h₀)) (𝓝 x₀) := by
    have hsection := contDiffAt_chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda S.h₀_pos S.h₀_lt_half
    have hsectionComp : ContinuousAt
        (fun muh : ℝ × ℝ =>
          chebyshevPhaseSectionPoint S.n S.i S.j S.lambda muh.2)
        (0, S.h₀) := by
      have hsnd : ContinuousAt (fun muh : ℝ × ℝ => muh.2) (0, S.h₀) :=
        continuousAt_snd
      change ContinuousAt
        (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda ∘
          fun muh : ℝ × ℝ => muh.2) (0, S.h₀)
      exact hsection.continuousAt.tendsto.comp hsnd
    have hcomp : ContinuousAt initX (0, S.h₀) := by
      exact (phaseSpaceProdEquiv.continuous.continuousAt.fst.comp
        hsectionComp)
    simpa [initX, x₀, basePoint] using hcomp.tendsto
  have hsqrtPos : 0 < Real.sqrt (2 * S.h₀) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) S.h₀_pos)
  have hpBase : p.eval x₀ = Real.sqrt (2 * S.h₀) := by
    simpa [p, x₀, basePoint] using
      chebyshevPhaseSectionPoint_forwardCoordinate_eq
        S.n_ne_zero S.h₀_pos.le S.h₀_lt_half.le
  have hpDerivNe : p.derivative.eval x₀ ≠ 0 := by
    have hprod := Spikes.chebyshevForwardDerivative_mul_inverseDeriv_eq_one
      (i := S.i) S.n_ne_zero (u := Real.sqrt (2 * S.h₀)) (by
        rw [abs_of_pos hsqrtPos]
        have hsquare : (Real.sqrt (2 * S.h₀)) ^ 2 = 2 * S.h₀ :=
          Real.sq_sqrt (mul_nonneg (by norm_num) S.h₀_pos.le)
        have htwo : 2 * S.h₀ < 1 := by nlinarith [S.h₀_lt_half]
        nlinarith)
    have hx₀ : x₀ = Spikes.chebyshevInverseBranch S.n S.i
        (Real.sqrt (2 * S.h₀)) := by
      simpa [x₀, basePoint] using
        chebyshevPhaseSectionPoint_fst_eq_inverseBranch
          S.n S.i S.j S.lambda S.h₀
    have hforwardNe : Spikes.chebyshevForwardDerivative S.n
        (Spikes.chebyshevInverseBranch S.n S.i (Real.sqrt (2 * S.h₀))) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hprod
      norm_num at hprod
    simpa [Spikes.chebyshevForwardDerivative, p, hx₀] using hforwardNe
  have hpStrict : HasStrictDerivAt (fun x : ℝ => p.eval x)
      (p.derivative.eval x₀) x₀ := p.hasStrictDerivAt x₀
  have hsectionLevel : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      chebyshevSectionCoordinate S.n S.j (S.returnPoint muh) = 0 := by
    have hlevel := S.returnTime.eventually_returnPoint_level
      (flow := S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
      (sectionFn := chebyshevSectionCoordinate S.n S.j)
    have hbaseSection : chebyshevSectionCoordinate S.n S.j
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda S.base) = 0 := by
      rw [hbaseFlow]
      exact chebyshevPhaseSectionPoint_on_section _ _ _ _ _
    have hlevel' : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
        chebyshevSectionCoordinate S.n S.j (S.returnPoint muh) =
          chebyshevSectionCoordinate S.n S.j
            (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda S.base) := by
      simpa [ChebyshevReturnSetup.returnPoint, ChebyshevReturnSetup.base] using hlevel
    filter_upwards [hlevel'] with muh hm
    exact hm.trans hbaseSection
  have henergyRange : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      0 < muh.2 ∧ muh.2 < 1 / 2 := by
    have hsnd : Tendsto (fun muh : ℝ × ℝ => muh.2)
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 S.h₀) := continuousAt_snd
    exact (hsnd.eventually (eventually_gt_nhds S.h₀_pos)).and
      (hsnd.eventually (eventually_lt_nhds S.h₀_lt_half))
  have hretPos : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀), 0 < p.eval (retX muh) := by
    have htendsto : Tendsto (fun muh => p.eval (retX muh))
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 (p.eval x₀)) :=
      p.continuous.continuousAt.tendsto.comp hretCont
    have hpBasePos : 0 < p.eval x₀ := by simpa [hpBase] using hsqrtPos
    exact htendsto.eventually (eventually_gt_nhds hpBasePos)
  have hinitPos : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀), 0 < p.eval (initX muh) := by
    have htendsto : Tendsto (fun muh => p.eval (initX muh))
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 (p.eval x₀)) :=
      p.continuous.continuousAt.tendsto.comp hinitCont
    have hpBasePos : 0 < p.eval x₀ := by simpa [hpBase] using hsqrtPos
    exact htendsto.eventually (eventually_gt_nhds hpBasePos)
  have hpEq : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      S.energyReturnMap muh.1 muh.2 = muh.2 →
        p.eval (retX muh) = p.eval (initX muh) := by
    filter_upwards [hsectionLevel, henergyRange, hretPos, hinitPos]
      with muh hsection hrange hretp hinitp
    intro hfixed
    let ret := S.returnPoint muh
    let init := chebyshevPhaseSectionPoint S.n S.i S.j S.lambda muh.2
    have hy : (phaseSpaceProdEquiv ret).2 = (phaseSpaceProdEquiv init).2 := by
      have hinitSection := chebyshevPhaseSectionPoint_on_section
        S.n S.i S.j S.lambda muh.2
      dsimp [ret, init] at hsection hinitSection ⊢
      unfold chebyshevSectionCoordinate at hsection hinitSection
      linarith
    have hretEnergy : chebyshevPhaseEnergy S.n S.lambda ret = muh.2 := by
      rw [← hfixed, S.energyReturnMap_eq_returnCoordinate]
      rfl
    have hinitEnergy : chebyshevPhaseEnergy S.n S.lambda init = muh.2 :=
      chebyshevPhaseSectionPoint_energy_eq S.n_ne_zero S.lambda_ge_one
        hrange.1.le hrange.2.le
    have hsquares : p.eval (phaseSpaceProdEquiv ret).1 ^ 2 =
        p.eval (phaseSpaceProdEquiv init).1 ^ 2 := by
      unfold chebyshevPhaseEnergy Spikes.chebyshevHamiltonian at hretEnergy hinitEnergy
      dsimp [p]
      rw [hy] at hretEnergy
      linarith
    change p.eval (phaseSpaceProdEquiv ret).1 =
      p.eval (phaseSpaceProdEquiv init).1
    dsimp [retX, initX, ret, init] at hretp hinitp
    nlinarith
  have hxEq : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      S.energyReturnMap muh.1 muh.2 = muh.2 → retX muh = initX muh := by
    -- The local-inverse conclusion is used only under the fixed-point hypothesis.
    filter_upwards [hpEq,
      hretCont.eventually (hpStrict.eventually_left_inverse hpDerivNe),
      hinitCont.eventually (hpStrict.eventually_left_inverse hpDerivNe)]
      with muh hp hri hii
    intro hfix
    calc
      retX muh = hpStrict.localInverse _ _ _ hpDerivNe (p.eval (retX muh)) := hri.symm
      _ = hpStrict.localInverse _ _ _ hpDerivNe (p.eval (initX muh)) := by rw [hp hfix]
      _ = initX muh := hii
  filter_upwards [hsectionLevel, hxEq] with muh hsection hx hfixed
  apply phaseSpaceProdEquiv.injective
  apply Prod.ext
  · exact hx hfixed
  · have hinitSection := chebyshevPhaseSectionPoint_on_section
      S.n S.i S.j S.lambda muh.2
    unfold chebyshevSectionCoordinate at hsection hinitSection
    linarith

end Hilbert16
