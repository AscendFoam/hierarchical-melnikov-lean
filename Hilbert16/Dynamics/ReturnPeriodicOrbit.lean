import Hilbert16.Dynamics.ReturnEndpoint
import Hilbert16.Dynamics.MelnikovPersistence

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

theorem exists_ne_zero_of_hasDerivAt_ne_zero_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ → E} {v : E} {T : ℝ}
    (hT : 0 < T) (hc : HasDerivAt c v 0) (hv : v ≠ 0) :
    ∃ s ∈ Set.Icc (0 : ℝ) T, c s ≠ c 0 := by
  by_contra h
  push Not at h
  have hconst : HasDerivWithinAt c 0 (Set.Icc (0 : ℝ) T) 0 := by
    exact (hasDerivAt_const (x := (0 : ℝ)) (c 0)).hasDerivWithinAt.congr
      (fun s hs => h s hs) rfl
  have hunique := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
  have hvEq := hc.hasDerivWithinAt.derivWithin hunique
  have hzeroEq := hconst.derivWithin hunique
  exact hv (hvEq.symm.trans hzeroEq)

/-- The perturbed Chebyshev vector never vanishes at a regular section
point: its second coordinate is the unchanged Hamiltonian component. -/
theorem chebyshevPerturbedPhaseVector_section_ne_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) (P : ℝ × ℝ → ℝ) (mu : ℝ) :
    chebyshevPerturbedPhaseVector n lambda P mu
      (chebyshevPhaseSectionPoint n i j lambda h) ≠ 0 := by
  intro hzero
  have htrans := chebyshevSectionFDeriv_phaseHamiltonianVector_ne_zero
    hn hi hj hlambda hh hhHalf
  apply htrans
  have heq : chebyshevSectionFDeriv
      (chebyshevPerturbedPhaseVector n lambda P mu
        (chebyshevPhaseSectionPoint n i j lambda h)) =
      chebyshevSectionFDeriv
        (chebyshevPhaseHamiltonianVector n lambda
          (chebyshevPhaseSectionPoint n i j lambda h)) := by
    simp [chebyshevSectionFDeriv, chebyshevPerturbedPhaseVector,
      chebyshevPerturbedVector, chebyshevPhaseHamiltonianVector,
      Spikes.chebyshevHamiltonianVector]
  rw [← heq, hzero, map_zero]

/-- The local return segment based at one parameter--energy pair. -/
noncomputable def ChebyshevReturnSetup.returnCurve
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (muh : ℝ × ℝ) (t : ℝ) : PhaseSpace :=
  S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda (muh, t)

/-- For the actual polynomial perturbation, every sufficiently nearby
energy fixed point of the genuine return map gives a genuine global
periodic orbit carrier. -/
theorem ChebyshevReturnSetup.eventually_exists_periodicOrbit_of_energy_fixed
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ)
    (hX : ∀ (mu : ℝ) (z : PhaseSpace),
      X mu z = chebyshevPerturbedPhaseVector S.n S.lambda P mu z) :
    ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      S.energyReturnMap muh.1 muh.2 = muh.2 →
        ∃ O : PeriodicOrbit (X muh.1),
          O.carrier = Set.range
            (periodicExtension (S.returnTime.time muh) (S.returnCurve muh)) := by
  obtain ⟨V, hVopen, hbaseV, hV⟩ := S.exists_admissibleReturnNeighborhood
  have hVevent : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀), muh ∈ V :=
    hVopen.mem_nhds hbaseV
  have henergyStrict : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      0 < muh.2 ∧ muh.2 < 1 / 2 := by
    have hsnd : Tendsto (fun muh : ℝ × ℝ => muh.2)
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 S.h₀) := continuousAt_snd
    exact (hsnd.eventually (eventually_gt_nhds S.h₀_pos)).and
      (hsnd.eventually (eventually_lt_nhds S.h₀_lt_half))
  have hendpoint := S.eventually_returnPoint_eq_sectionPoint_of_energy_fixed
  filter_upwards [hVevent, henergyStrict, hendpoint]
    with muh hmuhV hrange hendpointFixed
  intro hfixed
  have hadm := hV muh hmuhV
  have hT : 0 < S.returnTime.time muh := hadm.2.2.1
  have hsegment : ∀ t ∈ Set.Icc (0 : ℝ) (S.returnTime.time muh),
      ((muh.1, chebyshevPhaseSectionPoint
        S.n S.i S.j S.lambda muh.2), t) ∈ S.localFlow.domain := by
    intro t ht
    exact hadm.2.2.2 t (by simpa [uIcc_of_le hT.le] using ht)
  have hinitial : S.returnCurve muh 0 =
      chebyshevPhaseSectionPoint S.n S.i S.j S.lambda muh.2 := by
    exact S.localFlow.chebyshevByEnergy_initial
      S.n S.i S.j S.lambda muh.1 muh.2 (hsegment 0 ⟨le_rfl, hT.le⟩)
  have hclose : S.returnCurve muh (S.returnTime.time muh) =
      S.returnCurve muh 0 := by
    rw [hinitial]
    exact hendpointFixed hfixed
  have hcurveDeriv : ∀ t ∈ Set.Icc (0 : ℝ) (S.returnTime.time muh),
      HasDerivAt (S.returnCurve muh)
        (X muh.1 (S.returnCurve muh t)) t := by
    intro t ht
    exact S.localFlow.chebyshevByEnergy_hasDerivAt
      S.n S.i S.j S.lambda muh.1 muh.2 t (hsegment t ht)
  have hsectionDeriv : HasDerivAt
      (fun t : ℝ => chebyshevSectionCoordinate S.n S.j (S.returnCurve muh t))
      (chebyshevSectionFDeriv (X muh.1 (S.returnCurve muh 0))) 0 := by
    have hcomp := (chebyshevSectionCoordinate_hasFDerivAt S.n S.j _).comp 0
      (hcurveDeriv 0 ⟨le_rfl, hT.le⟩).hasFDerivAt |>.hasDerivAt
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hcomp
  have hsectionVelocity :
      chebyshevSectionFDeriv (X muh.1 (S.returnCurve muh 0)) ≠ 0 := by
    rw [hinitial, hX]
    simpa [chebyshevSectionFDeriv, chebyshevPerturbedPhaseVector,
      chebyshevPerturbedVector, chebyshevPhaseHamiltonianVector,
      Spikes.chebyshevHamiltonianVector] using
      (chebyshevSectionFDeriv_phaseHamiltonianVector_ne_zero
        S.n_ne_zero S.i_lt S.j_lt S.lambda_ge_one hrange.1 hrange.2)
  obtain ⟨s, hs, hsne⟩ := exists_ne_zero_of_hasDerivAt_ne_zero_on_Icc
    hT hsectionDeriv hsectionVelocity
  have hnonconst : ∃ s ∈ Set.Icc (0 : ℝ) (S.returnTime.time muh),
      S.returnCurve muh s ≠ S.returnCurve muh 0 := by
    refine ⟨s, hs, ?_⟩
    intro heq
    exact hsne (congrArg (chebyshevSectionCoordinate S.n S.j) heq)
  have hperiodic : IsPeriodicIntegralCurve (X muh.1)
      (periodicExtension (S.returnTime.time muh) (S.returnCurve muh)) :=
    isPeriodicIntegralCurve_periodicExtension hT hcurveDeriv hclose hnonconst
  let O : PeriodicOrbit (X muh.1) :=
    { carrier := Set.range
        (periodicExtension (S.returnTime.time muh) (S.returnCurve muh))
      exists_periodicParametrization := ⟨_, hperiodic, rfl⟩ }
  exact ⟨O, rfl⟩

end Hilbert16
