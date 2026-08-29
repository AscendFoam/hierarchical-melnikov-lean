import Hilbert16.Dynamics.PerturbedEnergy

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

/-- A common open parameter--energy neighborhood on which the locally
constructed return time is positive, the energy stays inside the regular
annulus, and the whole variable return segment stays in the genuine flow
domain. -/
theorem ChebyshevReturnSetup.exists_admissibleReturnNeighborhood
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (0, S.h₀) ∈ V ∧
      ∀ muh ∈ V,
        0 ≤ muh.2 ∧ muh.2 ≤ 1 / 2 ∧
        0 < S.returnTime.time muh ∧
        ∀ t ∈ Set.uIcc 0 (S.returnTime.time muh),
          ((muh.1, chebyshevPhaseSectionPoint
            S.n S.i S.j S.lambda muh.2), t) ∈ S.localFlow.domain := by
  let base : ℝ × ℝ := (0, S.h₀)
  let scaledInput : ((ℝ × ℝ) × ℝ) → ParameterPhaseSpace × ℝ := fun z ↦
    ((z.1.1, chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda z.1.2), S.returnTime.time z.1 * z.2)
  have htime : S.returnTime.time base = S.T₀ := by
    simpa [base, ChebyshevReturnSetup.base] using S.returnTime.time_at
  have hscaledAt (r : ℝ) : ContDiffAt ℝ 1 scaledInput (base, r) := by
    have hsection := contDiffAt_chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda S.h₀_pos S.h₀_lt_half
    have htimeComp : ContDiffAt ℝ 1
        (fun z : ((ℝ × ℝ) × ℝ) ↦ S.returnTime.time z.1) (base, r) :=
      S.returnTime.contDiffAt_time.comp (base, r) contDiffAt_fst
    exact (contDiffAt_fst.fst.prodMk
      (hsection.comp (base, r) contDiffAt_fst.snd)).prodMk
        (htimeComp.mul contDiffAt_snd)
  have hscaledEventually : ∀ᶠ muh in nhds base,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, scaledInput (muh, r) ∈ S.localFlow.domain := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have htimeMem : S.T₀ * r ∈ Set.Icc 0 S.T₀ := by
      constructor
      · exact mul_nonneg S.T₀_pos.le hr.1
      · exact (mul_le_mul_of_nonneg_left hr.2 S.T₀_pos.le).trans_eq (mul_one S.T₀)
    have hzero : ((0, chebyshevPhaseSectionPoint
        S.n S.i S.j S.lambda S.h₀), 0) ∈ S.localFlow.domain :=
      S.localFlow.zero_mem 0 _
    have hdomain : scaledInput (base, r) ∈ S.localFlow.domain := by
      simpa [scaledInput, base, htime] using
        S.localFlow.time_segment_mem 0 _ S.T₀_pos.le hzero S.return_mem
          (S.T₀ * r) htimeMem
    exact (hscaledAt r).continuousAt.eventually_mem
      (S.localFlow.isOpen_domain.mem_nhds hdomain)
  have henergyEventually : ∀ᶠ muh in nhds base,
      0 ≤ muh.2 ∧ muh.2 ≤ 1 / 2 := by
    have hbaseEnergy : base.2 ∈ Set.Ioo 0 (1 / 2) :=
      ⟨S.h₀_pos, S.h₀_lt_half⟩
    filter_upwards [continuousAt_snd.eventually_mem
      (isOpen_Ioo.mem_nhds hbaseEnergy)] with muh hmuh
    exact ⟨hmuh.1.le, hmuh.2.le⟩
  have htimeEventually : ∀ᶠ muh in nhds base, 0 < S.returnTime.time muh := by
    have : S.returnTime.time base ∈ Set.Ioi 0 := by
      rw [htime]
      exact S.T₀_pos
    exact S.returnTime.contDiffAt_time.continuousAt.eventually_mem
      (isOpen_Ioi.mem_nhds this)
  have hgood : ∀ᶠ muh in nhds base,
      (0 ≤ muh.2 ∧ muh.2 ≤ 1 / 2) ∧
      0 < S.returnTime.time muh ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1,
        scaledInput (muh, r) ∈ S.localFlow.domain :=
    henergyEventually.and (htimeEventually.and hscaledEventually)
  obtain ⟨V, hVsub, hVopen, hbaseV⟩ := mem_nhds_iff.mp hgood
  refine ⟨V, hVopen, ?_, ?_⟩
  · simpa [base] using hbaseV
  · intro muh hmuh
    have hg := hVsub hmuh
    refine ⟨hg.1.1, hg.1.2, hg.2.1, ?_⟩
    intro t ht
    have hTpos := hg.2.1
    have htIcc : t ∈ Set.Icc 0 (S.returnTime.time muh) := by
      simpa only [uIcc_of_le hTpos.le] using ht
    let r : ℝ := t / S.returnTime.time muh
    have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg htIcc.1 hTpos.le
      · exact (div_le_one hTpos).2 htIcc.2
    have hrDomain := hg.2.2 r hr
    have hmul : S.returnTime.time muh * r = t := by
      dsimp [r]
      exact mul_div_cancel₀ t hTpos.ne'
    simpa [scaledInput, hmul] using hrDomain

/-- On one common open neighborhood, the genuine return displacement for
the actual perturbed field has the exact division-free factorization and
the genuine energy return map equals the normalized return map. -/
theorem ChebyshevReturnSetup.exists_actualMelnikovFactorizationNeighborhood
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ)
    (hX : ∀ (mu : ℝ) (z : PhaseSpace),
      X mu z = chebyshevPerturbedPhaseVector S.n S.lambda P mu z)
    (hP : ContDiff ℝ 1 P) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (0, S.h₀) ∈ V ∧
      ∀ muh ∈ V,
        S.energyDisplacement muh =
          muh.1 * S.melnikovIntegral
            (chebyshevEnergyProduction S.n P) muh ∧
        S.energyReturnMap muh.1 muh.2 =
          normalizedReturnMap
            (S.melnikovIntegral (chebyshevEnergyProduction S.n P))
              muh.1 muh.2 := by
  obtain ⟨V, hVopen, hbaseV, hV⟩ := S.exists_admissibleReturnNeighborhood
  refine ⟨V, hVopen, hbaseV, ?_⟩
  intro muh hmuh
  have hfactor := S.energyDisplacement_eq_mu_mul_actualMelnikov
    P hX hP.continuous (mu := muh.1) (h := muh.2)
      (hV muh hmuh).1 (hV muh hmuh).2.1 (hV muh hmuh).2.2.2
  exact ⟨hfactor,
    S.energyReturnMap_eq_normalizedReturnMap hfactor⟩

/-- Complete conditional Poincaré--Pontryagin persistence at one simple
Melnikov zero.  For every sufficiently small nonzero parameter, the actual
energy return map (not merely an auxiliary normalized map) has a fixed point
whose multiplier differs from `1`. -/
theorem ChebyshevReturnSetup.eventually_energyReturnMap_fixed_and_hyperbolic
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ)
    (hX : ∀ (mu : ℝ) (z : PhaseSpace),
      X mu z = chebyshevPerturbedPhaseVector S.n S.lambda P mu z)
    (hP : ContDiff ℝ 1 P) {d : ℝ}
    (hzero : S.melnikovIntegral
      (chebyshevEnergyProduction S.n P) (0, S.h₀) = 0)
    (hslice : HasDerivAt
      (fun h : ℝ ↦ S.melnikovIntegral
        (chebyshevEnergyProduction S.n P) (0, h)) d S.h₀)
    (hd : d ≠ 0) :
    let C := ContDiffAt.localZeroContinuation_of_hasDerivAt
      (S.contDiffAt_actualMelnikov P hP) hzero hslice hd
    ∀ᶠ mu in nhds (0 : ℝ), mu ≠ 0 →
      S.energyReturnMap mu (C.root mu) = C.root mu ∧
        ∃ rho : ℝ, HasDerivAt (S.energyReturnMap mu) rho (C.root mu) ∧
          rho ≠ 1 := by
  let D := S.melnikovIntegral (chebyshevEnergyProduction S.n P)
  have hD : ContDiffAt ℝ 1 D (0, S.h₀) :=
    S.contDiffAt_actualMelnikov P hP
  let C := ContDiffAt.localZeroContinuation_of_hasDerivAt
    hD hzero hslice hd
  change ∀ᶠ mu in nhds (0 : ℝ), mu ≠ 0 →
    S.energyReturnMap mu (C.root mu) = C.root mu ∧
      ∃ rho : ℝ, HasDerivAt (S.energyReturnMap mu) rho (C.root mu) ∧
        rho ≠ 1
  have hnormalized : ∀ᶠ mu in nhds (0 : ℝ), mu ≠ 0 →
      normalizedReturnMap D mu (C.root mu) = C.root mu ∧
        ∃ rho : ℝ,
          HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) ∧ rho ≠ 1 := by
    simpa [C] using eventually_normalizedReturnMap_fixed_and_hyperbolic
      hD hzero hslice hd
  obtain ⟨V, hVopen, hbaseV, hfactor⟩ :=
    S.exists_actualMelnikovFactorizationNeighborhood P hX hP
  let rootPoint : ℝ → ℝ × ℝ := fun mu ↦ (mu, C.root mu)
  have hrootPointAt : ContinuousAt rootPoint 0 :=
    continuousAt_id.prodMk C.contDiffAt_root.continuousAt
  have hrootPointZero : rootPoint 0 = (0, S.h₀) := by
    exact Prod.ext rfl C.root_at
  have hrootIn : ∀ᶠ mu in nhds (0 : ℝ), rootPoint mu ∈ V := by
    have htend : Tendsto rootPoint (nhds (0 : ℝ)) (nhds (0, S.h₀)) := by
      rw [← hrootPointZero]
      exact hrootPointAt
    exact htend.eventually (hVopen.mem_nhds hbaseV)
  filter_upwards [hnormalized, hrootIn] with mu hnorm hmuV
  intro hmu
  have hn := hnorm hmu
  have heqAt := (hfactor (rootPoint mu) hmuV).2
  have hsliceIn : ∀ᶠ h in nhds (C.root mu), (mu, h) ∈ V :=
    (continuousAt_const.prodMk continuousAt_id).eventually_mem
      (hVopen.mem_nhds hmuV)
  have heqGerm : S.energyReturnMap mu =ᶠ[nhds (C.root mu)]
      normalizedReturnMap D mu := by
    filter_upwards [hsliceIn] with h hh
    exact (hfactor (mu, h) hh).2
  refine ⟨?_, ?_⟩
  · rw [heqAt]
    exact hn.1
  · rcases hn.2 with ⟨rho, hrho, hrhoNe⟩
    exact ⟨rho, hrho.congr_of_eventuallyEq heqGerm, hrhoNe⟩

end Hilbert16
