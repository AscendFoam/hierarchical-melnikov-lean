import Hilbert16.Dynamics.ThreeAdicPeriodicOrbit
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Filter Set
open scoped Topology

/-!
# Stability of return-orbit carriers

The local return segment is normalized to the fixed compact interval
`[0,1]`.  Joint continuity and the tube lemma then keep the whole segment,
and hence its global periodic extension, inside any prescribed open
neighborhood of the unperturbed oval.
-/

/-- The return segment with its varying return time rescaled to `[0,1]`. -/
noncomputable def ChebyshevReturnSetup.normalizedReturnCurve
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (muh : ℝ × ℝ) (s : ℝ) : PhaseSpace :=
  S.returnCurve muh (S.returnTime.time muh * s)

/-- The normalized return curve is jointly `C¹` at every point of the
compact unperturbed parameter fiber. -/
theorem ChebyshevReturnSetup.contDiffAt_normalizedReturnCurve
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ 1
      (fun z : (ℝ × ℝ) × ℝ => S.normalizedReturnCurve z.1 z.2)
      ((0, S.h₀), s) := by
  have htimeMem :
      ((0, chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀),
          S.T₀ * s) ∈ S.localFlow.domain := by
    apply S.localFlow.time_segment_mem 0
      (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀)
      S.T₀_pos.le
      (S.localFlow.zero_mem 0 _)
      S.return_mem
    refine ⟨mul_nonneg S.T₀_pos.le hs.1, ?_⟩
    have hnonneg := mul_nonneg S.T₀_pos.le (sub_nonneg.mpr hs.2)
    nlinarith
  have hflow : ContDiffAt ℝ 1
      (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
      ((0, S.h₀), S.T₀ * s) :=
    S.localFlow.contDiffAt_chebyshevByEnergy S.n S.i S.j S.lambda
      S.h₀_pos S.h₀_lt_half htimeMem
  have htimeAt : S.returnTime.time (0, S.h₀) = S.T₀ := by
    simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
  have hflow' : ContDiffAt ℝ 1
      (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
      (((0, S.h₀), s).1,
        S.returnTime.time ((0, S.h₀), s).1 * ((0, S.h₀), s).2) := by
    simpa [htimeAt] using hflow
  have htime : ContDiffAt ℝ 1
      (fun z : (ℝ × ℝ) × ℝ => S.returnTime.time z.1)
      ((0, S.h₀), s) :=
    by
      simpa [Function.comp_def] using
        S.returnTime.contDiffAt_time.comp ((0, S.h₀), s) contDiffAt_fst
  have hinput : ContDiffAt ℝ 1
      (fun z : (ℝ × ℝ) × ℝ =>
        (z.1, S.returnTime.time z.1 * z.2))
      ((0, S.h₀), s) :=
    contDiffAt_fst.prodMk (htime.mul contDiffAt_snd)
  change ContDiffAt ℝ 1
    ((S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda) ∘
      fun z : (ℝ × ℝ) × ℝ =>
        (z.1, S.returnTime.time z.1 * z.2)) ((0, S.h₀), s)
  exact hflow'.comp ((0, S.h₀), s) hinput

/-- Compactness of `[0,1]` upgrades pointwise joint continuity to one
parameter neighborhood on which every normalized return segment stays in
the prescribed open set. -/
theorem ChebyshevReturnSetup.eventually_normalizedReturnCurve_mem_of_open
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    {U : Set PhaseSpace} (hU : IsOpen U)
    (hbase : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      S.normalizedReturnCurve (0, S.h₀) s ∈ U) :
    ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, S.normalizedReturnCurve muh s ∈ U := by
  classical
  let G : ((ℝ × ℝ) × ℝ) → PhaseSpace := fun z =>
    S.normalizedReturnCurve z.1 z.2
  have hlocal : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1),
      ∃ W : Set ((ℝ × ℝ) × ℝ), IsOpen W ∧
        ((0, S.h₀), s) ∈ W ∧ W ⊆ G ⁻¹' U := by
    intro s hs
    have hcont : ContinuousAt G ((0, S.h₀), s) :=
      (S.contDiffAt_normalizedReturnCurve hs).continuousAt
    have hpre : G ⁻¹' U ∈ 𝓝 ((0, S.h₀), s) :=
      hcont.preimage_mem_nhds (hU.mem_nhds (hbase s hs))
    rcases mem_nhds_iff.mp hpre with ⟨W, hWsub, hWopen, hpoint⟩
    exact ⟨W, hWopen, hpoint, hWsub⟩
  choose W hWopen hWpoint hWsub using hlocal
  let V : Set ((ℝ × ℝ) × ℝ) :=
    ⋃ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1), W s hs
  have hVopen : IsOpen V := by
    exact isOpen_iUnion fun s => isOpen_iUnion fun hs => hWopen s hs
  have hfiber : ({((0 : ℝ), S.h₀)} : Set (ℝ × ℝ)) ×ˢ
      Set.Icc (0 : ℝ) 1 ⊆ V := by
    rintro ⟨muh, s⟩ ⟨hmuh, hs⟩
    have hmuh : muh = (0, S.h₀) := Set.mem_singleton_iff.mp hmuh
    subst muh
    exact Set.mem_iUnion_of_mem s (Set.mem_iUnion_of_mem hs (hWpoint s hs))
  have hVsub : V ⊆ G ⁻¹' U := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨s, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hs, hz⟩
    exact hWsub s hs hz
  obtain ⟨A, B, hAopen, hBopen, hbaseA, hIccB, hABV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hVopen hfiber
  have hbaseIn : ((0 : ℝ), S.h₀) ∈ A :=
    hbaseA (Set.mem_singleton _)
  filter_upwards [hAopen.mem_nhds hbaseIn] with muh hmuh
  intro s hs
  have hzV : (muh, s) ∈ V := hABV ⟨hmuh, hIccB hs⟩
  exact hVsub hzV

/-- At the base parameter the normalized genuine flow segment lies on the
explicit Chebyshev energy oval. -/
theorem ChebyshevPolynomialReturnCertificate.normalizedReturnCurve_base_mem
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    C.setup.normalizedReturnCurve (0, C.setup.h₀) s ∈
      Set.range (chebyshevPhaseOrbit n i j lambda h) := by
  let t := C.setup.T₀ * s
  have ht : t ∈ Set.Icc (0 : ℝ) C.setup.T₀ :=
    ⟨mul_nonneg C.setup.T₀_pos.le hs.1, by
      have hnonneg := mul_nonneg C.setup.T₀_pos.le (sub_nonneg.mpr hs.2)
      nlinarith⟩
  have hsegment : ∀ u ∈ Set.Icc (0 : ℝ) C.setup.T₀,
      ((0, chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
        C.setup.lambda C.setup.h₀), u) ∈ C.setup.localFlow.domain := by
    intro u hu
    exact C.setup.localFlow.time_segment_mem 0 _ C.setup.T₀_pos.le
      (C.setup.localFlow.zero_mem 0 _) C.setup.return_mem u hu
  have hperiod : C.setup.T₀ =
      Spikes.chebyshevHamiltonianSectionPeriod C.setup.n C.setup.i C.setup.j
        C.setup.lambda C.setup.h₀ := by
    rw [C.setup_n, C.setup_i, C.setup_j, C.setup_lambda, C.setup_energy]
    exact C.setup_period
  have htraj := C.setup.localFlow.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
    C.setup.n_ne_zero C.setup.i_lt C.setup.j_lt C.setup.lambda_ge_one
    C.setup.h₀_pos C.setup.h₀_lt_half C.setup.unperturbed_eq
    (by simpa [hperiod] using hsegment)
    (by simpa [hperiod] using ht)
  have htime : C.setup.returnTime.time (0, C.setup.h₀) = C.setup.T₀ := by
    simpa [ChebyshevReturnSetup.base] using C.setup.returnTime.time_at
  have htime' : C.setup.returnTime.time (0, h) = C.setup.T₀ := by
    exact (congrArg (fun e : ℝ => C.setup.returnTime.time (0, e))
      C.setup_energy).symm.trans htime
  let angle := Spikes.chebyshevHamiltonianAngle C.setup.i C.setup.j
    (Spikes.chebyshevHamiltonianSectionAngularStart C.setup.i C.setup.j +
      Spikes.chebyshevHamiltonianSectionPhysicalOffset
        C.setup.n_ne_zero C.setup.i_lt C.setup.j_lt C.setup.lambda_ge_one
        C.setup.h₀_pos.le C.setup.h₀_lt_half t)
  refine ⟨angle, ?_⟩
  apply phaseSpaceProdEquiv.injective
  rw [phaseSpaceProdEquiv_chebyshevPhaseOrbit]
  simpa [ChebyshevReturnSetup.normalizedReturnCurve,
    ChebyshevReturnSetup.returnCurve, htime, htime', t, angle,
    Spikes.chebyshevHamiltonianSectionTimeOrbit,
    Spikes.chebyshevHamiltonianAngularOrbit,
    C.setup_n, C.setup_i, C.setup_j, C.setup_lambda, C.setup_energy] using htraj.symm

/-- Every open neighborhood of the unperturbed oval contains the carrier of
the continued actual periodic orbit for all sufficiently small nonzero
parameters. -/
theorem ChebyshevPolynomialReturnCertificate.eventually_periodicOrbitAt_carrier_subset
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀)
    {U : Set PhaseSpace} (hU : IsOpen U)
    (hcarrier : Set.range (chebyshevPhaseOrbit n i j lambda h) ⊆ U) :
    ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      ∃ A : ChebyshevPolynomialPeriodicOrbitAt C mu,
        A.orbit.carrier ⊆ U := by
  let path : ℝ → ℝ × ℝ := fun mu => (mu, C.continuation.root mu)
  have hpathCont : ContinuousAt path 0 :=
    continuousAt_id.prodMk C.continuation.contDiffAt_root.continuousAt
  have hpathAt : path 0 = (0, C.setup.h₀) := by
    apply Prod.ext
    · rfl
    · exact C.continuation.root_at.trans C.setup_energy.symm
  have hpath : Tendsto path (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ), C.setup.h₀)) := by
    rw [← hpathAt]
    exact hpathCont
  have hbase : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      C.setup.normalizedReturnCurve (0, C.setup.h₀) s ∈ U := by
    intro s hs
    exact hcarrier (C.normalizedReturnCurve_base_mem s hs)
  have hnormalized := hpath.eventually
    (C.setup.eventually_normalizedReturnCurve_mem_of_open hU hbase)
  filter_upwards [C.eventually_periodicOrbitAt, hnormalized]
    with mu horbit hnormalizedMu
  intro hmu
  rcases horbit hmu with ⟨A⟩
  refine ⟨A, ?_⟩
  rw [A.orbit_carrier]
  apply range_periodicExtension_subset_of_scaled_Icc _ U
  intro s hs
  exact hnormalizedMu s hs

end Hilbert16
