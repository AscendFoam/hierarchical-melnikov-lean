import Hilbert16.Dynamics.MonotoneReturn
import Hilbert16.Dynamics.ReturnCarrierStability
import Hilbert16.Dynamics.ReturnTubeSection

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Hilbert16

open Filter Set
open scoped Topology

/-!
# Isolation from an oriented return tube

The local return-time branch need not be the first return of an arbitrary
nearby periodic carrier.  We therefore iterate every section hit.  The
oriented angular tube forces all iterates to remain in one compact energy
interval; order preservation makes them converge; and the uniform simple-
root theorem identifies the limit with the continued root.
-/

/-- One compact energy interval simultaneously supports the genuine return
segment, the angular-ray endpoint, order preservation, and uniform fixed-
point uniqueness. -/
theorem ChebyshevPolynomialReturnCertificate.exists_compactReturnIterationInterval
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀) :
    ∃ a b : ℝ,
      0 < a ∧ a < h ∧ h < b ∧ b < 1 / 2 ∧
      ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
        ContinuousOn (C.setup.energyReturnMap mu) (Set.Icc a b) ∧
        MonotoneOn (C.setup.energyReturnMap mu) (Set.Icc a b) ∧
        (∀ e ∈ Set.Icc a b,
          C.setup.energyReturnMap mu e = e →
            e = C.continuation.root mu) ∧
        ∀ e ∈ Set.Icc a b,
          0 < C.setup.returnTime.time (mu, e) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) (C.setup.returnTime.time (mu, e)),
            ((mu, chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
              C.setup.lambda e), t) ∈ C.setup.localFlow.domain) ∧
          C.setup.returnPoint (mu, e) =
            chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
              C.setup.lambda (C.setup.energyReturnMap mu e) ∧
          chebyshevSignedForwardY C.setup.n C.setup.i C.setup.j C.setup.lambda
              (C.setup.returnPoint (mu, e)) = 0 ∧
            0 < chebyshevForwardX C.setup.n (C.setup.returnPoint (mu, e)) := by
  let P : ℝ × ℝ → ℝ :=
    mvPolynomialProdEval (chebyshevPPolynomial n S₀)
  let D : ℝ × ℝ → ℝ :=
    C.setup.melnikovIntegral
      (chebyshevEnergyProduction C.setup.n P)
  have hP : ContDiff ℝ 1 P :=
    contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S₀) 1
  have hD : ContDiffAt ℝ 1 D (0, h) := by
    simpa only [D, C.setup_energy] using
      C.setup.contDiffAt_actualMelnikov P hP
  obtain ⟨a₀, b₀, ha₀, hb₀, hmono⟩ :=
    exists_Icc_eventually_monotone_normalizedReturnMap hD
  obtain ⟨Vfix, hVfixOpen, hhVfix, hfix⟩ :=
    C.exists_uniformFixedPointNeighborhood
  obtain ⟨Vadm, hVadmOpen, hbaseVadm, hVadm⟩ :=
    C.setup.exists_admissibleReturnNeighborhood
  have hadm : ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      0 ≤ muh.2 ∧ muh.2 ≤ 1 / 2 ∧
      0 < C.setup.returnTime.time muh ∧
      ∀ t ∈ Set.uIcc 0 (C.setup.returnTime.time muh),
        ((muh.1, chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
          C.setup.lambda muh.2), t) ∈ C.setup.localFlow.domain := by
    have hbase : ((0 : ℝ), h) ∈ Vadm := by
      simpa only [C.setup_energy] using hbaseVadm
    filter_upwards [hVadmOpen.mem_nhds hbase] with muh hmuh
    exact hVadm muh hmuh
  have hX : ∀ (mu : ℝ) (z : PhaseSpace),
      chebyshevPerturbedPhaseVector n lambda P mu z =
        chebyshevPerturbedPhaseVector C.setup.n C.setup.lambda P mu z := by
    intro mu z
    rw [C.setup_n, C.setup_lambda]
  obtain ⟨Vfactor, hVfactorOpen, hbaseVfactor, hVfactor⟩ :=
    C.setup.exists_actualMelnikovFactorizationNeighborhood P hX hP
  have hfactor : ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      C.setup.energyReturnMap muh.1 muh.2 =
        normalizedReturnMap D muh.1 muh.2 := by
    have hbase : ((0 : ℝ), h) ∈ Vfactor := by
      simpa only [C.setup_energy] using hbaseVfactor
    filter_upwards [hVfactorOpen.mem_nhds hbase] with muh hmuh
    simpa only [D] using (hVfactor muh hmuh).2
  have hendpoint : ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      C.setup.returnPoint muh = chebyshevPhaseSectionPoint
        C.setup.n C.setup.i C.setup.j C.setup.lambda
          (C.setup.energyReturnMap muh.1 muh.2) := by
    simpa only [C.setup_energy] using
      C.setup.eventually_returnPoint_eq_sectionPoint_energyReturnMap
  have hray : ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      chebyshevSignedForwardY C.setup.n C.setup.i C.setup.j C.setup.lambda
          (C.setup.returnPoint muh) = 0 ∧
        0 < chebyshevForwardX C.setup.n (C.setup.returnPoint muh) := by
    simpa only [C.setup_energy] using
      C.setup.eventually_returnPoint_mem_chebyshevPositiveRay
  have hpair : ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      (0 ≤ muh.2 ∧ muh.2 ≤ 1 / 2 ∧
        0 < C.setup.returnTime.time muh ∧
        ∀ t ∈ Set.uIcc 0 (C.setup.returnTime.time muh),
          ((muh.1, chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
            C.setup.lambda muh.2), t) ∈ C.setup.localFlow.domain) ∧
      C.setup.energyReturnMap muh.1 muh.2 =
        normalizedReturnMap D muh.1 muh.2 ∧
      C.setup.returnPoint muh = chebyshevPhaseSectionPoint
        C.setup.n C.setup.i C.setup.j C.setup.lambda
          (C.setup.energyReturnMap muh.1 muh.2) ∧
      (chebyshevSignedForwardY C.setup.n C.setup.i C.setup.j C.setup.lambda
          (C.setup.returnPoint muh) = 0 ∧
        0 < chebyshevForwardX C.setup.n (C.setup.returnPoint muh)) :=
    hadm.and (hfactor.and (hendpoint.and hray))
  rcases mem_nhds_prod_iff.mp hpair with ⟨A, hA, B, hB, hAB⟩
  let E : Set ℝ :=
    Set.Ioo a₀ b₀ ∩ Vfix ∩ B ∩ Set.Ioo 0 (1 / 2)
  have hE : E ∈ 𝓝 h := by
    apply inter_mem
    · apply inter_mem
      · exact inter_mem
          (isOpen_Ioo.mem_nhds ⟨ha₀, hb₀⟩)
          (hVfixOpen.mem_nhds hhVfix)
      · exact hB
    · exact isOpen_Ioo.mem_nhds ⟨C.setup.h₀_pos.trans_eq C.setup_energy,
        C.setup_energy ▸ C.setup.h₀_lt_half⟩
  rcases Metric.mem_nhds_iff.mp hE with ⟨eps, heps, hball⟩
  let delta : ℝ := eps / 2
  let a : ℝ := h - delta
  let b : ℝ := h + delta
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hJsub : Set.Icc a b ⊆ E := by
    intro e he
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have heL : h - delta ≤ e := by simpa only [a] using he.1
    have heU : e ≤ h + delta := by simpa only [b] using he.2
    have habs : |e - h| ≤ delta := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    exact habs.trans_lt (by dsimp [delta]; linarith)
  have hJmonoSub : Set.Icc a b ⊆ Set.Ioo a₀ b₀ := by
    intro e he
    exact (hJsub he).1.1.1
  have hJfix : Set.Icc a b ⊆ Vfix := by
    intro e he
    exact (hJsub he).1.1.2
  have hJB : Set.Icc a b ⊆ B := by
    intro e he
    exact (hJsub he).1.2
  have hJregular : Set.Icc a b ⊆ Set.Ioo 0 (1 / 2) := by
    intro e he
    exact (hJsub he).2
  have haPos : 0 < a := by
    exact (hJregular (show a ∈ Set.Icc a b from ⟨le_rfl, by
      dsimp [a, b]; linarith⟩)).1
  have hbHalf : b < 1 / 2 := by
    exact (hJregular (show b ∈ Set.Icc a b from ⟨by
      dsimp [a, b]; linarith, le_rfl⟩)).2
  refine ⟨a, b, haPos, by dsimp [a]; linarith,
    by dsimp [b]; linarith, hbHalf, ?_⟩
  filter_upwards [hA, hmono, hfix] with mu hmuA hmonoMu hfixMu
  intro hmu
  have hJmono : Set.Icc a b ⊆ Set.Icc a₀ b₀ := by
    intro e he
    exact ⟨(hJmonoSub he).1.le, (hJmonoSub he).2.le⟩
  have hgood (e : ℝ) (he : e ∈ Set.Icc a b) :=
    hAB (show (mu, e) ∈ A ×ˢ B from ⟨hmuA, hJB he⟩)
  have heqOn : Set.EqOn (C.setup.energyReturnMap mu)
      (normalizedReturnMap D mu) (Set.Icc a b) := by
    intro e he
    exact (hgood e he).2.1
  have hcont : ContinuousOn (C.setup.energyReturnMap mu) (Set.Icc a b) :=
    (hmonoMu.1.mono hJmono).congr heqOn
  have hmonotone : MonotoneOn (C.setup.energyReturnMap mu) (Set.Icc a b) := by
    intro x hx y hy hxy
    rw [heqOn hx, heqOn hy]
    exact hmonoMu.2 (hJmono hx) (hJmono hy) hxy
  refine ⟨hcont, hmonotone, ?_, ?_⟩
  · intro e he hfixed
    exact hfixMu hmu e (hJfix he) hfixed
  · intro e he
    have hg := hgood e he
    have hadmE := hg.1
    refine ⟨hadmE.2.2.1, ?_, hg.2.2.1, hg.2.2.2⟩
    intro t ht
    exact hadmE.2.2.2 t (by
      simpa [uIcc_of_le hadmE.2.2.1.le] using ht)

/-- Every sufficiently small nonzero parameter carries the continued
periodic orbit as an actual isolated periodic-orbit carrier. -/
theorem ChebyshevPolynomialReturnCertificate.eventually_isolatedPeriodicOrbitAt
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀) :
    ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      ∃ A : ChebyshevPolynomialPeriodicOrbitAt C mu,
        A.orbit.IsIsolated := by
  classical
  let P : ℝ × ℝ → ℝ :=
    mvPolynomialProdEval (chebyshevPPolynomial n S₀)
  have hP : ContDiff ℝ 1 P :=
    contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S₀) 1
  have hn : n ≠ 0 := by simpa only [C.setup_n] using C.setup.n_ne_zero
  have hi : i < n := by simpa only [C.setup_i, C.setup_n] using C.setup.i_lt
  have hj : j < n := by simpa only [C.setup_j, C.setup_n] using C.setup.j_lt
  have hlambda : 1 ≤ lambda := by
    simpa only [C.setup_lambda] using C.setup.lambda_ge_one
  have hh : 0 < h := by simpa only [C.setup_energy] using C.setup.h₀_pos
  have hhHalf : h < 1 / 2 := by
    simpa only [C.setup_energy] using C.setup.h₀_lt_half
  obtain ⟨a, b, ha, hah, hhb, hb, hreturn⟩ :=
    C.exists_compactReturnIterationInterval
  obtain ⟨Uorient, hUorientOpen, hbaseOrient, horient⟩ :=
    exists_chebyshevOrientedAngularTube hn hi hj hlambda hh hhHalf
      hP.continuous
  obtain ⟨Ulocal, hUlocalOpen, hbaseLocal, hlocal⟩ :=
    exists_chebyshevLocalizedPositiveRayTube hn hi hj hlambda hh hhHalf
      isOpen_Ioo ⟨hah, hhb⟩
  let U : Set PhaseSpace := Uorient ∩ Ulocal
  have hUopen : IsOpen U := hUorientOpen.inter hUlocalOpen
  have hbaseU : Set.range (chebyshevPhaseOrbit n i j lambda h) ⊆ U := by
    intro z hz
    exact ⟨hbaseOrient hz, hbaseLocal hz⟩
  have hcarrier := C.eventually_periodicOrbitAt_carrier_subset hUopen hbaseU
  have hfield : ∀ mu : ℝ, ContDiff ℝ 1
      (fun z : PhaseSpace => chebyshevPerturbedPhaseVector
        n lambda P mu z) := by
    intro mu
    exact (contDiff_chebyshevPerturbedParameter hP n lambda).comp
      ((contDiff_const : ContDiff ℝ 1 (fun _ : PhaseSpace => mu)).prodMk
        contDiff_id)
  filter_upwards [hreturn, horient, hcarrier]
    with mu hreturnMu horientMu hcarrierMu
  intro hmu
  rcases hreturnMu hmu with ⟨hcont, hmono, hunique, hstep⟩
  rcases hcarrierMu hmu with ⟨A, hAU⟩
  refine ⟨A, U, hUopen, hAU, ?_⟩
  intro O' hO'U
  have hO'orient : O'.carrier ⊆ Uorient := fun z hz => (hO'U hz).1
  rcases O'.exists_mem_chebyshevPositiveRay_of_subset hO'orient
      (fun z hz => (horientMu z hz).1)
      (fun z hz => (horientMu z hz).2) with
    ⟨z₀, hz₀carrier, hz₀y, hz₀x⟩
  have hz₀local := hlocal z₀ (hO'U hz₀carrier).2 hz₀y hz₀x
  let e₀ : ℝ := chebyshevPhaseEnergy n lambda z₀
  let f : ℝ → ℝ := C.setup.energyReturnMap mu
  let sec : ℝ → PhaseSpace := fun e =>
    chebyshevPhaseSectionPoint C.setup.n C.setup.i C.setup.j
      C.setup.lambda e
  have he₀ : e₀ ∈ Set.Icc a b := ⟨hz₀local.1.1.le, hz₀local.1.2.le⟩
  have hz₀sec : z₀ = sec e₀ := by
    simpa only [e₀, sec, C.setup_n, C.setup_i, C.setup_j,
      C.setup_lambda] using hz₀local.2
  have hsec₀ : sec e₀ ∈ O'.carrier := by
    rw [← hz₀sec]
    exact hz₀carrier
  have hiter : ∀ k : ℕ,
      (f^[k]) e₀ ∈ Set.Icc a b ∧ sec ((f^[k]) e₀) ∈ O'.carrier := by
    intro k
    induction k with
    | zero => simpa using And.intro he₀ hsec₀
    | succ k ih =>
        let ek : ℝ := (f^[k]) e₀
        have hek : ek ∈ Set.Icc a b := ih.1
        rcases hstep ek hek with ⟨hT, hsegment, hendpoint, hy, hx⟩
        have hflowCarrier := C.setup.localFlow.apply_mem_periodicOrbit_carrier
          hT.le (hfield mu) O' ih.2 hsegment
        have hreturnCarrier : C.setup.returnPoint (mu, ek) ∈ O'.carrier := by
          rw [C.setup.returnPoint_eq_flow]
          simpa only [C1LocalFlow.chebyshevByEnergy, sec] using hflowCarrier
        have hreturnUlocal : C.setup.returnPoint (mu, ek) ∈ Ulocal :=
          (hO'U hreturnCarrier).2
        have hy' : chebyshevSignedForwardY n i j lambda
            (C.setup.returnPoint (mu, ek)) = 0 := by
          simpa only [C.setup_n, C.setup_i, C.setup_j, C.setup_lambda] using hy
        have hx' : 0 < chebyshevForwardX n
            (C.setup.returnPoint (mu, ek)) := by
          simpa only [C.setup_n] using hx
        have hlocalized := hlocal (C.setup.returnPoint (mu, ek))
          hreturnUlocal hy' hx'
        have henergyEq : chebyshevPhaseEnergy n lambda
            (C.setup.returnPoint (mu, ek)) = f ek := by
          have hm := C.setup.energyReturnMap_eq_returnCoordinate mu ek
          change C.setup.energyReturnMap mu ek =
            chebyshevPhaseEnergy C.setup.n C.setup.lambda
              (C.setup.returnPoint (mu, ek)) at hm
          simpa only [f, C.setup_n, C.setup_lambda] using hm.symm
        have hfek : f ek ∈ Set.Icc a b := by
          rw [← henergyEq]
          exact ⟨hlocalized.1.1.le, hlocalized.1.2.le⟩
        have hsecCarrier : sec (f ek) ∈ O'.carrier := by
          rw [hendpoint] at hreturnCarrier
          simpa only [sec, f] using hreturnCarrier
        have hnext : (f^[k.succ]) e₀ = f ek := by
          simpa only [ek] using Function.iterate_succ_apply' f k e₀
        rw [hnext]
        exact ⟨hfek, hsecCarrier⟩
  obtain ⟨ell, hell, hellFixed, hellLim⟩ :=
    exists_fixedPoint_limit_of_iterates_mem_Icc hcont hmono
      (fun k => (hiter k).1)
  have hellPos : 0 < ell := ha.trans_le hell.1
  have hellHalf : ell < 1 / 2 := hell.2.trans_lt hb
  have hsecLim : Tendsto (fun k : ℕ => sec ((f^[k]) e₀)) atTop
      (𝓝 (sec ell)) := by
    exact (contDiffAt_chebyshevPhaseSectionPoint C.setup.n C.setup.i
      C.setup.j C.setup.lambda hellPos hellHalf).continuousAt.tendsto.comp hellLim
  have hellCarrier : sec ell ∈ O'.carrier :=
    O'.isCompact_carrier.isClosed.mem_of_tendsto hsecLim
      (Eventually.of_forall fun k => (hiter k).2)
  have hellRoot : ell = C.continuation.root mu :=
    hunique ell hell hellFixed
  have hrootCarrier : sec (C.continuation.root mu) ∈ A.orbit.carrier := by
    rw [A.orbit_carrier]
    refine ⟨0, ?_⟩
    rw [periodicExtension_zero]
    have hzero := C.setup.localFlow.chebyshevByEnergy_initial
      C.setup.n C.setup.i C.setup.j C.setup.lambda mu
        (C.continuation.root mu)
        (C.setup.localFlow.zero_mem mu _)
    simpa only [ChebyshevReturnSetup.returnCurve, sec] using hzero
  rw [hellRoot] at hellCarrier
  exact O'.carrier_eq_of_mem_of_mem (hfield mu) A.orbit
    hellCarrier hrootCarrier

end Hilbert16
