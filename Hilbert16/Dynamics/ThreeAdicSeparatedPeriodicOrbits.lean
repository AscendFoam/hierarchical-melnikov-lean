import Hilbert16.Dynamics.ThreeAdicOrbitGeometry
import Hilbert16.Dynamics.ReturnCarrierStability
import Hilbert16.Dynamics.ReturnTubeIsolation
import Hilbert16.Dynamics.FiniteCompactSeparation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Filter Set
open scoped Topology

/-!
# Pairwise separated actual three-adic periodic orbits
-/

/-- The exact three-adic family is realized at one common positive
perturbation parameter by pairwise-disjoint global periodic-orbit carriers
of one actual polynomial vector field. -/
theorem threeAdicPolynomialCommonSeparatedPeriodicOrbits
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (blockCoeff : ThreeAdicMode r → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ)
        (zeta : ℝ),
        0 < zeta ∧
        (∀ c, Function.Injective (fun s => root c s zeta)) ∧
        ∃ C : ∀ q : ThreeAdicCycleIndex r,
            ChebyshevPolynomialReturnCertificate
              (3 ^ r)
              (threeAdicRowIndex (threeAdicCycleCell q).2.1)
              (threeAdicRowIndex (threeAdicCycleCell q).2.2)
              lambda
              (root (threeAdicCycleCell q) (threeAdicCycleRootSlot q) zeta)
              (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff),
          ∃ (mu : ℝ) (A : ∀ q : ThreeAdicCycleIndex r,
              ChebyshevPolynomialPeriodicOrbitAt (C q) mu),
            0 < mu ∧ Pairwise (fun q p =>
              Disjoint (A q).orbit.carrier (A p).orbit.carrier) ∧
              (∀ q, (A q).orbit.IsIsolated) ∧
              ∀ q, IsLocalPoincareReturnMap
                (fun z => chebyshevPerturbedPhaseVector (3 ^ r) lambda
                  (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r)
                    (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) mu z)
                (fun e => chebyshevPhaseSectionPoint
                  (C q).setup.n (C q).setup.i (C q).setup.j
                    (C q).setup.lambda e)
                ((C q).setup.energyReturnMap mu)
                ((C q).continuation.root mu) := by
  rcases threeAdicPolynomialReturnCertificateRealization hr with
    ⟨Lambda, hLambda, hrealize⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  rcases hrealize lambda hlambda with ⟨blockCoeff, root, hevent⟩
  have hselect : ∀ᶠ zeta in 𝓝[>] (0 : ℝ),
      0 < zeta ∧
      (∀ c, Function.Injective (fun s => root c s zeta)) ∧
      ∀ c (s : Fin (threeAdicBlockRootCount c.1)),
        Nonempty (ChebyshevPolynomialReturnCertificate
          (3 ^ r) (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
          lambda (root c s zeta)
          (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff)) := by
    filter_upwards [self_mem_nhdsWithin, hevent] with zeta hzeta hcert
    exact ⟨hzeta, hcert.1, hcert.2⟩
  rcases hselect.exists with ⟨zeta, hzeta, hinj, hcert⟩
  let D : ∀ c : ThreeAdicTensorCell r,
      ∀ s : Fin (threeAdicBlockRootCount c.1),
        ChebyshevPolynomialReturnCertificate
          (3 ^ r) (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
          lambda (root c s zeta)
          (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff) :=
    fun c s => Classical.choice (hcert c s)
  let C : ∀ q : ThreeAdicCycleIndex r,
      ChebyshevPolynomialReturnCertificate
        (3 ^ r)
        (threeAdicRowIndex (threeAdicCycleCell q).2.1)
        (threeAdicRowIndex (threeAdicCycleCell q).2.2)
        lambda
        (root (threeAdicCycleCell q) (threeAdicCycleRootSlot q) zeta)
        (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff) :=
    fun q => D (threeAdicCycleCell q) (threeAdicCycleRootSlot q)
  have hpos : ∀ c s, 0 < root c s zeta := by
    intro c s
    simpa only [(D c s).setup_energy] using (D c s).setup.h₀_pos
  have hupper : ∀ c s,
      root c s zeta < Spikes.chebyshevCommonEnergyUpper := by
    intro c s
    exact (D c s).energy_lt_commonUpper
  let K : ThreeAdicCycleIndex r → Set PhaseSpace :=
    threeAdicUnperturbedCarrier lambda zeta root
  have hKcompact : ∀ q, IsCompact (K q) := by
    intro q
    exact isCompact_threeAdicUnperturbedCarrier lambda zeta root q
  have hKpair : Pairwise (fun q p => Disjoint (K q) (K p)) := by
    simpa [K] using threeAdicUnperturbedCarrier_pairwise_disjoint
      hr (hLambda.trans (le_of_lt hlambda)) root hinj hpos hupper
  rcases exists_pairwiseDisjoint_open_supersets K hKcompact hKpair with
    ⟨U, hU, hUpair⟩
  have hallCarrier : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ q, mu ≠ 0 →
      ∃ A : ChebyshevPolynomialPeriodicOrbitAt (C q) mu,
        A.orbit.carrier ⊆ U q := by
    rw [Filter.eventually_all]
    intro q
    apply (C q).eventually_periodicOrbitAt_carrier_subset (hU q).1
    simpa [K, C, D, threeAdicUnperturbedCarrier] using (hU q).2
  have hallIsolated : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ q, mu ≠ 0 →
      ∃ A : ChebyshevPolynomialPeriodicOrbitAt (C q) mu,
        A.orbit.IsIsolated := by
    rw [Filter.eventually_all]
    intro q
    exact (C q).eventually_isolatedPeriodicOrbitAt
  have hallPoincare : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ q, mu ≠ 0 →
      IsLocalPoincareReturnMap
        (fun z => chebyshevPerturbedPhaseVector (3 ^ r) lambda
          (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r)
            (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) mu z)
        (fun e => chebyshevPhaseSectionPoint
          (C q).setup.n (C q).setup.i (C q).setup.j (C q).setup.lambda e)
        ((C q).setup.energyReturnMap mu)
        ((C q).continuation.root mu) := by
    rw [Filter.eventually_all]
    intro q
    exact (C q).eventually_isLocalPoincareReturnMap
  have hall : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ q, mu ≠ 0 →
      ∃ A : ChebyshevPolynomialPeriodicOrbitAt (C q) mu,
        A.orbit.carrier ⊆ U q ∧ A.orbit.IsIsolated ∧
        IsLocalPoincareReturnMap
          (fun z => chebyshevPerturbedPhaseVector (3 ^ r) lambda
            (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r)
              (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) mu z)
          (fun e => chebyshevPhaseSectionPoint
            (C q).setup.n (C q).setup.i (C q).setup.j (C q).setup.lambda e)
          ((C q).setup.energyReturnMap mu)
          ((C q).continuation.root mu) := by
    filter_upwards [hallCarrier, hallIsolated, hallPoincare]
      with mu hcarrier hisolated hpoincare
    intro q hmu
    rcases hcarrier q hmu with ⟨A, hAsub⟩
    rcases hisolated q hmu with ⟨B, hBisolated⟩
    have horbit : A.orbit = B.orbit := by
      apply PeriodicOrbit.ext
      exact A.orbit_carrier.trans B.orbit_carrier.symm
    refine ⟨A, hAsub, ?_, hpoincare q hmu⟩
    rw [horbit]
    exact hBisolated
  have hallWithin : ∀ᶠ mu in 𝓝[>] (0 : ℝ),
      0 < mu ∧ ∀ q, mu ≠ 0 →
        ∃ A : ChebyshevPolynomialPeriodicOrbitAt (C q) mu,
          A.orbit.carrier ⊆ U q ∧ A.orbit.IsIsolated ∧
          IsLocalPoincareReturnMap
            (fun z => chebyshevPerturbedPhaseVector (3 ^ r) lambda
              (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r)
                (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) mu z)
            (fun e => chebyshevPhaseSectionPoint
              (C q).setup.n (C q).setup.i (C q).setup.j (C q).setup.lambda e)
            ((C q).setup.energyReturnMap mu)
            ((C q).continuation.root mu) := by
    filter_upwards [self_mem_nhdsWithin,
      hall.filter_mono inf_le_left] with mu hmu hallmu
    exact ⟨hmu, hallmu⟩
  rcases hallWithin.exists with ⟨mu, hmu, hmuAll⟩
  have hAexists : ∀ q, ∃ A : ChebyshevPolynomialPeriodicOrbitAt (C q) mu,
      A.orbit.carrier ⊆ U q ∧ A.orbit.IsIsolated ∧
      IsLocalPoincareReturnMap
        (fun z => chebyshevPerturbedPhaseVector (3 ^ r) lambda
          (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r)
            (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) mu z)
        (fun e => chebyshevPhaseSectionPoint
          (C q).setup.n (C q).setup.i (C q).setup.j (C q).setup.lambda e)
        ((C q).setup.energyReturnMap mu)
        ((C q).continuation.root mu) :=
    fun q => hmuAll q hmu.ne'
  choose A hAsub hAisolated hApoincare using hAexists
  refine ⟨blockCoeff, root, zeta, hzeta, hinj, C, mu, A, hmu, ?_,
    hAisolated, hApoincare⟩
  intro q p hqp
  exact (hUpair hqp).mono (hAsub q) (hAsub p)

/-- The full standard-hyperbolic realization theorem: at the exact audited
degree ceiling there is one polynomial vector field carrying the three-adic
lower bound as a finite injective family of genuine hyperbolic limit cycles. -/
theorem exists_threeAdicPolynomialVectorField_with_hyperbolicLimitCycles
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ lambda : ℝ, 1 < lambda ∧
      ∃ X : PolyVectorField,
        X.degree ≤ ((4 * 3 ^ r - 5 : ℕ) : WithBot ℕ) ∧
        HasAtLeastHyperbolicLimitCycles X.eval (cycleLowerBound r) := by
  classical
  rcases threeAdicPolynomialCommonSeparatedPeriodicOrbits hr with
    ⟨Lambda, hLambda, hrealize⟩
  let lambda : ℝ := Lambda + 1
  have hlambda : Lambda < lambda := by dsimp [lambda]; linarith
  rcases hrealize lambda hlambda with
    ⟨blockCoeff, root, zeta, hzeta, hinj, C, mu, A, hmu, hpair,
      hisolated, hpoincare⟩
  let S : MvPolynomial (Fin 2) ℝ :=
    threeAdicHierarchicalDensityPolynomial r zeta blockCoeff
  let X : PolyVectorField := finalPolyVectorField (3 ^ r) lambda mu S
  have hdegree : X.degree ≤ ((4 * 3 ^ r - 5 : ℕ) : WithBot ℕ) := by
    simpa only [X, S] using
      threeAdicHierarchicalFinalVectorField_degree_le hr lambda mu zeta blockCoeff
  refine ⟨lambda, hLambda.trans_lt hlambda, X, hdegree, ?_⟩
  have hfieldEq : X.eval =
      (fun z : PhaseSpace => chebyshevPerturbedPhaseVector (3 ^ r) lambda
        (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r) S)) mu z) := by
    funext z
    exact finalPolyVectorField_eval_eq_perturbedPhaseVector
      (3 ^ r) lambda mu S z
  rw [hfieldEq]
  let L : ThreeAdicCycleIndex r → HyperbolicLimitCycle
      (fun z : PhaseSpace => chebyshevPerturbedPhaseVector (3 ^ r) lambda
        (mvPolynomialProdEval (chebyshevPPolynomial (3 ^ r) S)) mu z) :=
    fun q => {
      toLimitCycle := {
        orbit := (A q).orbit
        isIsolated := hisolated q }
      isHyperbolic := ⟨{
        sectionMap := fun e => chebyshevPhaseSectionPoint
          (C q).setup.n (C q).setup.i (C q).setup.j (C q).setup.lambda e
        returnMap := (C q).setup.energyReturnMap mu
        fixedCoordinate := (C q).continuation.root mu
        multiplier := (A q).multiplier
        section_fixed_mem := (A q).sectionPoint_mem_orbit
        return_fixed := (A q).energy_fixed
        multiplier_deriv := (A q).multiplier_deriv
        multiplier_pos := (A q).multiplier_pos
        multiplier_ne_one := (A q).multiplier_ne_one
        multiplier_abs_ne_one := (A q).multiplier_abs_ne_one
        isLocalReturn := hpoincare q }⟩ }
  have hLinjective : Function.Injective L := by
    intro q p hL
    by_contra hqp
    have hdis := hpair hqp
    have hcarrierEq : (A q).orbit.carrier = (A p).orbit.carrier :=
      congrArg (fun Z => Z.toLimitCycle.orbit.carrier) hL
    rcases (A q).orbit.carrier_nonempty with ⟨z, hzq⟩
    have hzp : z ∈ (A p).orbit.carrier := by
      rw [← hcarrierEq]
      exact hzq
    exact Set.disjoint_left.1 hdis hzq hzp
  let indexEquiv : Fin (cycleLowerBound r) ≃ ThreeAdicCycleIndex r :=
    (finCongr (card_threeAdicCycleIndex_eq_cycleLowerBound r).symm).trans
      (Fintype.equivFin (ThreeAdicCycleIndex r)).symm
  refine ⟨fun k => L (indexEquiv k), ?_⟩
  exact hLinjective.comp indexEquiv.injective

/-- Forgetting the standard Poincaré certificate recovers the previous
finite injective family of isolated limit cycles. -/
theorem exists_threeAdicPolynomialVectorField_with_limitCycles
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ lambda : ℝ, 1 < lambda ∧
      ∃ X : PolyVectorField,
        X.degree ≤ ((4 * 3 ^ r - 5 : ℕ) : WithBot ℕ) ∧
        HasAtLeastLimitCycles X.eval (cycleLowerBound r) := by
  rcases exists_threeAdicPolynomialVectorField_with_hyperbolicLimitCycles hr with
    ⟨lambda, hlambda, X, hdegree, hcycles⟩
  exact ⟨lambda, hlambda, X, hdegree, hcycles.toHasAtLeastLimitCycles⟩

end Hilbert16
