import Hilbert16.Dynamics.ReturnMelnikovGerm
import Hilbert16.Dynamics.ThreeAdicPolynomialBridge
import Hilbert16.Dynamics.MelnikovPersistence
import Hilbert16.Counting.ThreeAdicCycles

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set
open scoped Topology

namespace Hilbert16

/-!
# Actual polynomial return-map persistence
-/

/-- Complete data produced at one marked simple Melnikov root, including the
actual flow-based return map and its continued hyperbolic fixed point. -/
structure ChebyshevPolynomialReturnCertificate
    (n i j : ℕ) (lambda h : ℝ) (S₀ : MvPolynomial (Fin 2) ℝ) where
  derivative : ℝ
  derivative_ne : derivative ≠ 0
  setup : ChebyshevReturnSetup
    (fun mu x => chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) mu x)
  setup_n : setup.n = n
  setup_i : setup.i = i
  setup_j : setup.j = j
  setup_lambda : setup.lambda = lambda
  setup_energy : setup.h₀ = h
  setup_period : setup.T₀ =
    Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h
  energy_lt_commonUpper : h < Spikes.chebyshevCommonEnergyUpper
  melnikov_zero : setup.melnikovIntegral
    (chebyshevEnergyProduction n
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀))) (0, h) = 0
  melnikov_deriv : HasDerivAt
    (fun e => setup.melnikovIntegral
      (chebyshevEnergyProduction n
        (mvPolynomialProdEval (chebyshevPPolynomial n S₀))) (0, e))
    derivative h
  continuation : LocalZeroContinuation
    (setup.melnikovIntegral
      (chebyshevEnergyProduction n
        (mvPolynomialProdEval (chebyshevPPolynomial n S₀)))) (0, h)
  eventually_fixed_hyperbolic : ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
    setup.energyReturnMap mu (continuation.root mu) = continuation.root mu ∧
      ∃ rho : ℝ,
        HasDerivAt (setup.energyReturnMap mu) rho (continuation.root mu) ∧
          rho ≠ 1

/-- Finitely many local return-persistence germs admit one common positive
nonzero perturbation parameter. -/
theorem exists_commonPositiveParameter_of_returnCertificates
    {alpha : Type*} [Fintype alpha]
    {n i j : alpha → ℕ} {lambda h : alpha → ℝ}
    {S₀ : alpha → MvPolynomial (Fin 2) ℝ}
    (C : ∀ a, ChebyshevPolynomialReturnCertificate
      (n a) (i a) (j a) (lambda a) (h a) (S₀ a)) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ a,
      (C a).setup.energyReturnMap mu ((C a).continuation.root mu) =
          (C a).continuation.root mu ∧
        ∃ rho : ℝ,
          HasDerivAt ((C a).setup.energyReturnMap mu) rho
            ((C a).continuation.root mu) ∧ rho ≠ 1 := by
  have hall : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ a, mu ≠ 0 →
      (C a).setup.energyReturnMap mu ((C a).continuation.root mu) =
          (C a).continuation.root mu ∧
        ∃ rho : ℝ,
          HasDerivAt ((C a).setup.energyReturnMap mu) rho
            ((C a).continuation.root mu) ∧ rho ≠ 1 := by
    rw [Filter.eventually_all]
    intro a
    exact (C a).eventually_fixed_hyperbolic
  have hallWithin : ∀ᶠ mu in 𝓝[>] (0 : ℝ),
      0 < mu ∧ ∀ a, mu ≠ 0 →
        (C a).setup.energyReturnMap mu ((C a).continuation.root mu) =
            (C a).continuation.root mu ∧
          ∃ rho : ℝ,
            HasDerivAt ((C a).setup.energyReturnMap mu) rho
              ((C a).continuation.root mu) ∧ rho ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      hall.filter_mono inf_le_left] with mu hmu hallmu
    exact ⟨hmu, hallmu⟩
  rcases hallWithin.exists with ⟨mu, hmu, hmuAll⟩
  exact ⟨mu, hmu, fun a => hmuAll a hmu.ne'⟩

/-- Convert the exact counting index into its marked tensor cell. -/
def threeAdicCycleCell {r : ℕ} (q : ThreeAdicCycleIndex r) :
    ThreeAdicTensorCell r :=
  ⟨(q.1, q.2.1), (q.2.2.1, q.2.2.2.1)⟩

/-- Root slot carried by the exact counting index. -/
def threeAdicCycleRootSlot {r : ℕ} (q : ThreeAdicCycleIndex r) :
    Fin (threeAdicBlockRootCount (threeAdicCycleCell q).1) :=
  q.2.2.2.2

/-- A simple zero of the compiled first Melnikov displacement produces an
actual finite `C¹` flow, a genuine return setup for the same audited
polynomial field, and a locally continued hyperbolic fixed point. -/
theorem exists_chebyshevPolynomialReturnPersistence
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h d : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) (S₀ : MvPolynomial (Fin 2) ℝ)
    (hzero : Spikes.chebyshevFirstMelnikovDisplacement n i j
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) lambda h = 0)
    (hderiv : HasDerivAt
      (fun e => Spikes.chebyshevFirstMelnikovDisplacement n i j
        (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) lambda e) d h)
    (hd : d ≠ 0) :
    let P := mvPolynomialProdEval (chebyshevPPolynomial n S₀)
    let X := fun mu x => chebyshevPerturbedPhaseVector n lambda P mu x
    ∃ R : ChebyshevReturnSetup X,
      R.n = n ∧ R.i = i ∧ R.j = j ∧ R.lambda = lambda ∧ R.h₀ = h ∧
      R.T₀ = Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h ∧
      R.melnikovIntegral (chebyshevEnergyProduction n P) (0, h) = 0 ∧
      HasDerivAt
        (fun e => R.melnikovIntegral (chebyshevEnergyProduction n P) (0, e)) d h ∧
      ∃ C : LocalZeroContinuation
          (R.melnikovIntegral (chebyshevEnergyProduction n P)) (0, h),
        ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
          R.energyReturnMap mu (C.root mu) = C.root mu ∧
            ∃ rho : ℝ, HasDerivAt (R.energyReturnMap mu) rho (C.root mu) ∧
              rho ≠ 1 := by
  dsimp only
  let P : ℝ × ℝ → ℝ := mvPolynomialProdEval (chebyshevPPolynomial n S₀)
  let X : ℝ → PhaseSpace → PhaseSpace := fun mu x =>
    chebyshevPerturbedPhaseVector n lambda P mu x
  obtain ⟨N, delta, hdelta, hmesh, hsegment⟩ :=
    exists_chebyshevPolynomialFiniteC1LocalFlow_sectionPeriod
      hn hi hj hlambda hh.le hhHalf S₀
  let Phi : C1LocalFlow X :=
    chebyshevPolynomialFiniteC1LocalFlow n lambda S₀ delta hdelta N
  have hXzero : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z := by
    intro z
    apply phaseSpaceProdEquiv.injective
    simp [X, P, chebyshevPerturbedPhaseVector, chebyshevPerturbedVector,
      chebyshevPhaseHamiltonianVector, Spikes.chebyshevHamiltonianVector,
      Spikes.chebyshevHamiltonianDx, Spikes.chebyshevHamiltonianDy]
  let R : ChebyshevReturnSetup X :=
    Phi.chebyshevReturnSetupOfSectionPeriod
      hn hi hj hlambda hh hhHalf hXzero hsegment
  have hP : ContDiff ℝ 1 P := by
    exact contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S₀) 1
  have heq :
      (fun e => R.melnikovIntegral (chebyshevEnergyProduction n P) (0, e)) =ᶠ[𝓝 h]
        (fun e => Spikes.chebyshevFirstMelnikovDisplacement n i j P lambda e) := by
    simpa [R, P, X, Phi] using
      Phi.eventually_chebyshevReturnSetupOfSectionPeriod_melnikov_eq_first
        hn hi hj hlambda hh hhHalf hXzero hsegment hP.continuous
  have hzeroR :
      R.melnikovIntegral (chebyshevEnergyProduction n P) (0, h) = 0 := by
    have heqAt := heq.self_of_nhds
    change (fun e => R.melnikovIntegral
      (chebyshevEnergyProduction n P) (0, e)) h = 0
    rw [heqAt]
    simpa [P] using hzero
  have hderivR : HasDerivAt
      (fun e => R.melnikovIntegral (chebyshevEnergyProduction n P) (0, e)) d h :=
    hderiv.congr_of_eventuallyEq heq
  have hXall : ∀ (mu : ℝ) (z : PhaseSpace),
      X mu z = chebyshevPerturbedPhaseVector R.n R.lambda P mu z := by
    intro mu z
    rfl
  have hpersist := R.eventually_energyReturnMap_fixed_and_hyperbolic
    P hXall hP hzeroR hderivR hd
  let C := ContDiffAt.localZeroContinuation_of_hasDerivAt
    (R.contDiffAt_actualMelnikov P hP) hzeroR hderivR hd
  refine ⟨R, rfl, rfl, rfl, rfl, rfl, rfl, hzeroR, hderivR, C, ?_⟩
  simpa [C] using hpersist

/-- Structure-valued form of `exists_chebyshevPolynomialReturnPersistence`. -/
theorem nonempty_chebyshevPolynomialReturnCertificate
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h d : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhUpper : h < Spikes.chebyshevCommonEnergyUpper)
    (S₀ : MvPolynomial (Fin 2) ℝ)
    (hzero : Spikes.chebyshevFirstMelnikovDisplacement n i j
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) lambda h = 0)
    (hderiv : HasDerivAt
      (fun e => Spikes.chebyshevFirstMelnikovDisplacement n i j
        (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) lambda e) d h)
    (hd : d ≠ 0) :
    Nonempty (ChebyshevPolynomialReturnCertificate n i j lambda h S₀) := by
  rcases exists_chebyshevPolynomialReturnPersistence
    hn hi hj hlambda hh
      (hhUpper.trans Spikes.chebyshevCommonEnergyUpper_lt_half)
      S₀ hzero hderiv hd with
    ⟨R, hRn, hRi, hRj, hRlambda, hRh, hRT, hzeroR, hderivR, C, hC⟩
  exact ⟨{
    derivative := d
    derivative_ne := hd
    setup := R
    setup_n := hRn
    setup_i := hRi
    setup_j := hRj
    setup_lambda := hRlambda
    setup_energy := hRh
    setup_period := hRT
    energy_lt_commonUpper := hhUpper
    melnikov_zero := hzeroR
    melnikov_deriv := hderivR
    continuation := C
    eventually_fixed_hyperbolic := hC }⟩

/-- The concrete three-adic hierarchy now supplies an actual polynomial
return certificate at every marked cell/root, simultaneously for one
coefficient family and one positive hierarchy parameter germ. -/
theorem threeAdicPolynomialReturnCertificateRealization
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (blockCoeff : ThreeAdicMode r → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ),
        ∀ᶠ zeta in 𝓝[>] 0,
          (∀ c, Function.Injective (fun s => root c s zeta)) ∧
          ∀ c, ∀ s : Fin (threeAdicBlockRootCount c.1),
              Nonempty (ChebyshevPolynomialReturnCertificate
                (3 ^ r) (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
                lambda (root c s zeta)
                (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff)) := by
  rcases threeAdicPolynomialMelnikovSimpleRootRealization hr with
    ⟨Lambda, hLambda, hrealize⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  rcases hrealize lambda hlambda with ⟨blockCoeff, root, hevent⟩
  refine ⟨blockCoeff, root, ?_⟩
  filter_upwards [hevent] with zeta hzeta
  refine ⟨hzeta.1, ?_⟩
  intro c s
  rcases hzeta.2 c s with
    ⟨hzero, hpos, hquarter, dM, hdM, hderiv⟩
  apply nonempty_chebyshevPolynomialReturnCertificate
    (pow_ne_zero _ (by decide))
    (threeAdicRowIndex_lt_pow c.1.1.2 c.2.1)
    (threeAdicRowIndex_lt_pow c.1.2.2 c.2.2)
    (hLambda.trans (le_of_lt hlambda)) hpos hquarter _
    hzero hderiv hdM

/-- After the hierarchy parameter is selected, finiteness of the exact
cycle-index type gives one common positive perturbation parameter for all
actual polynomial return-map fixed points and all their nonunit
multipliers. -/
theorem threeAdicPolynomialCommonReturnParameter
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
          ∃ mu : ℝ, 0 < mu ∧ ∀ q,
            (C q).setup.energyReturnMap mu ((C q).continuation.root mu) =
                (C q).continuation.root mu ∧
              ∃ rho : ℝ,
                HasDerivAt ((C q).setup.energyReturnMap mu) rho
                  ((C q).continuation.root mu) ∧ rho ≠ 1 := by
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
  let C : ∀ q : ThreeAdicCycleIndex r,
      ChebyshevPolynomialReturnCertificate
        (3 ^ r)
        (threeAdicRowIndex (threeAdicCycleCell q).2.1)
        (threeAdicRowIndex (threeAdicCycleCell q).2.2)
        lambda
        (root (threeAdicCycleCell q) (threeAdicCycleRootSlot q) zeta)
        (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff) :=
    fun q => Classical.choice
      (hcert (threeAdicCycleCell q) (threeAdicCycleRootSlot q))
  have hcommon := exists_commonPositiveParameter_of_returnCertificates C
  exact ⟨blockCoeff, root, zeta, hzeta, hinj, C, hcommon⟩

end Hilbert16
