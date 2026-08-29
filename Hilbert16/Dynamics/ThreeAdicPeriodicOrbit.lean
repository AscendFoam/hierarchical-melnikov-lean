import Hilbert16.Dynamics.ReturnPeriodicOrbit
import Hilbert16.Dynamics.ThreeAdicReturnPersistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Filter Set
open scoped Topology

/-!
# Actual periodic orbits at the common three-adic parameter
-/

/-- All data attached to one continued simple root after a concrete
nonzero perturbation parameter has been selected.  In particular, the
return-map fixed point is now packaged as an actual global periodic orbit
of the same audited polynomial vector field. -/
structure ChebyshevPolynomialPeriodicOrbitAt
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀)
    (mu : ℝ) where
  energy_fixed :
    C.setup.energyReturnMap mu (C.continuation.root mu) =
      C.continuation.root mu
  multiplier : ℝ
  multiplier_deriv : HasDerivAt (C.setup.energyReturnMap mu) multiplier
    (C.continuation.root mu)
  multiplier_ne_one : multiplier ≠ 1
  orbit : PeriodicOrbit
    (fun z => chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) mu z)
  orbit_carrier : orbit.carrier = Set.range
    (periodicExtension
      (C.setup.returnTime.time (mu, C.continuation.root mu))
      (C.setup.returnCurve (mu, C.continuation.root mu)))

/-- Along the implicit simple-root branch, every sufficiently small
nonzero parameter produces the complete fixed-point, multiplier, and
global-periodic-orbit package. -/
theorem ChebyshevPolynomialReturnCertificate.eventually_periodicOrbitAt
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀) :
    ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      Nonempty (ChebyshevPolynomialPeriodicOrbitAt C mu) := by
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
  have hX : ∀ (mu : ℝ) (z : PhaseSpace),
      chebyshevPerturbedPhaseVector n lambda
          (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) mu z =
        chebyshevPerturbedPhaseVector C.setup.n C.setup.lambda
          (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) mu z := by
    intro mu z
    rw [C.setup_n, C.setup_lambda]
  have horbit := hpath.eventually
    (C.setup.eventually_exists_periodicOrbit_of_energy_fixed
      (mvPolynomialProdEval (chebyshevPPolynomial n S₀)) hX)
  filter_upwards [C.eventually_fixed_hyperbolic, horbit]
    with mu hhyper horbitMu
  intro hmu
  rcases hhyper hmu with ⟨hfixed, rho, hrho, hrhoNe⟩
  rcases horbitMu hfixed with ⟨O, hO⟩
  exact ⟨{
    energy_fixed := hfixed
    multiplier := rho
    multiplier_deriv := hrho
    multiplier_ne_one := hrhoNe
    orbit := O
    orbit_carrier := hO }⟩

/-- Finiteness upgrades the pointwise periodic-orbit germs to one common
positive perturbation parameter. -/
theorem exists_commonPositiveParameter_with_periodicOrbits
    {alpha : Type*} [Fintype alpha]
    {n i j : alpha → ℕ} {lambda h : alpha → ℝ}
    {S₀ : alpha → MvPolynomial (Fin 2) ℝ}
    (C : ∀ a, ChebyshevPolynomialReturnCertificate
      (n a) (i a) (j a) (lambda a) (h a) (S₀ a)) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ a,
      Nonempty (ChebyshevPolynomialPeriodicOrbitAt (C a) mu) := by
  have hall : ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ a, mu ≠ 0 →
      Nonempty (ChebyshevPolynomialPeriodicOrbitAt (C a) mu) := by
    rw [Filter.eventually_all]
    intro a
    exact (C a).eventually_periodicOrbitAt
  have hallWithin : ∀ᶠ mu in 𝓝[>] (0 : ℝ),
      0 < mu ∧ ∀ a, mu ≠ 0 →
        Nonempty (ChebyshevPolynomialPeriodicOrbitAt (C a) mu) := by
    filter_upwards [self_mem_nhdsWithin,
      hall.filter_mono inf_le_left] with mu hmu hallmu
    exact ⟨hmu, hallmu⟩
  rcases hallWithin.exists with ⟨mu, hmu, hmuAll⟩
  exact ⟨mu, hmu, fun a => hmuAll a hmu.ne'⟩

/-- The exact three-adic counting family is realized, for one common
positive perturbation parameter, by genuine global periodic orbits of one
actual polynomial vector field. -/
theorem threeAdicPolynomialCommonPeriodicOrbits
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
            Nonempty (ChebyshevPolynomialPeriodicOrbitAt (C q) mu) := by
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
  exact ⟨blockCoeff, root, zeta, hzeta, hinj, C,
    exists_commonPositiveParameter_with_periodicOrbits C⟩

end Hilbert16
