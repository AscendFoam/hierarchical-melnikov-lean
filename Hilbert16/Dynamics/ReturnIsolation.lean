import Hilbert16.Dynamics.PeriodicOrbitUniqueness
import Hilbert16.Dynamics.ThreeAdicPeriodicOrbit
import Mathlib.Analysis.Calculus.Deriv.Inverse

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

/-- A fixed point whose scalar return multiplier is not one is an isolated
fixed point.  Only differentiability at the fixed point is needed. -/
theorem exists_open_fixedPointNeighborhood_of_hasDerivAt_ne_one
    {f : ℝ → ℝ} {e rho : ℝ}
    (hfixed : f e = e) (hderiv : HasDerivAt f rho e)
    (hrho : rho ≠ 1) :
    ∃ V : Set ℝ, IsOpen V ∧ e ∈ V ∧
      ∀ e' ∈ V, f e' = e' → e' = e := by
  let g : ℝ → ℝ := f - id
  have hg : HasDerivAt g (rho - 1) e :=
    hderiv.sub (hasDerivAt_id e)
  have hgne : rho - 1 ≠ 0 := sub_ne_zero.mpr hrho
  have hge : g e = 0 := by
    simpa [g] using sub_eq_zero.mpr hfixed
  have hpunctured : ∀ᶠ x in 𝓝[≠] e, g x ≠ 0 := by
    simpa only [hge] using hg.eventually_ne (c := g e) hgne
  rw [eventually_nhdsWithin_iff] at hpunctured
  have hlocal : ∀ᶠ x in 𝓝 e, g x = 0 → x = e := by
    filter_upwards [hpunctured] with x hx
    intro hgzero
    by_contra hxe
    exact hx hxe hgzero
  rcases mem_nhds_iff.mp hlocal with ⟨V, hVsub, hVopen, heV⟩
  refine ⟨V, hVopen, heV, ?_⟩
  intro e' he' hfix'
  exact hVsub he' (by simpa [g] using sub_eq_zero.mpr hfix')

/-- The multiplier stored in a concrete periodic-orbit package supplies an
open energy neighborhood in which its continued return fixed point is the
only fixed point. -/
theorem ChebyshevPolynomialPeriodicOrbitAt.exists_open_energyNeighborhood
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    {C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀}
    {mu : ℝ} (A : ChebyshevPolynomialPeriodicOrbitAt C mu) :
    ∃ V : Set ℝ, IsOpen V ∧ C.continuation.root mu ∈ V ∧
      ∀ e ∈ V,
        C.setup.energyReturnMap mu e = e →
          e = C.continuation.root mu := by
  exact exists_open_fixedPointNeighborhood_of_hasDerivAt_ne_one
    A.energy_fixed A.multiplier_deriv A.multiplier_ne_one

/-- The implicit zero continuation and the exact Melnikov factorization give
one fixed open energy neighborhood of the unperturbed root on which the
continued return fixed point is unique for every sufficiently small nonzero
parameter.  Unlike the multiplier-only neighborhood above, this neighborhood
is uniform in the perturbation parameter. -/
theorem ChebyshevPolynomialReturnCertificate.exists_uniformFixedPointNeighborhood
    {n i j : ℕ} {lambda h : ℝ} {S₀ : MvPolynomial (Fin 2) ℝ}
    (C : ChebyshevPolynomialReturnCertificate n i j lambda h S₀) :
    ∃ V : Set ℝ, IsOpen V ∧ h ∈ V ∧
      ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
        ∀ e ∈ V, C.setup.energyReturnMap mu e = e →
          e = C.continuation.root mu := by
  let P : ℝ × ℝ → ℝ :=
    mvPolynomialProdEval (chebyshevPPolynomial n S₀)
  let D : ℝ × ℝ → ℝ :=
    C.setup.melnikovIntegral (chebyshevEnergyProduction C.setup.n P)
  have hP : ContDiff ℝ 1 P :=
    contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S₀) 1
  have hX : ∀ (mu : ℝ) (z : PhaseSpace),
      chebyshevPerturbedPhaseVector n lambda P mu z =
        chebyshevPerturbedPhaseVector C.setup.n C.setup.lambda P mu z := by
    intro mu z
    rw [C.setup_n, C.setup_lambda]
  obtain ⟨W, hWopen, hbaseW, hfactor⟩ :=
    C.setup.exists_actualMelnikovFactorizationNeighborhood P hX hP
  have hfactorNhds :
      {muh : ℝ × ℝ |
        C.setup.energyReturnMap muh.1 muh.2 =
          normalizedReturnMap D muh.1 muh.2} ∈
        𝓝 ((0 : ℝ), h) := by
    have hbaseW' : ((0 : ℝ), h) ∈ W := by
      simpa [C.setup_energy] using hbaseW
    exact mem_of_superset (hWopen.mem_nhds hbaseW') (by
      intro muh hmuh
      simpa [D] using (hfactor muh hmuh).2)
  have huniqueNhds :
      {muh : ℝ × ℝ |
        D muh = 0 ↔ C.continuation.root muh.1 = muh.2} ∈
        𝓝 ((0 : ℝ), h) := by
    change ∀ᶠ muh in 𝓝 ((0 : ℝ), h),
      D muh = 0 ↔ C.continuation.root muh.1 = muh.2
    simpa only [D, C.setup_n, P] using C.continuation.eventually_unique
  have hgood :
      ({muh : ℝ × ℝ |
        C.setup.energyReturnMap muh.1 muh.2 =
          normalizedReturnMap D muh.1 muh.2} ∩
       {muh : ℝ × ℝ |
        D muh = 0 ↔ C.continuation.root muh.1 = muh.2}) ∈
        𝓝 ((0 : ℝ), h) :=
    inter_mem hfactorNhds huniqueNhds
  rcases mem_nhds_prod_iff.mp hgood with ⟨A, hA, B, hB, hAB⟩
  rcases mem_nhds_iff.mp hB with ⟨V, hVsub, hVopen, hhV⟩
  refine ⟨V, hVopen, hhV, ?_⟩
  filter_upwards [hA] with mu hmuA
  intro hmu e heV hfixed
  have hpair := hAB (show (mu, e) ∈ A ×ˢ B from ⟨hmuA, hVsub heV⟩)
  have hmap : C.setup.energyReturnMap mu e =
      normalizedReturnMap D mu e := hpair.1
  have hDzero : D (mu, e) = 0 := by
    rw [normalizedReturnMap] at hmap
    have hprod : mu * D (mu, e) = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left hmu
  exact (hpair.2.mp hDzero).symm

/-- A reusable last-mile criterion for Poincaré isolation.  Once every
periodic orbit contained in one open return tube is known to hit the local
section at a fixed energy in the isolated fixed-point neighborhood, ODE
uniqueness turns that scalar uniqueness into carrier isolation. -/
theorem PeriodicOrbit.isIsolated_of_returnSection
    {X : PhaseSpace → PhaseSpace} (hX : ContDiff ℝ 1 X)
    (O : PeriodicOrbit X) {f : ℝ → ℝ} {e : ℝ}
    {sectionPoint : ℝ → PhaseSpace}
    (hpoint : sectionPoint e ∈ O.carrier)
    {V : Set ℝ} (_heV : e ∈ V)
    (hunique : ∀ e' ∈ V, f e' = e' → e' = e)
    {U : Set PhaseSpace} (hUopen : IsOpen U) (hOU : O.carrier ⊆ U)
    (hhit : ∀ O' : PeriodicOrbit X, O'.carrier ⊆ U →
      ∃ e' ∈ V, f e' = e' ∧ sectionPoint e' ∈ O'.carrier) :
    O.IsIsolated := by
  refine ⟨U, hUopen, hOU, ?_⟩
  intro O' hO'U
  rcases hhit O' hO'U with ⟨e', he'V, he'fixed, he'carrier⟩
  have heq : e' = e := hunique e' he'V he'fixed
  subst e'
  exact O'.carrier_eq_of_mem_of_mem hX O he'carrier hpoint

end Hilbert16
