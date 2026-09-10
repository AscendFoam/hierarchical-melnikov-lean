import Hilbert16.Foundations.PolynomialVectorField
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

namespace Hilbert16

open Set

/-- An autonomous vector field viewed through Mathlib's time-dependent ODE interface. -/
def autonomousField (X : PhaseSpace → PhaseSpace) : ℝ → PhaseSpace → PhaseSpace :=
  fun _ x => X x

/-- A nonconstant global integral curve with a positive period. -/
def IsPeriodicIntegralCurve (X : PhaseSpace → PhaseSpace) (γ : ℝ → PhaseSpace) : Prop :=
  ∃ T : ℝ, 0 < T ∧
    IsIntegralCurve γ (autonomousField X) ∧
    (∀ t : ℝ, γ (t + T) = γ t) ∧
    ∃ t : ℝ, γ t ≠ γ 0

/-- A periodic orbit is identified by its carrier set; parametrizations occur only in a
proposition-valued existence certificate. -/
structure PeriodicOrbit (X : PhaseSpace → PhaseSpace) where
  carrier : Set PhaseSpace
  exists_periodicParametrization :
    ∃ γ : ℝ → PhaseSpace, IsPeriodicIntegralCurve X γ ∧ Set.range γ = carrier

@[ext]
theorem PeriodicOrbit.ext {X : PhaseSpace → PhaseSpace} {O₁ O₂ : PeriodicOrbit X}
    (hcarrier : O₁.carrier = O₂.carrier) : O₁ = O₂ := by
  cases O₁
  cases O₂
  cases hcarrier
  rfl

theorem PeriodicOrbit.carrier_nonempty {X : PhaseSpace → PhaseSpace}
    (O : PeriodicOrbit X) : O.carrier.Nonempty := by
  rcases O.exists_periodicParametrization with ⟨γ, hγ, hrange⟩
  rw [← hrange]
  exact Set.range_nonempty γ

theorem PeriodicOrbit.carrier_nontrivial {X : PhaseSpace → PhaseSpace}
    (O : PeriodicOrbit X) : ∃ x ∈ O.carrier, ∃ y ∈ O.carrier, x ≠ y := by
  rcases O.exists_periodicParametrization with ⟨γ, hγ, hrange⟩
  rcases hγ with ⟨T, hT, hIntegral, hperiodic, t, ht⟩
  refine ⟨γ t, ?_, γ 0, ?_, ht⟩
  · rw [← hrange]
    exact ⟨t, rfl⟩
  · rw [← hrange]
    exact ⟨0, rfl⟩

/-- Isolation among periodic-orbit carriers contained in one open neighborhood. -/
def PeriodicOrbit.IsIsolated {X : PhaseSpace → PhaseSpace} (O : PeriodicOrbit X) : Prop :=
  ∃ U : Set PhaseSpace, IsOpen U ∧ O.carrier ⊆ U ∧
    ∀ O' : PeriodicOrbit X, O'.carrier ⊆ U → O'.carrier = O.carrier

/-- A limit cycle is a periodic orbit isolated among nearby periodic-orbit carriers. -/
structure LimitCycle (X : PhaseSpace → PhaseSpace) where
  orbit : PeriodicOrbit X
  isIsolated : orbit.IsIsolated

@[ext]
theorem LimitCycle.ext {X : PhaseSpace → PhaseSpace} {C₁ C₂ : LimitCycle X}
    (hcarrier : C₁.orbit.carrier = C₂.orbit.carrier) : C₁ = C₂ := by
  cases C₁ with
  | mk O₁ h₁ =>
      cases C₂ with
      | mk O₂ h₂ =>
          have hO : O₁ = O₂ := PeriodicOrbit.ext hcarrier
          cases hO
          rfl

/-- A scalar map is locally induced by the autonomous flow on a section if,
near the fixed coordinate, every section point follows an actual positive-
time integral curve to the section point indexed by the returned
coordinate. -/
def IsLocalPoincareReturnMap
    (X : PhaseSpace → PhaseSpace) (sectionMap : ℝ → PhaseSpace)
    (returnMap : ℝ → ℝ) (fixedCoordinate : ℝ) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ fixedCoordinate ∈ U ∧
    ContDiffOn ℝ 1 sectionMap U ∧ Set.InjOn sectionMap U ∧
    ∃ (sectionFunction : PhaseSpace → ℝ)
      (sectionDerivative : ℝ → PhaseSpace →L[ℝ] ℝ)
      (returnTime : ℝ → ℝ) (returnCurve : ℝ → ℝ → PhaseSpace),
      (∀ e ∈ U, sectionFunction (sectionMap e) = 0) ∧
      (∀ e ∈ U,
        HasFDerivAt sectionFunction (sectionDerivative e) (sectionMap e)) ∧
      (∀ e ∈ U, sectionDerivative e (X (sectionMap e)) ≠ 0) ∧
      ∀ e ∈ U,
        0 < returnTime e ∧
        returnCurve e 0 = sectionMap e ∧
        returnCurve e (returnTime e) = sectionMap (returnMap e) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (returnTime e),
          HasDerivAt (returnCurve e) (X (returnCurve e t)) t

/-- Local scalar Poincaré data anchored at a point of a periodic-orbit
carrier.  The dynamics layer constructs this record only from its genuine
flow return map; the foundations layer records the coordinate-independent
spectral datum needed by the public notion of hyperbolicity. -/
structure PoincareMultiplierCertificate {X : PhaseSpace → PhaseSpace}
    (O : PeriodicOrbit X) where
  sectionMap : ℝ → PhaseSpace
  returnMap : ℝ → ℝ
  fixedCoordinate : ℝ
  multiplier : ℝ
  section_fixed_mem : sectionMap fixedCoordinate ∈ O.carrier
  return_fixed : returnMap fixedCoordinate = fixedCoordinate
  multiplier_deriv : HasDerivAt returnMap multiplier fixedCoordinate
  multiplier_pos : 0 < multiplier
  multiplier_ne_one : multiplier ≠ 1
  multiplier_abs_ne_one : |multiplier| ≠ 1
  isLocalReturn :
    IsLocalPoincareReturnMap X sectionMap returnMap fixedCoordinate

/-- A hyperbolic limit cycle is an isolated periodic-orbit carrier equipped
with a genuine local Poincaré multiplier certificate satisfying the standard
spectral condition `|rho| ≠ 1`. -/
structure HyperbolicLimitCycle (X : PhaseSpace → PhaseSpace) where
  toLimitCycle : LimitCycle X
  isHyperbolic : Nonempty (PoincareMultiplierCertificate toLimitCycle.orbit)

@[ext]
theorem HyperbolicLimitCycle.ext
    {X : PhaseSpace → PhaseSpace} {C₁ C₂ : HyperbolicLimitCycle X}
    (hcarrier : C₁.toLimitCycle.orbit.carrier =
      C₂.toLimitCycle.orbit.carrier) : C₁ = C₂ := by
  cases C₁ with
  | mk L₁ h₁ =>
      cases C₂ with
      | mk L₂ h₂ =>
          have hL : L₁ = L₂ := LimitCycle.ext hcarrier
          cases hL
          rfl

/-- A positive real Poincaré multiplier is standard-hyperbolic as soon as it
is different from `1`.  Positivity is essential: without it, `rho = -1`
would be a counterexample. -/
theorem abs_ne_one_of_pos_of_ne_one {rho : ℝ}
    (hpos : 0 < rho) (hne : rho ≠ 1) : |rho| ≠ 1 := by
  simpa [abs_of_pos hpos] using hne

/-- Cardinal lower-bound interface for (not yet necessarily hyperbolic) limit cycles. -/
def HasAtLeastLimitCycles (X : PhaseSpace → PhaseSpace) (L : ℕ) : Prop :=
  ∃ C : Fin L → LimitCycle X, Function.Injective C

/-- Cardinal lower-bound interface for standard hyperbolic limit cycles. -/
def HasAtLeastHyperbolicLimitCycles
    (X : PhaseSpace → PhaseSpace) (L : ℕ) : Prop :=
  ∃ C : Fin L → HyperbolicLimitCycle X, Function.Injective C

/-- A finite injective hyperbolic family remains injective after forgetting
its proposition-valued Poincaré certificate. -/
theorem HasAtLeastHyperbolicLimitCycles.toHasAtLeastLimitCycles
    {X : PhaseSpace → PhaseSpace} {L : ℕ}
    (h : HasAtLeastHyperbolicLimitCycles X L) : HasAtLeastLimitCycles X L := by
  rcases h with ⟨C, hC⟩
  refine ⟨fun k => (C k).toLimitCycle, ?_⟩
  intro i j hij
  apply hC
  apply HyperbolicLimitCycle.ext
  exact congrArg (fun L => L.orbit.carrier) hij

end Hilbert16
