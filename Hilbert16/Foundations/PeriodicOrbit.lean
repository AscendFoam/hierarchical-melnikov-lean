import Hilbert16.Foundations.PolynomialVectorField
import Mathlib.Analysis.ODE.Basic

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

/-- Cardinal lower-bound interface for (not yet necessarily hyperbolic) limit cycles. -/
def HasAtLeastLimitCycles (X : PhaseSpace → PhaseSpace) (L : ℕ) : Prop :=
  ∃ C : Fin L → LimitCycle X, Function.Injective C

end Hilbert16
