import Hilbert16.Asymptotics
import Hilbert16.Dynamics.ThreeAdicSeparatedPeriodicOrbits

set_option autoImplicit false

namespace Hilbert16

/-!
# End-to-end polynomial limit-cycle lower bounds

These statements quantify directly over polynomial vector fields and
finite injective families of actual limit cycles.  No finiteness assumption
for the Hilbert number is needed.
-/

/-- A degree ceiling admits at least `L` actual limit cycles. -/
def DegreeNAdmitsAtLeast (N L : ℕ) : Prop :=
  ∃ X : PolyVectorField,
    X.degree ≤ (N : WithBot ℕ) ∧ HasAtLeastLimitCycles X.eval L

/-- Degree-bounded existence of a finite injective family of standard
hyperbolic limit cycles. -/
def DegreeNAdmitsAtLeastHyperbolic (N L : ℕ) : Prop :=
  ∃ X : PolyVectorField,
    X.degree ≤ (N : WithBot ℕ) ∧
      HasAtLeastHyperbolicLimitCycles X.eval L

theorem DegreeNAdmitsAtLeastHyperbolic.toDegreeNAdmitsAtLeast
    {N L : ℕ} (h : DegreeNAdmitsAtLeastHyperbolic N L) :
    DegreeNAdmitsAtLeast N L := by
  rcases h with ⟨X, hdegree, hcycles⟩
  exact ⟨X, hdegree, hcycles.toHasAtLeastLimitCycles⟩

/-- The exact three-adic subsequence construction with the standard
hyperbolic Poincaré multiplier condition. -/
theorem threeAdic_subsequence_hyperbolicLimitCycle_lower_bound
    {r : ℕ} (hr : 2 ≤ r) :
    DegreeNAdmitsAtLeastHyperbolic
      (subsequenceDegree r) (cycleLowerBound r) := by
  rcases exists_threeAdicPolynomialVectorField_with_hyperbolicLimitCycles
      (show 1 ≤ r by omega) with ⟨lambda, hlambda, X, hdegree, hcycles⟩
  refine ⟨X, ?_, hcycles⟩
  simpa only [subsequenceDegree] using hdegree

/-- The exact three-adic subsequence construction, including the paper's
natural-number count and audited degree ceiling. -/
theorem threeAdic_subsequence_limitCycle_lower_bound
    {r : ℕ} (hr : 2 ≤ r) :
    DegreeNAdmitsAtLeast (subsequenceDegree r) (cycleLowerBound r) := by
  exact (threeAdic_subsequence_hyperbolicLimitCycle_lower_bound hr).toDegreeNAdmitsAtLeast

/-- Direct all-degree form with a finite injective family of standard
hyperbolic limit cycles. -/
theorem polynomial_hyperbolicLimitCycle_lower_bound_asymptotic :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ L : ℕ, DegreeNAdmitsAtLeastHyperbolic N L ∧
        c * (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 ≤ L := by
  refine ⟨hilbertAsymptoticConstant, hilbertAsymptoticConstant_pos,
    144, ?_⟩
  intro N hN
  have hN31 : 31 ≤ N := by omega
  let r : ℕ := allDegreeIndex N
  have hr : 2 ≤ r := two_le_allDegreeIndex hN31
  rcases threeAdic_subsequence_hyperbolicLimitCycle_lower_bound hr with
    ⟨X, hXdegree, hXcycles⟩
  have hdegreeNat : subsequenceDegree r ≤ N := by
    simpa only [r] using (allDegreeIndex_bracket hN31).1
  have hXdegreeN : X.degree ≤ (N : WithBot ℕ) :=
    hXdegree.trans (by exact_mod_cast hdegreeNat)
  have hcount :
      hilbertAsymptoticConstant * (N : ℝ) ^ 2 *
          (Real.log (N : ℝ)) ^ 2 ≤ cycleLowerBound r := by
    apply (asymptoticMonomial_le_explicit hN).trans
    exact le_of_lt ((explicitAllDegreeLowerBound_lt_leading hN31).trans
      (cycleLowerBound_gt_leading hr))
  exact ⟨cycleLowerBound r, ⟨X, hXdegreeN, hXcycles⟩, hcount⟩

/-- Direct all-degree form of the paper's final asymptotic lower bound.
For every sufficiently large degree, the theorem returns a concrete degree-
bounded polynomial field and a finite injective family of its limit cycles. -/
theorem polynomial_limitCycle_lower_bound_asymptotic :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ L : ℕ, DegreeNAdmitsAtLeast N L ∧
        c * (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 ≤ L := by
  rcases polynomial_hyperbolicLimitCycle_lower_bound_asymptotic with
    ⟨c, hc, N₀, hmain⟩
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN
  rcases hmain N hN with ⟨L, hcycles, hcount⟩
  exact ⟨L, hcycles.toDegreeNAdmitsAtLeast, hcount⟩

end Hilbert16
