import Hilbert16.Dynamics.PolynomialPrimitive
import Hilbert16.Dynamics.ThreeAdicMelnikov

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter
open scoped BigOperators Topology

namespace Hilbert16

/-!
# From the three-adic finite density to the audited polynomial perturbation
-/

@[simp]
theorem mvPolynomialProdEval_finsetSum {alpha : Type*}
    (s : Finset alpha) (p : alpha → MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (∑ a ∈ s, p a) z =
      ∑ a ∈ s, mvPolynomialProdEval (p a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

/-- The hierarchy polynomial is exactly the support-indexed polynomial with
the coefficient family used by the compiled Melnikov sum. -/
theorem threeAdicHierarchicalDensityPolynomial_eq_chebyshevDensityPolynomial
    (r : ℕ) (zeta : ℝ) (blockCoeff : ThreeAdicMode r → ℝ) :
    threeAdicHierarchicalDensityPolynomial r zeta blockCoeff =
      chebyshevDensityPolynomial (threeAdicModeSupport r)
        (threeAdicHierarchicalPairCoefficient r zeta blockCoeff) := by
  unfold threeAdicHierarchicalDensityPolynomial
    threeAdicGlobalDensityPolynomial chebyshevDensityPolynomial
    threeAdicModeSupport
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro m _
    rw [threeAdicHierarchicalPairCoefficient_mode]
    rfl
  · exact threeAdicModeFrequencyPair_injective.injOn

/-- Evaluation of the algebraic Chebyshev density polynomial is the finite
sum of its tensor modes. -/
theorem mvPolynomialProdEval_chebyshevDensityPolynomial
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (chebyshevDensityPolynomial support coeff) z =
      ∑ k ∈ support, coeff k *
        ((Polynomial.Chebyshev.T ℝ (k.1 : ℤ)).eval z.1 *
          (Polynomial.Chebyshev.T ℝ (k.2 : ℤ)).eval z.2) := by
  unfold chebyshevDensityPolynomial
  rw [mvPolynomialProdEval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [chebyshevModePolynomial]

/-- The algebraic `q=T_n'(x)T_n'(y)S` evaluates to the same finite density
used by the analytic change-of-variables calculation. -/
theorem mvPolynomialProdEval_chebyshevQPolynomial_eq_finiteChebyshevDensity
    (n : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (z : ℝ × ℝ) :
    mvPolynomialProdEval
        (chebyshevQPolynomial n (chebyshevDensityPolynomial support coeff)) z =
      Spikes.finiteChebyshevDensity n support coeff z := by
  unfold chebyshevQPolynomial
  rw [mvPolynomialProdEval_mul, mvPolynomialProdEval_mul,
    mvPolynomialProdEval_chebyshevDensityPolynomial]
  unfold Spikes.finiteChebyshevDensity
    Spikes.chebyshevDensityMode Spikes.chebyshevForwardDerivative
  simp only [mvPolynomialProdEval_chebyshevDerivativeAt_zero,
    mvPolynomialProdEval_chebyshevDerivativeAt_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Consequently the normalized audited polynomial primitive is pointwise
the same primitive used in the compiled Melnikov formula. -/
theorem mvPolynomialProdEval_chebyshevPPolynomial_eq_firstCoordinatePrimitive
    (n : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (z : ℝ × ℝ) :
    mvPolynomialProdEval
        (chebyshevPPolynomial n (chebyshevDensityPolynomial support coeff)) z =
      Spikes.firstCoordinatePrimitive
        (Spikes.finiteChebyshevDensity n support coeff) z := by
  unfold chebyshevPPolynomial
  rw [mvPolynomialProdEval_integrateAt_eq_firstCoordinatePrimitive]
  congr 1
  funext w
  exact mvPolynomialProdEval_chebyshevQPolynomial_eq_finiteChebyshevDensity
    n support coeff w

/-- The actual hierarchy polynomial primitive and the analytic finite-density
primitive define identical first Melnikov displacements. -/
theorem chebyshevFirstMelnikovDisplacement_threeAdicPolynomial_eq
    (r : ℕ) (lambda zeta : ℝ) (blockCoeff : ThreeAdicMode r → ℝ)
    (c : ThreeAdicTensorCell r) (h : ℝ) :
    Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
        (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
        (mvPolynomialProdEval
          (chebyshevPPolynomial (3 ^ r)
            (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) lambda h =
      Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
        (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
        (Spikes.firstCoordinatePrimitive
          (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
            (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda h := by
  rw [threeAdicHierarchicalDensityPolynomial_eq_chebyshevDensityPolynomial]
  congr 1
  funext z
  exact mvPolynomialProdEval_chebyshevPPolynomial_eq_firstCoordinatePrimitive
    (3 ^ r) (threeAdicModeSupport r)
      (threeAdicHierarchicalPairCoefficient r zeta blockCoeff) z

/-- One coefficient family simultaneously gives simple Melnikov roots for
the genuine degree-audited polynomial perturbation on every marked cell. -/
theorem threeAdicPolynomialMelnikovSimpleRootRealization {r : ℕ} (hr : 1 ≤ r) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (blockCoeff : ThreeAdicMode r → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ),
        ∀ᶠ zeta in 𝓝[>] 0,
          (∀ c, Function.Injective (fun s => root c s zeta)) ∧
          ∀ c, ∀ s : Fin (threeAdicBlockRootCount c.1),
            let h := root c s zeta
            Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
                (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
                (mvPolynomialProdEval
                  (chebyshevPPolynomial (3 ^ r)
                    (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) lambda h = 0 ∧
              0 < h ∧ h < 1 / 4 ∧
              ∃ dM : ℝ, dM ≠ 0 ∧
                HasDerivAt
                  (fun u => Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
                    (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
                    (mvPolynomialProdEval
                      (chebyshevPPolynomial (3 ^ r)
                        (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff))) lambda u)
                  dM h := by
  rcases threeAdicMelnikovSimpleRootRealization hr with
    ⟨Lambda, hLambda, hrealize⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  rcases hrealize lambda hlambda with ⟨blockCoeff, root, hevent⟩
  refine ⟨blockCoeff, root, ?_⟩
  filter_upwards [hevent] with zeta hzeta
  refine ⟨hzeta.1, ?_⟩
  intro c s
  dsimp only
  rcases hzeta.2 c s with ⟨hzero, hpos, hquarter, dM, hdM, hderiv⟩
  have heq := chebyshevFirstMelnikovDisplacement_threeAdicPolynomial_eq
    r lambda zeta blockCoeff c (root c s zeta)
  rw [heq]
  refine ⟨hzero, hpos, hquarter, dM, hdM, ?_⟩
  apply hderiv.congr_of_eventuallyEq
  exact Eventually.of_forall fun u =>
    (chebyshevFirstMelnikovDisplacement_threeAdicPolynomial_eq
      r lambda zeta blockCoeff c u)

end Hilbert16
