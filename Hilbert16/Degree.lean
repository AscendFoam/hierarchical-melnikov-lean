import Hilbert16.Foundations.PolynomialVectorField
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Chebyshev

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Hilbert16

open scoped BigOperators

/-- Embed a univariate real polynomial in one selected multivariate coordinate. -/
noncomputable def univariateAt {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : Polynomial ℝ) : MvPolynomial sigma ℝ :=
  p.support.sum fun k =>
    MvPolynomial.monomial (Finsupp.single i k) (p.coeff k)

theorem univariateAt_totalDegree_le {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : Polynomial ℝ) :
    MvPolynomial.totalDegree (univariateAt i p) ≤ p.natDegree := by
  unfold univariateAt
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    MvPolynomial.totalDegree
        (MvPolynomial.monomial (Finsupp.single i k) (p.coeff k)) ≤ k := by
      simpa using MvPolynomial.totalDegree_monomial_le
        (Finsupp.single i k) (p.coeff k)
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk

theorem eval_univariateAt {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : Polynomial ℝ) (z : sigma → ℝ) :
    MvPolynomial.eval z (univariateAt i p) = p.eval (z i) := by
  unfold univariateAt
  rw [map_sum, Polynomial.eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [MvPolynomial.eval_monomial]

/-- Algebraic antiderivative in one selected variable, normalized to have no terms independent of
that variable. -/
noncomputable def MvPolynomial.integrateAt {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : MvPolynomial sigma ℝ) : MvPolynomial sigma ℝ :=
  p.support.sum fun m =>
    MvPolynomial.monomial (m + Finsupp.single i 1)
      (p.coeff m / ((m i + 1 : ℕ) : ℝ))

theorem MvPolynomial.pderiv_integrateAt {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : MvPolynomial sigma ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.integrateAt i p) = p := by
  unfold MvPolynomial.integrateAt
  rw [map_sum]
  calc
    (∑ m ∈ p.support,
        MvPolynomial.pderiv i
          (MvPolynomial.monomial (m + Finsupp.single i 1)
            (p.coeff m / ((m i + 1 : ℕ) : ℝ)))) =
        ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [MvPolynomial.pderiv_monomial]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
      congr 1
      field_simp
    _ = p := p.support_sum_monomial_coeff

theorem MvPolynomial.totalDegree_integrateAt_le {sigma : Type*} [DecidableEq sigma]
    (i : sigma) (p : MvPolynomial sigma ℝ) :
    MvPolynomial.totalDegree (MvPolynomial.integrateAt i p) ≤
      MvPolynomial.totalDegree p + 1 := by
  unfold MvPolynomial.integrateAt
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro m hm
  calc
    MvPolynomial.totalDegree
        (MvPolynomial.monomial (m + Finsupp.single i 1)
          (p.coeff m / ((m i + 1 : ℕ) : ℝ))) ≤
        (m + Finsupp.single i 1).sum fun _ e => e :=
      MvPolynomial.totalDegree_monomial_le _ _
    _ = (m.sum fun _ e => e : ℕ) + 1 := by
      change (m + Finsupp.single i 1).degree = m.degree + 1
      simp
    _ ≤ MvPolynomial.totalDegree p + 1 := by
      simpa [add_comm] using add_le_add_right (MvPolynomial.le_totalDegree hm) 1

/-- The univariate Chebyshev polynomial placed in one planar coordinate. -/
noncomputable def chebyshevAt (i : Fin 2) (n : ℕ) : MvPolynomial (Fin 2) ℝ :=
  univariateAt i (Polynomial.Chebyshev.T ℝ (n : ℤ))

/-- The derivative of `T_n` placed in one planar coordinate. -/
noncomputable def chebyshevDerivativeAt (i : Fin 2) (n : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  univariateAt i (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative

theorem chebyshev_natDegree (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree = n := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  simpa only [Int.natAbs_natCast] using
    (Polynomial.Chebyshev.degree_T ℝ (n : ℤ))

theorem chebyshevAt_totalDegree_le (i : Fin 2) (n : ℕ) :
    MvPolynomial.totalDegree (chebyshevAt i n) ≤ n := by
  simpa [chebyshevAt, chebyshev_natDegree] using
    univariateAt_totalDegree_le i (Polynomial.Chebyshev.T ℝ (n : ℤ))

theorem chebyshevDerivativeAt_totalDegree_le (i : Fin 2) (n : ℕ) :
    MvPolynomial.totalDegree (chebyshevDerivativeAt i n) ≤ n - 1 := by
  refine (univariateAt_totalDegree_le i
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative).trans ?_
  simpa [chebyshev_natDegree] using
    Polynomial.natDegree_derivative_le (Polynomial.Chebyshev.T ℝ (n : ℤ))

/-- One tensor Chebyshev mode `T_a(x)T_b(y)` as an actual bivariate polynomial. -/
noncomputable def chebyshevModePolynomial (a b : ℕ) : MvPolynomial (Fin 2) ℝ :=
  chebyshevAt 0 a * chebyshevAt 1 b

theorem chebyshevModePolynomial_totalDegree_le (a b : ℕ) :
    MvPolynomial.totalDegree (chebyshevModePolynomial a b) ≤ a + b := by
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (add_le_add (chebyshevAt_totalDegree_le 0 a) (chebyshevAt_totalDegree_le 1 b))

/-- Paper Eq. (6.9)'s finite global density before the two Jacobian-cancelling derivatives. -/
noncomputable def chebyshevDensityPolynomial
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  support.sum fun k => MvPolynomial.C (coeff k) * chebyshevModePolynomial k.1 k.2

theorem chebyshevDensityPolynomial_totalDegree_le
    {support : Finset (ℕ × ℕ)} {coeff : ℕ × ℕ → ℝ} {d : ℕ}
    (hfreq : ∀ k ∈ support, k.1 + k.2 ≤ d) :
    MvPolynomial.totalDegree (chebyshevDensityPolynomial support coeff) ≤ d := by
  unfold chebyshevDensityPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa using chebyshevModePolynomial_totalDegree_le k.1 k.2 |>.trans (hfreq k hk))

/-- Paper Eq. (3.4): `q=T_n'(x)T_n'(y)S`. -/
noncomputable def chebyshevQPolynomial (n : ℕ) (S : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  chebyshevDerivativeAt 0 n * chebyshevDerivativeAt 1 n * S

theorem chebyshevQPolynomial_totalDegree_le
    {n : ℕ} (hn : 2 ≤ n) {S : MvPolynomial (Fin 2) ℝ}
    (hS : MvPolynomial.totalDegree S ≤ 2 * n - 4) :
    MvPolynomial.totalDegree (chebyshevQPolynomial n S) ≤ 4 * n - 6 := by
  unfold chebyshevQPolynomial
  calc
    MvPolynomial.totalDegree
        (chebyshevDerivativeAt 0 n * chebyshevDerivativeAt 1 n * S) ≤
        MvPolynomial.totalDegree (chebyshevDerivativeAt 0 n * chebyshevDerivativeAt 1 n) +
          MvPolynomial.totalDegree S :=
      MvPolynomial.totalDegree_mul
        (chebyshevDerivativeAt 0 n * chebyshevDerivativeAt 1 n) S
    _ ≤ (MvPolynomial.totalDegree (chebyshevDerivativeAt 0 n) +
          MvPolynomial.totalDegree (chebyshevDerivativeAt 1 n)) +
          MvPolynomial.totalDegree S :=
      by simpa [add_comm] using add_le_add_right (MvPolynomial.totalDegree_mul
        (chebyshevDerivativeAt 0 n) (chebyshevDerivativeAt 1 n))
          (MvPolynomial.totalDegree S)
    _ ≤ (n - 1) + (n - 1) + (2 * n - 4) :=
      add_le_add (add_le_add
        (chebyshevDerivativeAt_totalDegree_le 0 n)
        (chebyshevDerivativeAt_totalDegree_le 1 n)) hS
    _ = 4 * n - 6 := by omega

/-- Paper Eq. (3.4)'s normalized polynomial primitive in the `x` variable. -/
noncomputable def chebyshevPPolynomial (n : ℕ) (S : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.integrateAt 0 (chebyshevQPolynomial n S)

theorem chebyshevPPolynomial_pderiv (n : ℕ) (S : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial.pderiv 0 (chebyshevPPolynomial n S) = chebyshevQPolynomial n S :=
  MvPolynomial.pderiv_integrateAt _ _

theorem chebyshevPPolynomial_totalDegree_le
    {n : ℕ} (hn : 2 ≤ n) {S : MvPolynomial (Fin 2) ℝ}
    (hS : MvPolynomial.totalDegree S ≤ 2 * n - 4) :
    MvPolynomial.totalDegree (chebyshevPPolynomial n S) ≤ 4 * n - 5 := by
  unfold chebyshevPPolynomial
  refine (MvPolynomial.totalDegree_integrateAt_le 0 (chebyshevQPolynomial n S)).trans ?_
  calc
    MvPolynomial.totalDegree (chebyshevQPolynomial n S) + 1 ≤
        (4 * n - 6) + 1 :=
      by simpa [add_comm] using
        add_le_add_right (chebyshevQPolynomial_totalDegree_le hn hS) 1
    _ = 4 * n - 5 := by omega

/-- The polynomial Hamiltonian vector field `(H_y,-H_x)`. -/
noncomputable def chebyshevHamiltonianPolyVectorField (n : ℕ) (lambda : ℝ) :
    PolyVectorField
  | 0 => MvPolynomial.C lambda * chebyshevAt 1 n * chebyshevDerivativeAt 1 n
  | 1 => -(chebyshevAt 0 n * chebyshevDerivativeAt 0 n)

theorem chebyshevHamiltonianPolyVectorField_coordinate_totalDegree_le
    {n : ℕ} (hn : 1 ≤ n) (lambda : ℝ) (k : Fin 2) :
    MvPolynomial.totalDegree (chebyshevHamiltonianPolyVectorField n lambda k) ≤
      2 * n - 1 := by
  fin_cases k
  · simp only [chebyshevHamiltonianPolyVectorField, Fin.isValue]
    calc
      _ ≤ MvPolynomial.totalDegree (MvPolynomial.C lambda * chebyshevAt 1 n) +
          MvPolynomial.totalDegree (chebyshevDerivativeAt 1 n) :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (MvPolynomial.totalDegree
              (MvPolynomial.C lambda : MvPolynomial (Fin 2) ℝ) +
            MvPolynomial.totalDegree (chebyshevAt 1 n)) +
          MvPolynomial.totalDegree (chebyshevDerivativeAt 1 n) :=
        by simpa [add_comm] using (add_le_add_right
          (MvPolynomial.totalDegree_mul
            (MvPolynomial.C lambda : MvPolynomial (Fin 2) ℝ) (chebyshevAt 1 n))
          (MvPolynomial.totalDegree (chebyshevDerivativeAt 1 n)))
      _ ≤ 0 + n + (n - 1) := by
        exact add_le_add (add_le_add (by simp) (chebyshevAt_totalDegree_le 1 n))
          (chebyshevDerivativeAt_totalDegree_le 1 n)
      _ = 2 * n - 1 := by omega
  · simp only [chebyshevHamiltonianPolyVectorField, Fin.isValue,
      MvPolynomial.totalDegree_neg]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((add_le_add (chebyshevAt_totalDegree_le 0 n)
        (chebyshevDerivativeAt_totalDegree_le 0 n)).trans (by
          omega))

theorem chebyshevHamiltonianPolyVectorField_degree_le
    {n : ℕ} (hn : 1 ≤ n) (lambda : ℝ) :
    (chebyshevHamiltonianPolyVectorField n lambda).degree ≤
      ((2 * n - 1 : ℕ) : WithBot ℕ) := by
  unfold PolyVectorField.degree
  apply max_le
  · exact_mod_cast chebyshevHamiltonianPolyVectorField_coordinate_totalDegree_le hn lambda 0
  · exact_mod_cast chebyshevHamiltonianPolyVectorField_coordinate_totalDegree_le hn lambda 1

/-- Paper Eq. (3.5), represented in the public polynomial-vector-field type. -/
noncomputable def finalPolyVectorField
    (n : ℕ) (lambda mu : ℝ) (S : MvPolynomial (Fin 2) ℝ) : PolyVectorField
  | 0 => chebyshevHamiltonianPolyVectorField n lambda 0 +
      MvPolynomial.C mu * chebyshevPPolynomial n S
  | 1 => chebyshevHamiltonianPolyVectorField n lambda 1

theorem finalPolyVectorField_coordinate_totalDegree_le
    {n : ℕ} (hn : 2 ≤ n) (lambda mu : ℝ) {S : MvPolynomial (Fin 2) ℝ}
    (hS : MvPolynomial.totalDegree S ≤ 2 * n - 4) (k : Fin 2) :
    MvPolynomial.totalDegree (finalPolyVectorField n lambda mu S k) ≤
      4 * n - 5 := by
  have hn1 : 1 ≤ n := by omega
  fin_cases k
  · simp only [finalPolyVectorField, Fin.isValue]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (chebyshevHamiltonianPolyVectorField_coordinate_totalDegree_le hn1 lambda 0).trans
        (by omega)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simpa using add_le_add
        (show MvPolynomial.totalDegree
          (MvPolynomial.C mu : MvPolynomial (Fin 2) ℝ) ≤ 0 by simp)
        (chebyshevPPolynomial_totalDegree_le hn hS)
  · simp only [finalPolyVectorField, Fin.isValue]
    exact (chebyshevHamiltonianPolyVectorField_coordinate_totalDegree_le hn1 lambda 1).trans
      (by omega)

/-- Paper Eq. (6.10)'s final degree audit. -/
theorem finalVectorField_degree_le
    {n : ℕ} (hn : 2 ≤ n) (lambda mu : ℝ) {S : MvPolynomial (Fin 2) ℝ}
    (hS : MvPolynomial.totalDegree S ≤ 2 * n - 4) :
    (finalPolyVectorField n lambda mu S).degree ≤
      ((4 * n - 5 : ℕ) : WithBot ℕ) := by
  unfold PolyVectorField.degree
  apply max_le
  · exact_mod_cast finalPolyVectorField_coordinate_totalDegree_le hn lambda mu hS 0
  · exact_mod_cast finalPolyVectorField_coordinate_totalDegree_le hn lambda mu hS 1

end Hilbert16
