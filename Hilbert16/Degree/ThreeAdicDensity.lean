import Hilbert16.Degree
import Hilbert16.Chebyshev.ThreeAdicVisibility

set_option autoImplicit false

namespace Hilbert16

open scoped BigOperators

/-!
# The actual three-adic global density and its degree
-/

/-- Every actual frequency in a three-adic band is odd. -/
theorem threeAdicFrequencyValue_odd {r k : ℕ} (a : ThreeAdicFrequency k) :
    Odd (threeAdicFrequencyValue (r := r) a) := by
  exact (threeAdicFrequencyNumerator_odd a).mul
    ((show Odd (3 : ℕ) by decide).pow)

/-- Since both the degree `3^r` and every band frequency are odd, the
strict upper bound improves to the paper's `a ≤ 3^r-2`. -/
theorem threeAdicFrequencyValue_le_pow_sub_two {r k : ℕ} (hk : k < r)
    (a : ThreeAdicFrequency k) :
    threeAdicFrequencyValue (r := r) a ≤ 3 ^ r - 2 := by
  have hlt := threeAdicFrequencyValue_lt_pow hk a
  rcases threeAdicFrequencyValue_odd a with ⟨u, hu⟩
  rcases (show Odd (3 ^ r) from (show Odd (3 : ℕ) by decide).pow) with ⟨v, hv⟩
  omega

/-- A dependent mode index records its two genuine three-adic bands and
one actual frequency parameter in each band. -/
def ThreeAdicMode (r : ℕ) :=
  Σ k : Fin r, Σ l : Fin r, ThreeAdicFrequency k × ThreeAdicFrequency l

instance (r : ℕ) : Fintype (ThreeAdicMode r) := by
  unfold ThreeAdicMode
  infer_instance

/-- The actual pair `(a,b)` carried by a dependent three-adic mode. -/
def threeAdicModeFrequencyPair {r : ℕ} (m : ThreeAdicMode r) : ℕ × ℕ :=
  (threeAdicFrequencyValue (r := r) m.2.2.1,
    threeAdicFrequencyValue (r := r) m.2.2.2)

theorem threeAdicModeFrequencyPair_sum_le {r : ℕ} (m : ThreeAdicMode r) :
    (threeAdicModeFrequencyPair m).1 + (threeAdicModeFrequencyPair m).2 ≤
      2 * 3 ^ r - 4 := by
  have ha := threeAdicFrequencyValue_le_pow_sub_two m.1.2 m.2.2.1
  have hb := threeAdicFrequencyValue_le_pow_sub_two m.2.1.2 m.2.2.2
  simp only [threeAdicModeFrequencyPair]
  have hn : 2 ≤ 3 ^ r := by
    cases r with
    | zero => exact Fin.elim0 m.1
    | succ q =>
        have hq : 1 ≤ 3 ^ q :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
        rw [pow_succ]
        omega
  omega

/-- Paper Eq. (6.6)'s single finite global polynomial density, with an
arbitrary coefficient on every actual three-adic tensor mode. -/
noncomputable def threeAdicGlobalDensityPolynomial (r : ℕ)
    (coeff : ThreeAdicMode r → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ m, MvPolynomial.C (coeff m) *
    chebyshevModePolynomial (threeAdicModeFrequencyPair m).1
      (threeAdicModeFrequencyPair m).2

/-- Paper Eq. (6.6)'s one-parameter hierarchy, using the paper's one-based
weight `(k+1)+(l+1)`. -/
noncomputable def threeAdicHierarchicalDensityPolynomial (r : ℕ) (zeta : ℝ)
    (blockCoeff : ThreeAdicMode r → ℝ) : MvPolynomial (Fin 2) ℝ :=
  threeAdicGlobalDensityPolynomial r fun m =>
    zeta ^ (m.1.1 + 1 + (m.2.1.1 + 1)) * blockCoeff m

/-- Paper Lemma 6.2 for the actual global density: all modes have
`a+b ≤ 2*3^r-4`. -/
theorem threeAdicGlobalDensityPolynomial_totalDegree_le (r : ℕ)
    (coeff : ThreeAdicMode r → ℝ) :
    MvPolynomial.totalDegree (threeAdicGlobalDensityPolynomial r coeff) ≤
      2 * 3 ^ r - 4 := by
  unfold threeAdicGlobalDensityPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa using
      (chebyshevModePolynomial_totalDegree_le
        (threeAdicModeFrequencyPair m).1 (threeAdicModeFrequencyPair m).2).trans
          (threeAdicModeFrequencyPair_sum_le m))

theorem threeAdicHierarchicalDensityPolynomial_totalDegree_le (r : ℕ) (zeta : ℝ)
    (blockCoeff : ThreeAdicMode r → ℝ) :
    MvPolynomial.totalDegree
        (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff) ≤
      2 * 3 ^ r - 4 := by
  exact threeAdicGlobalDensityPolynomial_totalDegree_le r _

/-- The final polynomial field built from any actual global three-adic
density satisfies the paper's exact degree ceiling. -/
theorem threeAdicFinalVectorField_degree_le {r : ℕ} (hr : 1 ≤ r)
    (lambda mu : ℝ) (coeff : ThreeAdicMode r → ℝ) :
    (finalPolyVectorField (3 ^ r) lambda mu
      (threeAdicGlobalDensityPolynomial r coeff)).degree ≤
        ((4 * 3 ^ r - 5 : ℕ) : WithBot ℕ) := by
  have hn : 2 ≤ 3 ^ r := by
    cases r with
    | zero => simp at hr
    | succ q =>
        have hq : 1 ≤ 3 ^ q :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
        rw [pow_succ]
        omega
  exact finalVectorField_degree_le hn lambda mu
    (threeAdicGlobalDensityPolynomial_totalDegree_le r coeff)

theorem threeAdicHierarchicalFinalVectorField_degree_le {r : ℕ} (hr : 1 ≤ r)
    (lambda mu zeta : ℝ) (blockCoeff : ThreeAdicMode r → ℝ) :
    (finalPolyVectorField (3 ^ r) lambda mu
      (threeAdicHierarchicalDensityPolynomial r zeta blockCoeff)).degree ≤
        ((4 * 3 ^ r - 5 : ℕ) : WithBot ℕ) := by
  exact threeAdicFinalVectorField_degree_le hr lambda mu _

end Hilbert16
