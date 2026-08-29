import Hilbert16.Chebyshev.ThreeAdicVisibility
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators

namespace Hilbert16

/-!
# The actual finite index set counted in Eq. (6.7)

An index records its two layers, its two rows, and one of the
`d_k d_l - 1` simple roots supplied by the corresponding analytic block.
-/

/-- The exact lower-bound count in the division-free natural-number form
used by the main theorem. -/
def cycleLowerBound (r : ℕ) : ℕ :=
  (2 * 3 ^ (r - 1) * r) ^ 2 - (3 ^ r - 1) ^ 2

/-- The finite set of all marked roots before Poincare--Pontryagin
persistence, indexed by their actual three-adic row parameters. -/
def ThreeAdicCycleIndex (r : ℕ) :=
  Σ k : Fin r, Σ l : Fin r,
    ThreeAdicRow r k × ThreeAdicRow r l ×
      Fin (Fintype.card (ThreeAdicFrequency k) *
        Fintype.card (ThreeAdicFrequency l) - 1)

instance (r : ℕ) : Fintype (ThreeAdicCycleIndex r) := by
  unfold ThreeAdicCycleIndex
  infer_instance

/-- Cardinality of the dependent index type as the paper's finite double
sum, still expressed through the genuine row and frequency types. -/
theorem card_threeAdicCycleIndex_sum (r : ℕ) :
    Fintype.card (ThreeAdicCycleIndex r) =
      ∑ k : Fin r, ∑ l : Fin r,
        Fintype.card (ThreeAdicRow r k) *
          Fintype.card (ThreeAdicRow r l) *
          (Fintype.card (ThreeAdicFrequency k) *
            Fintype.card (ThreeAdicFrequency l) - 1) := by
  simp [ThreeAdicCycleIndex, mul_assoc]

/-- The two square terms in Eq. (6.7) are ordered, so the natural-number
subtraction in the exact count is not truncated. -/
theorem threeAdic_count_sub_le (r : ℕ) :
    (3 ^ r - 1) ^ 2 ≤ (2 * 3 ^ (r - 1) * r) ^ 2 := by
  apply Nat.pow_le_pow_left
  cases r with
  | zero => simp
  | succ r =>
      cases r with
      | zero => norm_num
      | succ q =>
          have hcoef : 3 ≤ 2 * (q + 2) := by omega
          calc
            3 ^ (q + 2) - 1 ≤ 3 ^ (q + 2) := Nat.sub_le _ _
            _ = 3 * 3 ^ (q + 1) := by rw [pow_succ]; ring
            _ ≤ 2 * (q + 2) * 3 ^ (q + 1) :=
              Nat.mul_le_mul_right (3 ^ (q + 1)) hcoef
            _ = 2 * 3 ^ (q + 1) * (q + 2) := by ring

/-- **Equation (6.7), exact natural-number count.**  The cardinality of the
actual finite marked-root index is the paper's closed formula. -/
theorem card_threeAdicCycleIndex (r : ℕ) :
    Fintype.card (ThreeAdicCycleIndex r) =
      (2 * 3 ^ (r - 1) * r) ^ 2 - (3 ^ r - 1) ^ 2 := by
  rw [card_threeAdicCycleIndex_sum]
  have hfreq (k l : Fin r) :
      1 ≤ Fintype.card (ThreeAdicFrequency k) *
        Fintype.card (ThreeAdicFrequency l) := by
    rw [card_threeAdicFrequency, card_threeAdicFrequency]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))
  have hrpow : 1 ≤ 3 ^ r :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub (threeAdic_count_sub_le r)]
  push_cast
  rw [Nat.cast_sub hrpow]
  simp_rw [Nat.cast_sub (hfreq _ _)]
  simp only [card_threeAdicRow, card_threeAdicFrequency, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  let E : ℕ → ℕ → ℤ := fun k l =>
    2 * 3 ^ (r - (k + 1)) * (2 * 3 ^ (r - (l + 1))) *
      (3 ^ k * 3 ^ l - 1)
  change (∑ k : Fin r, ∑ l : Fin r, E k l) =
    (2 * 3 ^ (r - 1) * (r : ℤ)) ^ 2 - (3 ^ r - 1) ^ 2
  calc
    (∑ k : Fin r, ∑ l : Fin r, E k l) =
        ∑ k : Fin r, ∑ l ∈ Finset.range r, E k l := by
          apply Finset.sum_congr rfl
          intro k _
          exact Fin.sum_univ_eq_sum_range (fun l => E k l) r
    _ = ∑ k ∈ Finset.range r, ∑ l ∈ Finset.range r, E k l :=
      Fin.sum_univ_eq_sum_range
        (fun k => ∑ l ∈ Finset.range r, E k l) r
    _ = (2 * 3 ^ (r - 1) * (r : ℤ)) ^ 2 - (3 ^ r - 1) ^ 2 := by
      simpa only [E, rowMultiplicity, bandDimension] using threeAdic_exact_count r

theorem card_threeAdicCycleIndex_eq_cycleLowerBound (r : ℕ) :
    Fintype.card (ThreeAdicCycleIndex r) = cycleLowerBound r := by
  exact card_threeAdicCycleIndex r

end Hilbert16
