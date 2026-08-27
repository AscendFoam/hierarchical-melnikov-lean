import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace Hilbert16

section TensorCounting

variable {R ι : Type*} [CommRing R]

/-- Right multiplication distributes over a finite sum. -/
private lemma sum_mul_right (s : Finset ι) (f : ι → R) (a : R) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, add_mul]

/-- Left multiplication distributes over a finite sum. -/
private lemma mul_sum_left (s : Finset ι) (f : ι → R) (a : R) :
    a * (∑ i ∈ s, f i) = ∑ i ∈ s, a * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, mul_add]

/-- A product of two finite sums is the corresponding double sum. -/
private lemma sum_mul_sum (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i) * (∑ j ∈ s, g j) =
      ∑ i ∈ s, ∑ j ∈ s, f i * g j := by
  classical
  rw [sum_mul_right]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_sum_left s g (f i)

/-- Subtraction distributes over a finite sum. -/
private lemma sum_sub_sum (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, (f i - g i)) = (∑ i ∈ s, f i) - ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih]
      ring

/--
The exact finite tensor-layer identity used in the Hilbert-number count.
It is valid over every commutative ring, so no positivity or hidden
subtraction convention is involved.
-/
theorem tensorLayer_counting_identity (s : Finset ι) (y d : ι → R) :
    (∑ k ∈ s, ∑ l ∈ s, y k * y l * (d k * d l - 1)) =
      (∑ k ∈ s, y k * d k) ^ 2 - (∑ k ∈ s, y k) ^ 2 := by
  classical
  calc
    (∑ k ∈ s, ∑ l ∈ s, y k * y l * (d k * d l - 1)) =
        (∑ k ∈ s, ∑ l ∈ s, ((y k * d k) * (y l * d l) - y k * y l)) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            ring
    _ = (∑ k ∈ s, ∑ l ∈ s, (y k * d k) * (y l * d l)) -
          (∑ k ∈ s, ∑ l ∈ s, y k * y l) := by
            simp only [sum_sub_sum]
    _ = (∑ k ∈ s, y k * d k) ^ 2 - (∑ k ∈ s, y k) ^ 2 := by
          rw [pow_two, pow_two, sum_mul_sum s (fun k => y k * d k)
            (fun k => y k * d k), sum_mul_sum s y y]

end TensorCounting

section ThreeAdicLayers

/--
The paper's row multiplicity `y_(k+1)`, with zero-based layer index `k`.
It is integer-valued because `n = 3^r`.
-/
def rowMultiplicity (r k : ℕ) : ℤ := 2 * (3 : ℤ) ^ (r - (k + 1))

/-- The paper's band dimension `d_(k+1)`, with zero-based index `k`. -/
def bandDimension (k : ℕ) : ℤ := (3 : ℤ) ^ k

/-- Every one-dimensional 3-adic layer has the same row-times-band mass. -/
theorem balanced_layer {r k : ℕ} (hk : k < r) :
    rowMultiplicity r k * bandDimension k = 2 * (3 : ℤ) ^ (r - 1) := by
  have hexp : r - (k + 1) + k = r - 1 := by omega
  calc
    rowMultiplicity r k * bandDimension k =
        2 * ((3 : ℤ) ^ (r - (k + 1)) * (3 : ℤ) ^ k) := by
          simp [rowMultiplicity, bandDimension, mul_assoc]
    _ = 2 * (3 : ℤ) ^ (r - (k + 1) + k) := by rw [pow_add]
    _ = 2 * (3 : ℤ) ^ (r - 1) := by rw [hexp]

/-- The 3-adic row layers exhaust all noncentral rows: `sum y_k = 3^r - 1`. -/
theorem rowMultiplicity_sum (r : ℕ) :
    ∑ k ∈ Finset.range r, rowMultiplicity r k = (3 : ℤ) ^ r - 1 := by
  induction r with
  | zero => simp [rowMultiplicity]
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hscale :
          (∑ k ∈ Finset.range r, rowMultiplicity (r + 1) k) =
            3 * (∑ k ∈ Finset.range r, rowMultiplicity r k) := by
        rw [mul_sum_left]
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < r := Finset.mem_range.mp hk
        have hexp : r + 1 - (k + 1) = (r - (k + 1)) + 1 := by omega
        simp only [rowMultiplicity, hexp, pow_succ]
        ring
      rw [hscale, ih]
      simp [rowMultiplicity, pow_succ]
      ring

/-- Summing the balanced mass over all `r` layers gives `2*3^(r-1)*r`. -/
theorem balancedWeighted_sum (r : ℕ) :
    ∑ k ∈ Finset.range r, rowMultiplicity r k * bandDimension k =
      2 * (3 : ℤ) ^ (r - 1) * r := by
  calc
    (∑ k ∈ Finset.range r, rowMultiplicity r k * bandDimension k) =
        ∑ _k ∈ Finset.range r, 2 * (3 : ℤ) ^ (r - 1) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact balanced_layer (Finset.mem_range.mp hk)
    _ = 2 * (3 : ℤ) ^ (r - 1) * r := by simp; ring

/--
The exact 3-adic double count, in the division-free form
`(2*3^(r-1)*r)^2 - (3^r-1)^2`.
-/
theorem threeAdic_exact_count (r : ℕ) :
    (∑ k ∈ Finset.range r, ∑ l ∈ Finset.range r,
      rowMultiplicity r k * rowMultiplicity r l *
        (bandDimension k * bandDimension l - 1)) =
      (2 * (3 : ℤ) ^ (r - 1) * r) ^ 2 - ((3 : ℤ) ^ r - 1) ^ 2 := by
  rw [tensorLayer_counting_identity]
  rw [balancedWeighted_sum r, rowMultiplicity_sum r]

/-- The same count with the paper's denominator `9` cleared. -/
theorem threeAdic_exact_count_scaled (r : ℕ) :
    9 * (∑ k ∈ Finset.range r, ∑ l ∈ Finset.range r,
      rowMultiplicity r k * rowMultiplicity r l *
        (bandDimension k * bandDimension l - 1)) =
      4 * ((3 : ℤ) ^ r) ^ 2 * (r : ℤ) ^ 2 -
        9 * ((3 : ℤ) ^ r - 1) ^ 2 := by
  rw [threeAdic_exact_count]
  cases r with
  | zero => norm_num
  | succ r =>
      simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
      ring

end ThreeAdicLayers

end Hilbert16
