import Hilbert16.Counting.ThreeAdicCycles
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Hilbert16

/-!
# Passage from the three-adic subsequence to all degrees
-/

/-- The degree of the field constructed at the three-adic scale `r`. -/
def subsequenceDegree (r : ℕ) : ℕ := 4 * 3 ^ r - 5

/-- Real coercion of the division-free exact count. -/
theorem cycleLowerBound_cast (r : ℕ) :
    (cycleLowerBound r : ℝ) =
      (2 * (3 : ℝ) ^ (r - 1) * r) ^ 2 - ((3 : ℝ) ^ r - 1) ^ 2 := by
  have hpow : 1 ≤ 3 ^ r :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  rw [cycleLowerBound, Nat.cast_sub (threeAdic_count_sub_le r)]
  push_cast [Nat.cast_sub hpow]
  rfl

/-- The division-free count is exactly the displayed formula in Theorem
1.1 after substituting `n=3^r`. -/
theorem cycleLowerBound_eq_paper_formula {r : ℕ} (hr : 1 ≤ r) :
    (cycleLowerBound r : ℝ) =
      4 * ((3 : ℝ) ^ r) ^ 2 * (r : ℝ) ^ 2 / 9 -
        ((3 : ℝ) ^ r - 1) ^ 2 := by
  rcases r with _ | r
  · omega
  rw [cycleLowerBound_cast]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

/-- For `r ≥ 2`, the exact natural count dominates the simpler leading
term used in the asymptotic estimate. -/
theorem cycleLowerBound_gt_leading {r : ℕ} (hr : 2 ≤ r) :
    ((3 : ℝ) ^ r) ^ 2 * (r : ℝ) ^ 2 / 9 < cycleLowerBound r := by
  rcases r with _ | r
  · omega
  have hr' : 1 ≤ r := by omega
  have ha : (0 : ℝ) < 3 ^ r := pow_pos (by norm_num) _
  have ha1 : (1 : ℝ) ≤ 3 ^ r := one_le_pow₀ (by norm_num)
  have hR : (2 : ℝ) ≤ r + 1 := by exact_mod_cast hr
  rw [cycleLowerBound_cast]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, pow_succ]
  have hsqR : (4 : ℝ) ≤ (r + 1 : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hsmall : (3 * (3 : ℝ) ^ r - 1) ^ 2 <
      9 * ((3 : ℝ) ^ r) ^ 2 := by nlinarith [sq_nonneg ((3 : ℝ) ^ r)]
  norm_num [div_eq_mul_inv]
  nlinarith [sq_nonneg ((3 : ℝ) ^ r * (r + 1 : ℝ))]

/-- The logarithmic scale selected for an arbitrary sufficiently large
degree. -/
def allDegreeIndex (N : ℕ) : ℕ := Nat.log 3 ((N + 5) / 4)

/-- Every `N ≥ 31` lies between two consecutive construction degrees. -/
theorem allDegreeIndex_bracket {N : ℕ} (hN : 31 ≤ N) :
    subsequenceDegree (allDegreeIndex N) ≤ N ∧
      N < subsequenceDegree (allDegreeIndex N + 1) := by
  let x := (N + 5) / 4
  let r := allDegreeIndex N
  have hx : x ≠ 0 := by
    dsimp [x]
    omega
  have hlo : 3 ^ r ≤ x := by
    dsimp [r, allDegreeIndex]
    exact Nat.pow_log_le_self 3 hx
  have hhi : x < 3 ^ (r + 1) := by
    dsimp [r, allDegreeIndex]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) x
  have hdiv : (N + 5) % 4 + 4 * x = N + 5 := by
    simpa [x, mul_comm] using Nat.mod_add_div (N + 5) 4
  have hmod : (N + 5) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  constructor
  · unfold subsequenceDegree
    change 4 * 3 ^ r - 5 ≤ N
    have hmul : 4 * 3 ^ r ≤ N + 5 := by omega
    omega
  · unfold subsequenceDegree
    change N < 4 * 3 ^ (r + 1) - 5
    have hmul : N + 5 < 4 * 3 ^ (r + 1) := by omega
    omega

/-- The selected logarithmic scale is at least two in the range needed by
the paper. -/
theorem two_le_allDegreeIndex {N : ℕ} (hN : 31 ≤ N) :
    2 ≤ allDegreeIndex N := by
  let x := (N + 5) / 4
  have hx : x ≠ 0 := by
    dsimp [x]
    omega
  rw [allDegreeIndex, Nat.le_log_iff_pow_le (by norm_num : 1 < 3) hx]
  norm_num
  dsimp [x]
  omega

/-- The upper half of the degree bracket gives the paper's scale estimate
`3^r > (N+5)/12`. -/
theorem allDegreeIndex_scale_lower {N : ℕ} (hN : 31 ≤ N) :
    ((N : ℝ) + 5) / 12 < (3 : ℝ) ^ allDegreeIndex N := by
  have hupp := (allDegreeIndex_bracket hN).2
  unfold subsequenceDegree at hupp
  have hnat : N + 5 < 12 * 3 ^ allDegreeIndex N := by
    rw [pow_succ] at hupp
    have hp : 0 < 3 ^ allDegreeIndex N := pow_pos (by decide) _
    omega
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 12)).2
  have hnat' : N + 5 < 3 ^ allDegreeIndex N * 12 := by
    simpa [mul_comm] using hnat
  exact_mod_cast hnat'

/-- Taking logarithms in the scale estimate yields the second inequality
in Eq. (6.11). -/
theorem allDegreeIndex_log_lower {N : ℕ} (hN : 31 ≤ N) :
    Real.log (((N : ℝ) + 5) / 12) / Real.log 3 <
      (allDegreeIndex N : ℝ) := by
  have hscale := allDegreeIndex_scale_lower hN
  have hNreal : (31 : ℝ) ≤ N := by exact_mod_cast hN
  have harg : (0 : ℝ) < ((N : ℝ) + 5) / 12 := by positivity
  have hpow : (0 : ℝ) < (3 : ℝ) ^ allDegreeIndex N :=
    pow_pos (by norm_num) _
  have hlog := Real.strictMonoOn_log harg hpow hscale
  rw [Real.log_pow] at hlog
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).2
  simpa [mul_comm] using hlog

/-- The explicit right-hand side of Eq. (6.12). -/
noncomputable def explicitAllDegreeLowerBound (N : ℕ) : ℝ :=
  ((N : ℝ) + 5) ^ 2 / 1296 *
    (Real.log (((N : ℝ) + 5) / 12) / Real.log 3) ^ 2

/-- The two strict scale inequalities imply that the leading subsequence
term dominates the explicit all-degree expression. -/
theorem explicitAllDegreeLowerBound_lt_leading {N : ℕ} (hN : 31 ≤ N) :
    explicitAllDegreeLowerBound N <
      ((3 : ℝ) ^ allDegreeIndex N) ^ 2 *
        (allDegreeIndex N : ℝ) ^ 2 / 9 := by
  let A : ℝ := ((N : ℝ) + 5) / 12
  let B : ℝ := Real.log A / Real.log 3
  let n : ℝ := (3 : ℝ) ^ allDegreeIndex N
  let R : ℝ := allDegreeIndex N
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hAone : 1 < A := by
    have hNreal : (31 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [A]
    norm_num
    linarith
  have hB : 0 < B := by
    exact div_pos (Real.log_pos hAone) (Real.log_pos (by norm_num))
  have hn : A < n := by
    exact allDegreeIndex_scale_lower hN
  have hR : B < R := by
    exact allDegreeIndex_log_lower hN
  have hnpos : 0 < n := pow_pos (by norm_num) _
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_allDegreeIndex hN))
  have hn2 : A ^ 2 < n ^ 2 := by nlinarith [sq_nonneg (n - A)]
  have hR2 : B ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - B)]
  have hprod : A ^ 2 * B ^ 2 < n ^ 2 * R ^ 2 := by
    calc
      A ^ 2 * B ^ 2 < n ^ 2 * B ^ 2 :=
        mul_lt_mul_of_pos_right hn2 (sq_pos_of_pos hB)
      _ < n ^ 2 * R ^ 2 :=
        mul_lt_mul_of_pos_left hR2 (sq_pos_of_pos hnpos)
  have heq : explicitAllDegreeLowerBound N = A ^ 2 * B ^ 2 / 9 := by
    unfold explicitAllDegreeLowerBound
    dsimp [A, B]
    ring
  rw [heq]
  exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 9)).2 hprod

/-- **Equations (6.10)--(6.12), subsequence to all degrees.**  Any monotone
lower-bound function satisfying the exact three-adic subsequence estimate
satisfies the paper's explicit all-degree estimate for every `N ≥ 31`. -/
theorem subsequenceToAllDegrees
    (H : ℕ → ℝ) (hmono : Monotone H)
    (hsub : ∀ r, 2 ≤ r → (cycleLowerBound r : ℝ) ≤ H (subsequenceDegree r))
    {N : ℕ} (hN : 31 ≤ N) :
    explicitAllDegreeLowerBound N < H N := by
  let r := allDegreeIndex N
  have hr : 2 ≤ r := two_le_allDegreeIndex hN
  have hdegree : subsequenceDegree r ≤ N := (allDegreeIndex_bracket hN).1
  exact lt_of_lt_of_le (explicitAllDegreeLowerBound_lt_leading hN)
    (le_trans (cycleLowerBound_gt_leading hr).le
      (le_trans (hsub r hr) (hmono hdegree)))

/-- A concrete positive constant for the final `Omega` statement. -/
noncomputable def hilbertAsymptoticConstant : ℝ :=
  1 / (5184 * (Real.log 3) ^ 2)

theorem hilbertAsymptoticConstant_pos : 0 < hilbertAsymptoticConstant := by
  unfold hilbertAsymptoticConstant
  positivity

/-- For `N ≥ 144`, removing the harmless shift and scale loses at most a
factor two in the logarithm. -/
theorem half_log_le_shifted_log {N : ℕ} (hN : 144 ≤ N) :
    Real.log (N : ℝ) / 2 ≤ Real.log (((N : ℝ) + 5) / 12) := by
  have hNreal : (144 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNreal
  have hNgt : (1 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNreal
  have hlog144 : Real.log (144 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hNpos hNreal
  have h144eq : Real.log (144 : ℝ) = 2 * Real.log 12 := by
    have heq : (144 : ℝ) = 12 ^ 2 := by norm_num
    rw [heq, Real.log_pow]
    norm_num
  have hlog12 : Real.log 12 ≤ Real.log (N : ℝ) / 2 := by
    rw [h144eq] at hlog144
    linarith
  have hfracpos : (0 : ℝ) < (N : ℝ) / 12 := div_pos hNpos (by norm_num)
  have hshiftpos : (0 : ℝ) < ((N : ℝ) + 5) / 12 := by positivity
  have hfrac : (N : ℝ) / 12 ≤ ((N : ℝ) + 5) / 12 := by linarith
  have hlogfrac : Real.log ((N : ℝ) / 12) ≤
      Real.log (((N : ℝ) + 5) / 12) :=
    Real.strictMonoOn_log.monotoneOn hfracpos hshiftpos hfrac
  rw [Real.log_div (ne_of_gt hNpos) (by norm_num : (12 : ℝ) ≠ 0)] at hlogfrac
  linarith

/-- The explicit Eq. (6.12) dominates a fixed positive multiple of
`N²(log N)²`. -/
theorem asymptoticMonomial_le_explicit {N : ℕ} (hN : 144 ≤ N) :
    hilbertAsymptoticConstant * (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 ≤
      explicitAllDegreeLowerBound N := by
  let L : ℝ := Real.log (N : ℝ)
  let S : ℝ := Real.log (((N : ℝ) + 5) / 12)
  let g : ℝ := Real.log 3
  have hNreal : (0 : ℝ) ≤ N := by positivity
  have hNgt : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 144) hN)
  have hL : 0 < L := Real.log_pos hNgt
  have hhalf : L / 2 ≤ S := half_log_le_shifted_log hN
  have hS : 0 < S := lt_of_lt_of_le (half_pos hL) hhalf
  have hn2 : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 5) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) + 5)]
  have hs2 : (L / 2) ^ 2 ≤ S ^ 2 := by
    nlinarith [sq_nonneg (S - L / 2)]
  have hprod : (N : ℝ) ^ 2 * (L / 2) ^ 2 ≤
      ((N : ℝ) + 5) ^ 2 * S ^ 2 := by
    calc
      (N : ℝ) ^ 2 * (L / 2) ^ 2 ≤
          ((N : ℝ) + 5) ^ 2 * (L / 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hn2 (sq_nonneg _)
      _ ≤ ((N : ℝ) + 5) ^ 2 * S ^ 2 :=
        mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)
  have hg : 0 < g := Real.log_pos (by norm_num)
  have hden : 0 < 1296 * g ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hg)
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hprod
  unfold hilbertAsymptoticConstant explicitAllDegreeLowerBound
  dsimp [L, S, g] at hdiv ⊢
  have hleft :
      1 / (5184 * Real.log 3 ^ 2) * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2 =
        (N : ℝ) ^ 2 * (Real.log (N : ℝ) / 2) ^ 2 /
          (1296 * Real.log 3 ^ 2) := by
    field_simp [ne_of_gt hg]
    <;> ring
  have hright :
      ((N : ℝ) + 5) ^ 2 / 1296 *
          (Real.log (((N : ℝ) + 5) / 12) / Real.log 3) ^ 2 =
        ((N : ℝ) + 5) ^ 2 * Real.log (((N : ℝ) + 5) / 12) ^ 2 /
          (1296 * Real.log 3 ^ 2) := by
    field_simp [ne_of_gt hg]
    <;> ring
  rw [hleft, hright]
  exact hdiv

/-- **The all-degree `Omega(N²(log N)²)` conclusion.** -/
theorem hilbert_lower_bound_asymptotic
    (H : ℕ → ℝ) (hmono : Monotone H)
    (hsub : ∀ r, 2 ≤ r → (cycleLowerBound r : ℝ) ≤ H (subsequenceDegree r)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 ≤ H N := by
  refine ⟨hilbertAsymptoticConstant, hilbertAsymptoticConstant_pos, 144, ?_⟩
  intro N hN
  exact (asymptoticMonomial_le_explicit hN).trans
    (subsequenceToAllDegrees H hmono hsub (by omega)).le

end Hilbert16
