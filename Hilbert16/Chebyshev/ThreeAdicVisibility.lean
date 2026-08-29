import Hilbert16.Counting
import Hilbert16.Spikes.ChebyshevCell
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

namespace Hilbert16

/-!
# The exact three-adic row and frequency layers

The paper numbers its layers from `1` to `r`.  This file uses a zero-based
index `k < r`; it therefore represents the paper's `Y_(k+1)` and `W_(k+1)`.
Both finite sets are given by injective arithmetic parametrizations.  This
makes their cardinalities definitional while retaining the exact row and
frequency integers used in the cosine visibility calculation.
-/

/-- Parameters for the rows in the paper's layer `Y_(k+1)`. -/
def ThreeAdicRow (r k : ℕ) := Fin 2 × Fin (3 ^ (r - (k + 1)))

/-- Parameters for the frequencies in the paper's band `W_(k+1)`. -/
def ThreeAdicFrequency (k : ℕ) := Fin (3 ^ k)

instance (r k : ℕ) : Fintype (ThreeAdicRow r k) := by
  unfold ThreeAdicRow
  infer_instance

instance (k : ℕ) : Fintype (ThreeAdicFrequency k) := by
  unfold ThreeAdicFrequency
  infer_instance

theorem card_threeAdicRow (r k : ℕ) :
    Fintype.card (ThreeAdicRow r k) = 2 * 3 ^ (r - (k + 1)) := by
  simp [ThreeAdicRow]

theorem card_threeAdicFrequency (k : ℕ) :
    Fintype.card (ThreeAdicFrequency k) = 3 ^ k := by
  simp [ThreeAdicFrequency]

/-- The odd unit `u ≡1,5 (mod 6)` carried by a row parameter. -/
def threeAdicRowUnit {r k : ℕ} (i : ThreeAdicRow r k) : ℕ :=
  6 * i.2.1 + 4 * i.1.1 + 1

/-- The actual zero-based Chebyshev cell index represented by a row parameter. -/
def threeAdicRowIndex {r k : ℕ} (i : ThreeAdicRow r k) : ℕ :=
  (3 ^ k * threeAdicRowUnit i) / 2

/-- The primitive odd numerator in a frequency parameter. -/
def threeAdicFrequencyNumerator {k : ℕ} (a : ThreeAdicFrequency k) : ℕ :=
  3 * a.1 + 1 + a.1 % 2

/-- The actual Chebyshev frequency in degree `n = 3^r`. -/
def threeAdicFrequencyValue {r k : ℕ} (a : ThreeAdicFrequency k) : ℕ :=
  threeAdicFrequencyNumerator a * 3 ^ (r - (k + 1))

theorem threeAdicRowUnit_odd {r k : ℕ} (i : ThreeAdicRow r k) :
    Odd (threeAdicRowUnit i) := by
  refine ⟨3 * i.2.1 + 2 * i.1.1, ?_⟩
  simp [threeAdicRowUnit]
  ring

theorem threeAdicRowUnit_not_three_dvd {r k : ℕ} (i : ThreeAdicRow r k) :
    ¬3 ∣ threeAdicRowUnit i := by
  rintro ⟨q, hq⟩
  have hi : i.1.1 < 2 := i.1.2
  simp only [threeAdicRowUnit] at hq
  omega

theorem threeAdicRow_numerator {r k : ℕ} (i : ThreeAdicRow r k) :
    2 * threeAdicRowIndex i + 1 = 3 ^ k * threeAdicRowUnit i := by
  have hodd : Odd (3 ^ k * threeAdicRowUnit i) :=
    (show Odd (3 ^ k) from (by exact (show Odd 3 by decide).pow)).mul
      (threeAdicRowUnit_odd i)
  have hdiv := Nat.two_mul_odd_div_two (Nat.odd_iff.mp hodd)
  have hpos : 0 < 3 ^ k * threeAdicRowUnit i := by
    apply Nat.mul_pos (pow_pos (by decide) _)
    simp [threeAdicRowUnit]
  simp only [threeAdicRowIndex]
  calc
    2 * ((3 ^ k * threeAdicRowUnit i) / 2) + 1 =
        (3 ^ k * threeAdicRowUnit i - 1) + 1 := by rw [hdiv]
    _ = 3 ^ k * threeAdicRowUnit i := Nat.sub_add_cancel hpos

theorem threeAdicFrequencyNumerator_odd {k : ℕ} (a : ThreeAdicFrequency k) :
    Odd (threeAdicFrequencyNumerator a) := by
  rcases Nat.mod_two_eq_zero_or_one a.1 with h | h
  · have hdecomp := Nat.mod_add_div a.1 2
    refine ⟨3 * (a.1 / 2), ?_⟩
    simp only [threeAdicFrequencyNumerator, h]
    omega
  · have hdecomp := Nat.mod_add_div a.1 2
    refine ⟨3 * (a.1 / 2) + 2, ?_⟩
    simp only [threeAdicFrequencyNumerator, h]
    omega

theorem threeAdicFrequencyNumerator_not_three_dvd
    {k : ℕ} (a : ThreeAdicFrequency k) :
    ¬3 ∣ threeAdicFrequencyNumerator a := by
  rintro ⟨q, hq⟩
  have hmod : a.1 % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [threeAdicFrequencyNumerator] at hq
  omega

theorem threeAdicFrequencyNumerator_pos {k : ℕ} (a : ThreeAdicFrequency k) :
    0 < threeAdicFrequencyNumerator a := by
  simp [threeAdicFrequencyNumerator]

theorem threeAdicFrequencyNumerator_lt {k : ℕ} (a : ThreeAdicFrequency k) :
    threeAdicFrequencyNumerator a < 3 ^ (k + 1) := by
  have ha : a.1 < 3 ^ k := a.2
  have hmod : a.1 % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [threeAdicFrequencyNumerator, pow_succ]
  omega

theorem threeAdicFrequencyValue_lt_pow {r k : ℕ} (hk : k < r)
    (a : ThreeAdicFrequency k) :
    threeAdicFrequencyValue (r := r) a < 3 ^ r := by
  have hpos : 0 < 3 ^ (r - (k + 1)) := pow_pos (by decide) _
  calc
    threeAdicFrequencyValue (r := r) a <
        3 ^ (k + 1) * 3 ^ (r - (k + 1)) := by
      exact (Nat.mul_lt_mul_right hpos).2 (threeAdicFrequencyNumerator_lt a)
    _ = 3 ^ r := by
      rw [← pow_add]
      congr 1
      omega

theorem threeAdicRowUnit_lt {r k : ℕ} (hk : k < r) (i : ThreeAdicRow r k) :
    threeAdicRowUnit i < 2 * 3 ^ (r - k) := by
  have hq : i.2.1 < 3 ^ (r - (k + 1)) := i.2.2
  have hb : i.1.1 < 2 := i.1.2
  have hexp : r - k = (r - (k + 1)) + 1 := by omega
  simp only [threeAdicRowUnit, hexp, pow_succ]
  omega

theorem threeAdicRowIndex_lt_pow {r k : ℕ} (hk : k < r)
    (i : ThreeAdicRow r k) :
    threeAdicRowIndex i < 3 ^ r := by
  have hexp : r = k + (r - k) := by omega
  have hu := threeAdicRowUnit_lt hk i
  have hpow : 3 ^ r = 3 ^ k * 3 ^ (r - k) := by
    calc
      3 ^ r = 3 ^ (k + (r - k)) := congrArg (fun e : ℕ => 3 ^ e) hexp
      _ = 3 ^ k * 3 ^ (r - k) := pow_add 3 k (r - k)
  rw [threeAdicRowIndex, Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
  calc
    3 ^ k * threeAdicRowUnit i < 3 ^ k * (2 * 3 ^ (r - k)) :=
      (Nat.mul_lt_mul_left (pow_pos (by decide) _)).2 hu
    _ = 3 ^ r * 2 := by rw [hpow]; ring

theorem threeAdicRowUnit_injective {r k : ℕ} :
    Function.Injective (@threeAdicRowUnit r k) := by
  intro i j hij
  apply Prod.ext
  · apply Fin.ext
    have hi : i.1.1 < 2 := i.1.2
    have hj : j.1.1 < 2 := j.1.2
    simp only [threeAdicRowUnit] at hij
    omega
  · apply Fin.ext
    have hi : i.1.1 < 2 := i.1.2
    have hj : j.1.1 < 2 := j.1.2
    simp only [threeAdicRowUnit] at hij
    omega

theorem threeAdicRowIndex_injective {r k : ℕ} :
    Function.Injective (@threeAdicRowIndex r k) := by
  intro i j hij
  apply threeAdicRowUnit_injective
  have hnum : 3 ^ k * threeAdicRowUnit i = 3 ^ k * threeAdicRowUnit j := by
    rw [← threeAdicRow_numerator i, ← threeAdicRow_numerator j, hij]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) _) hnum

theorem threeAdicFrequencyNumerator_injective {k : ℕ} :
    Function.Injective (@threeAdicFrequencyNumerator k) := by
  intro a b hab
  apply Fin.ext
  have ha : a.1 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hb : b.1 % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [threeAdicFrequencyNumerator] at hab
  omega

theorem threeAdicFrequencyValue_injective {r k : ℕ} :
    Function.Injective (@threeAdicFrequencyValue r k) := by
  intro a b hab
  apply threeAdicFrequencyNumerator_injective
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by decide) _) hab

/-- The actual finite set of row indices in `Y_(k+1)`. -/
def threeAdicRowSet (r k : ℕ) : Finset ℕ :=
  Finset.univ.image (@threeAdicRowIndex r k)

/-- The actual finite set of frequencies in `W_(k+1)`. -/
def threeAdicFrequencySet (r k : ℕ) : Finset ℕ :=
  Finset.univ.image (@threeAdicFrequencyValue r k)

theorem card_threeAdicRowSet (r k : ℕ) :
    (threeAdicRowSet r k).card = 2 * 3 ^ (r - (k + 1)) := by
  rw [threeAdicRowSet, Finset.card_image_of_injective _ threeAdicRowIndex_injective]
  simp [card_threeAdicRow]

theorem card_threeAdicFrequencySet (r k : ℕ) :
    (threeAdicFrequencySet r k).card = 3 ^ k := by
  rw [threeAdicFrequencySet,
    Finset.card_image_of_injective _ threeAdicFrequencyValue_injective]
  simp [card_threeAdicFrequency]

/-- Every parametrized row has exactly the valuation prescribed by `Y_(k+1)`. -/
theorem threeAdicRowIndex_exact_layer {r k : ℕ} (hk : k < r)
    (i : ThreeAdicRow r k) :
    threeAdicRowIndex i < 3 ^ r ∧
      3 ^ k ∣ 2 * threeAdicRowIndex i + 1 ∧
      ¬3 ^ (k + 1) ∣ 2 * threeAdicRowIndex i + 1 := by
  refine ⟨threeAdicRowIndex_lt_pow hk i, ?_, ?_⟩
  · exact ⟨threeAdicRowUnit i, threeAdicRow_numerator i⟩
  · intro hdiv
    rw [threeAdicRow_numerator, pow_succ] at hdiv
    have : 3 ∣ threeAdicRowUnit i :=
      (Nat.mul_dvd_mul_iff_left (pow_pos (by decide) _)).mp hdiv
    exact threeAdicRowUnit_not_three_dvd i this

/-- Every parametrized frequency has exactly the primitive numerator prescribed by `W_(k+1)`. -/
theorem threeAdicFrequencyValue_exact_band {r k : ℕ} (_hk : k < r)
    (a : ThreeAdicFrequency k) :
    ∃ m : ℕ, 0 < m ∧ m < 3 ^ (k + 1) ∧ Odd m ∧ ¬3 ∣ m ∧
      threeAdicFrequencyValue (r := r) a = m * 3 ^ (r - (k + 1)) := by
  exact ⟨threeAdicFrequencyNumerator a, threeAdicFrequencyNumerator_pos a,
    threeAdicFrequencyNumerator_lt a, threeAdicFrequencyNumerator_odd a,
    threeAdicFrequencyNumerator_not_three_dvd a, rfl⟩

/-- A cosine at an odd multiple of `π/2` vanishes. -/
theorem cos_nat_mul_pi_div_two_eq_zero {q : ℕ} (hq : Odd q) :
    Real.cos ((q : ℝ) * Real.pi / 2) = 0 := by
  rcases hq with ⟨j, rfl⟩
  rw [Real.cos_eq_zero_iff]
  refine ⟨(j : ℤ), ?_⟩
  push_cast
  ring

/-- On its own row layer, a band frequency has the paper's `m u π / 6` phase. -/
theorem threeAdic_diagonal_phase {r k : ℕ} (hk : k < r)
    (i : ThreeAdicRow r k) (a : ThreeAdicFrequency k) :
    (threeAdicFrequencyValue (r := r) a : ℝ) *
        Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i) =
      ((threeAdicFrequencyNumerator a * threeAdicRowUnit i : ℕ) : ℝ) *
        Real.pi / 6 := by
  have hr : r = (k + 1) + (r - (k + 1)) := by omega
  have hn : 3 ^ r = 3 ^ (k + 1) * 3 ^ (r - (k + 1)) := by
    nth_rw 1 [hr, pow_add]
  unfold Spikes.chebyshevRootPhase
  rw [threeAdicRow_numerator, hn]
  simp only [threeAdicFrequencyValue, pow_succ]
  push_cast
  field_simp
  ring

/-- A frequency from an earlier band has an odd-half-period phase on a deeper row layer. -/
theorem threeAdic_lower_phase {r p k : ℕ} (hpk : p < k) (hkr : k < r)
    (i : ThreeAdicRow r k) (a : ThreeAdicFrequency p) :
    (threeAdicFrequencyValue (r := r) a : ℝ) *
        Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i) =
      ((threeAdicFrequencyNumerator a * 3 ^ (k - (p + 1)) *
          threeAdicRowUnit i : ℕ) : ℝ) * Real.pi / 2 := by
  have hr : r = (p + 1) + (r - (p + 1)) := by omega
  have hk : k = (p + 1) + (k - (p + 1)) := by omega
  have hn : 3 ^ r = 3 ^ (p + 1) * 3 ^ (r - (p + 1)) := by
    nth_rw 1 [hr, pow_add]
  have hkpow : 3 ^ k = 3 ^ (p + 1) * 3 ^ (k - (p + 1)) := by
    nth_rw 1 [hk, pow_add]
  unfold Spikes.chebyshevRootPhase
  rw [threeAdicRow_numerator, hn, hkpow]
  simp only [threeAdicFrequencyValue, pow_succ]
  push_cast
  field_simp

/-- Paper Lemma 5.1, strict lower-band invisibility in one coordinate. -/
theorem threeAdic_lower_band_invisible {r p k : ℕ} (hpk : p < k) (hkr : k < r)
    (i : ThreeAdicRow r k) (a : ThreeAdicFrequency p) :
    Real.cos ((threeAdicFrequencyValue (r := r) a : ℝ) *
      Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i)) = 0 := by
  rw [threeAdic_lower_phase hpk hkr]
  apply cos_nat_mul_pi_div_two_eq_zero
  exact ((threeAdicFrequencyNumerator_odd a).mul
    ((show Odd (3 ^ (k - (p + 1))) from (show Odd 3 by decide).pow))).mul
      (threeAdicRowUnit_odd i)

/-! ## The diagonal character modulo twelve -/

/-- The real sign character on units modulo `12`, extended arbitrarily off the units. -/
def modTwelveCharacter (s : ℕ) : ℝ :=
  if s % 12 = 1 ∨ s % 12 = 11 then 1 else -1

theorem modTwelveCharacter_mem (s : ℕ) :
    modTwelveCharacter s = 1 ∨ modTwelveCharacter s = -1 := by
  simp only [modTwelveCharacter]
  split_ifs <;> simp

theorem modTwelveCharacter_ne_zero (s : ℕ) : modTwelveCharacter s ≠ 0 := by
  rcases modTwelveCharacter_mem s with h | h <;> simp [h]

/-- An odd integer prime to `3` is in one of the four unit classes modulo `12`. -/
theorem mod_twelve_eq_of_odd_not_three_dvd {s : ℕ} (hs : Odd s) (h3 : ¬3 ∣ s) :
    s % 12 = 1 ∨ s % 12 = 5 ∨ s % 12 = 7 ∨ s % 12 = 11 := by
  have hlt : s % 12 < 12 := Nat.mod_lt _ (by decide)
  have htwo : (s % 12) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd s (by decide : 2 ∣ 12)]
    exact Nat.odd_iff.mp hs
  have hthree : (s % 12) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd s (by decide : 3 ∣ 12)]
    exact (Nat.dvd_iff_mod_eq_zero.not.mp h3)
  omega

/-- The sign is multiplicative on the units modulo `12`. -/
theorem modTwelveCharacter_mul {m u : ℕ}
    (hm : Odd m) (hmu : ¬3 ∣ m) (hu : Odd u) (hu3 : ¬3 ∣ u) :
    modTwelveCharacter (m * u) = modTwelveCharacter m * modTwelveCharacter u := by
  rcases mod_twelve_eq_of_odd_not_three_dvd hm hmu with hm12 | hm12 | hm12 | hm12 <;>
    rcases mod_twelve_eq_of_odd_not_three_dvd hu hu3 with hu12 | hu12 | hu12 | hu12 <;>
    simp [modTwelveCharacter, Nat.mul_mod, hm12, hu12]

/-- Reduction of the sixth-angle cosine to a residue modulo `12`. -/
theorem cos_nat_mul_pi_div_six_mod (s : ℕ) :
    Real.cos ((s : ℝ) * Real.pi / 6) =
      Real.cos (((s % 12 : ℕ) : ℝ) * Real.pi / 6) := by
  have hsNat := Nat.mod_add_div s 12
  have hsReal : (s : ℝ) = (s % 12 : ℕ) + 12 * (s / 12 : ℕ) := by
    exact_mod_cast hsNat.symm
  have hangle :
      (s : ℝ) * Real.pi / 6 =
        ((s % 12 : ℕ) : ℝ) * Real.pi / 6 +
          (s / 12 : ℕ) * (2 * Real.pi) := by
    rw [hsReal]
    ring
  rw [hangle, Real.cos_add_nat_mul_two_pi]

/-- The exact four-value evaluation used in the paper's diagonal replication. -/
theorem cos_nat_mul_pi_div_six_eq_character {s : ℕ}
    (hs : Odd s) (h3 : ¬3 ∣ s) :
    Real.cos ((s : ℝ) * Real.pi / 6) =
      Real.sqrt 3 / 2 * modTwelveCharacter s := by
  rw [cos_nat_mul_pi_div_six_mod]
  rcases mod_twelve_eq_of_odd_not_three_dvd hs h3 with h | h | h | h
  · simp [h, modTwelveCharacter, Real.cos_pi_div_six]
  · have hangle : ((5 : ℕ) : ℝ) * Real.pi / 6 =
        Real.pi - Real.pi / 6 := by norm_num; ring
    rw [h, hangle, Real.cos_pi_sub, Real.cos_pi_div_six]
    simp [modTwelveCharacter, h]
  · have hangle : ((7 : ℕ) : ℝ) * Real.pi / 6 =
        Real.pi / 6 + Real.pi := by norm_num; ring
    rw [h, hangle, Real.cos_add_pi, Real.cos_pi_div_six]
    simp [modTwelveCharacter, h]
  · have hangle : ((11 : ℕ) : ℝ) * Real.pi / 6 =
        2 * Real.pi - Real.pi / 6 := by norm_num; ring
    rw [h, hangle, Real.cos_two_pi_sub, Real.cos_pi_div_six]
    simp [modTwelveCharacter, h]

/-- Paper Eq. (5.7): the diagonal cosine splits into frequency and row signs. -/
theorem threeAdic_diagonal_cosine_factor {r k : ℕ} (hk : k < r)
    (i : ThreeAdicRow r k) (a : ThreeAdicFrequency k) :
    Real.cos ((threeAdicFrequencyValue (r := r) a : ℝ) *
        Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i)) =
      Real.sqrt 3 / 2 *
        modTwelveCharacter (threeAdicFrequencyNumerator a) *
        modTwelveCharacter (threeAdicRowUnit i) := by
  rw [threeAdic_diagonal_phase hk]
  rw [cos_nat_mul_pi_div_six_eq_character]
  · rw [modTwelveCharacter_mul]
    ring
    exact threeAdicFrequencyNumerator_odd a
    exact threeAdicFrequencyNumerator_not_three_dvd a
    exact threeAdicRowUnit_odd i
    exact threeAdicRowUnit_not_three_dvd i
  · exact (threeAdicFrequencyNumerator_odd a).mul (threeAdicRowUnit_odd i)
  · exact (show Nat.Prime 3 by norm_num).not_dvd_mul
      (threeAdicFrequencyNumerator_not_three_dvd a)
      (threeAdicRowUnit_not_three_dvd i)

theorem threeAdic_diagonal_cosine_ne_zero {r k : ℕ} (hk : k < r)
    (i : ThreeAdicRow r k) (a : ThreeAdicFrequency k) :
    Real.cos ((threeAdicFrequencyValue (r := r) a : ℝ) *
      Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i)) ≠ 0 := by
  rw [threeAdic_diagonal_cosine_factor hk]
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) (by norm_num))
      (modTwelveCharacter_ne_zero _))
    (modTwelveCharacter_ne_zero _)

/-! ## Disjoint bands and the two-coordinate visibility relation -/

theorem threeAdicFrequencyValue_ne_of_lt {r p k : ℕ}
    (hpk : p < k) (hkr : k < r)
    (a : ThreeAdicFrequency p) (b : ThreeAdicFrequency k) :
    threeAdicFrequencyValue (r := r) a ≠ threeAdicFrequencyValue (r := r) b := by
  intro hab
  have hexp : r - (p + 1) = (k - p) + (r - (k + 1)) := by omega
  have hpow : 3 ^ (r - (p + 1)) =
      3 ^ (k - p) * 3 ^ (r - (k + 1)) := by
    calc
      3 ^ (r - (p + 1)) = 3 ^ ((k - p) + (r - (k + 1))) :=
        congrArg (fun e : ℕ => 3 ^ e) hexp
      _ = _ := pow_add 3 (k - p) (r - (k + 1))
  simp only [threeAdicFrequencyValue] at hab
  rw [hpow] at hab
  have hcancel : threeAdicFrequencyNumerator a * 3 ^ (k - p) =
      threeAdicFrequencyNumerator b := by
    have heq :
        (threeAdicFrequencyNumerator a * 3 ^ (k - p)) *
            3 ^ (r - (k + 1)) =
          threeAdicFrequencyNumerator b * 3 ^ (r - (k + 1)) := by
      simpa only [mul_assoc] using hab
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by decide) _) heq
  have hdivpow : 3 ∣ 3 ^ (k - p) :=
    dvd_pow_self 3 (Nat.sub_ne_zero_of_lt hpk)
  rcases hdivpow with ⟨c, hc⟩
  apply threeAdicFrequencyNumerator_not_three_dvd b
  refine ⟨threeAdicFrequencyNumerator a * c, ?_⟩
  rw [← hcancel, hc]
  ring

theorem threeAdicFrequencySet_disjoint_of_lt {r p k : ℕ}
    (hpk : p < k) (hkr : k < r) :
    Disjoint (threeAdicFrequencySet r p) (threeAdicFrequencySet r k) := by
  rw [Finset.disjoint_left]
  intro x hxp hxk
  simp only [threeAdicFrequencySet, Finset.mem_image, Finset.mem_univ, true_and] at hxp hxk
  rcases hxp with ⟨a, rfl⟩
  rcases hxk with ⟨b, hab⟩
  exact threeAdicFrequencyValue_ne_of_lt hpk hkr a b hab.symm

theorem threeAdicRowSet_disjoint_of_lt {r p k : ℕ}
    (hpk : p < k) (hkr : k < r) :
    Disjoint (threeAdicRowSet r p) (threeAdicRowSet r k) := by
  rw [Finset.disjoint_left]
  intro x hxp hxk
  simp only [threeAdicRowSet, Finset.mem_image, Finset.mem_univ, true_and] at hxp hxk
  rcases hxp with ⟨i, rfl⟩
  rcases hxk with ⟨j, hij⟩
  have hi := threeAdicRowIndex_exact_layer (hpk.trans hkr) i
  have hj := threeAdicRowIndex_exact_layer hkr j
  apply hi.2.2
  have hpow : 3 ^ (p + 1) ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
  exact hpow.trans (hij ▸ hj.2.1)

/-- The exact balanced-layer count `|Y_(k+1)| |W_(k+1)| = 2·3^(r-1)`. -/
theorem threeAdic_layer_card_product {r k : ℕ} (hk : k < r) :
    (threeAdicRowSet r k).card * (threeAdicFrequencySet r k).card =
      2 * 3 ^ (r - 1) := by
  rw [card_threeAdicRowSet, card_threeAdicFrequencySet]
  have hexp : r - (k + 1) + k = r - 1 := by omega
  calc
    (2 * 3 ^ (r - (k + 1))) * 3 ^ k =
        2 * (3 ^ (r - (k + 1)) * 3 ^ k) := by ring
    _ = 2 * 3 ^ (r - 1) := by rw [← pow_add, hexp]

/-- The parametrized row layers contain exactly `3^r - 1` rows in total. -/
theorem threeAdicRowSet_card_sum (r : ℕ) :
    ∑ k ∈ Finset.range r, (threeAdicRowSet r k).card = 3 ^ r - 1 := by
  have hpos : 0 < (3 : ℕ) ^ r := pow_pos (by decide) r
  have hone : 1 ≤ (3 : ℕ) ^ r := hpos
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hone]
  push_cast
  simpa only [card_threeAdicRowSet, rowMultiplicity, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow] using rowMultiplicity_sum r

/-- The unique row retained in the paper's terminal set `X_r`. -/
def threeAdicCentralRow (r : ℕ) : ℕ := 3 ^ r / 2

theorem threeAdicCentralRow_numerator (r : ℕ) :
    2 * threeAdicCentralRow r + 1 = 3 ^ r := by
  have hodd : Odd ((3 : ℕ) ^ r) := (show Odd 3 by decide).pow
  have hdiv := Nat.two_mul_odd_div_two (Nat.odd_iff.mp hodd)
  have hpos : 0 < (3 : ℕ) ^ r := pow_pos (by decide) r
  simp only [threeAdicCentralRow]
  calc
    2 * (3 ^ r / 2) + 1 = (3 ^ r - 1) + 1 := by rw [hdiv]
    _ = 3 ^ r := Nat.sub_add_cancel hpos

theorem threeAdicCentralRow_lt (r : ℕ) : threeAdicCentralRow r < 3 ^ r := by
  exact Nat.div_lt_self (pow_pos (by decide) r) (by decide)

theorem threeAdicCentralRow_not_mem_rowSet {r k : ℕ} (hk : k < r) :
    threeAdicCentralRow r ∉ threeAdicRowSet r k := by
  intro hmem
  simp only [threeAdicRowSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨i, hi⟩
  have hexact := threeAdicRowIndex_exact_layer hk i
  apply hexact.2.2
  have hpow : 3 ^ (k + 1) ∣ 3 ^ r := pow_dvd_pow 3 (by omega)
  rw [← threeAdicCentralRow_numerator r, ← hi] at hpow
  exact hpow

/-- The discrete-cosine weight of a tensor frequency on a tensor row cell. -/
noncomputable def threeAdicTensorCellWeight {r k l p q : ℕ}
    (i : ThreeAdicRow r k) (j : ThreeAdicRow r l)
    (a : ThreeAdicFrequency p) (b : ThreeAdicFrequency q) : ℝ :=
  Real.cos ((threeAdicFrequencyValue (r := r) a : ℝ) *
      Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex i)) *
    Real.cos ((threeAdicFrequencyValue (r := r) b : ℝ) *
      Spikes.chebyshevRootPhase (3 ^ r) (threeAdicRowIndex j))

/-- A tensor block is invisible if either source coordinate lies below the target layer. -/
theorem threeAdic_tensor_invisible {r k l p q : ℕ}
    (hkr : k < r) (hlr : l < r)
    (i : ThreeAdicRow r k) (j : ThreeAdicRow r l)
    (a : ThreeAdicFrequency p) (b : ThreeAdicFrequency q)
    (hbelow : p < k ∨ q < l) :
    threeAdicTensorCellWeight i j a b = 0 := by
  rcases hbelow with hpk | hql
  · simp [threeAdicTensorCellWeight, threeAdic_lower_band_invisible hpk hkr]
  · simp [threeAdicTensorCellWeight, threeAdic_lower_band_invisible hql hlr]

/-- On a diagonal tensor layer the row dependence and frequency dependence separate. -/
theorem threeAdic_tensor_diagonal_factor {r k l : ℕ}
    (hkr : k < r) (hlr : l < r)
    (i : ThreeAdicRow r k) (j : ThreeAdicRow r l)
    (a : ThreeAdicFrequency k) (b : ThreeAdicFrequency l) :
    threeAdicTensorCellWeight i j a b =
      (3 / 4 : ℝ) *
        (modTwelveCharacter (threeAdicRowUnit i) *
          modTwelveCharacter (threeAdicRowUnit j)) *
        (modTwelveCharacter (threeAdicFrequencyNumerator a) *
          modTwelveCharacter (threeAdicFrequencyNumerator b)) := by
  rw [threeAdicTensorCellWeight, threeAdic_diagonal_cosine_factor hkr,
    threeAdic_diagonal_cosine_factor hlr]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 3 / 2 * modTwelveCharacter (threeAdicFrequencyNumerator a) *
          modTwelveCharacter (threeAdicRowUnit i)) *
        (Real.sqrt 3 / 2 * modTwelveCharacter (threeAdicFrequencyNumerator b) *
          modTwelveCharacter (threeAdicRowUnit j)) =
      (Real.sqrt 3 ^ 2 / 4) *
        (modTwelveCharacter (threeAdicRowUnit i) *
          modTwelveCharacter (threeAdicRowUnit j)) *
        (modTwelveCharacter (threeAdicFrequencyNumerator a) *
          modTwelveCharacter (threeAdicFrequencyNumerator b)) := by ring
    _ = _ := by rw [hsqrt]

theorem threeAdic_tensor_diagonal_ne_zero {r k l : ℕ}
    (hkr : k < r) (hlr : l < r)
    (i : ThreeAdicRow r k) (j : ThreeAdicRow r l)
    (a : ThreeAdicFrequency k) (b : ThreeAdicFrequency l) :
    threeAdicTensorCellWeight i j a b ≠ 0 := by
  unfold threeAdicTensorCellWeight
  exact mul_ne_zero (threeAdic_diagonal_cosine_ne_zero hkr i a)
    (threeAdic_diagonal_cosine_ne_zero hlr j b)

end Hilbert16
