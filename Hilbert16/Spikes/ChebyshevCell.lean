import Hilbert16.Hypergeometric.EllipseScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- Paper Eq. (3.4)'s inverse-branch sign, written without an integer power coercion. -/
def chebyshevCellOrientation (i : ℕ) : ℝ :=
  if Even i then -1 else 1

theorem chebyshevCellOrientation_eq_negOnePow (i : ℕ) :
    chebyshevCellOrientation i = (-1 : ℝ) ^ (i + 1) := by
  by_cases hi : Even i
  · simp [chebyshevCellOrientation, hi, pow_succ, hi.neg_one_pow]
  · have hiodd : Odd i := Nat.not_even_iff_odd.mp hi
    simp [chebyshevCellOrientation, hi, pow_succ, hiodd.neg_one_pow]

theorem chebyshevCellOrientation_mem (i : ℕ) :
    chebyshevCellOrientation i = -1 ∨ chebyshevCellOrientation i = 1 := by
  unfold chebyshevCellOrientation
  split_ifs <;> simp

theorem chebyshevCellOrientation_ne_zero (i : ℕ) :
    chebyshevCellOrientation i ≠ 0 := by
  rcases chebyshevCellOrientation_mem i with h | h <;> simp [h]

/-- The midpoint phase of the `i`-th monotonicity cell. -/
noncomputable def chebyshevRootPhase (n i : ℕ) : ℝ :=
  ((2 * i + 1 : ℕ) : ℝ) * Real.pi / (2 * (n : ℝ))

/-- Paper Eq. (3.4)'s explicit inverse branch of the `n`-th Chebyshev polynomial. -/
noncomputable def chebyshevInverseBranch (n i : ℕ) (u : ℝ) : ℝ :=
  Real.cos (chebyshevRootPhase n i +
    chebyshevCellOrientation i * Real.arcsin u / (n : ℝ))

/-- The displayed branch is a genuine right inverse of `T_n` on `[-1,1]`. -/
theorem eval_chebyshevInverseBranch
    {n i : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : |u| ≤ 1) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (chebyshevInverseBranch n i u) = u := by
  rw [chebyshevInverseBranch, Polynomial.Chebyshev.T_real_cos]
  have huneg : -1 ≤ u := (abs_le.mp hu).1
  have hupos : u ≤ 1 := (abs_le.mp hu).2
  by_cases hi : Even i
  · obtain ⟨k, rfl⟩ := hi
    have hangle :
        (n : ℝ) * (chebyshevRootPhase n (k + k) +
          chebyshevCellOrientation (k + k) * Real.arcsin u / (n : ℝ)) =
          (Real.pi / 2 - Real.arcsin u) + (k : ℤ) * (2 * Real.pi) := by
      simp only [chebyshevRootPhase, chebyshevCellOrientation,
        if_pos (by simp : Even (k + k))]
      field_simp [hn]
      push_cast
      ring
    rw [show ((n : ℤ) : ℝ) = (n : ℝ) by norm_num, hangle,
      Real.cos_add_int_mul_two_pi, Real.cos_pi_div_two_sub,
      Real.sin_arcsin huneg hupos]

  · have hiodd : Odd i := Nat.not_even_iff_odd.mp hi
    obtain ⟨k, rfl⟩ := hiodd
    have hangle :
        (n : ℝ) * (chebyshevRootPhase n (2 * k + 1) +
          chebyshevCellOrientation (2 * k + 1) * Real.arcsin u / (n : ℝ)) =
          (Real.arcsin u - Real.pi / 2) + ((k + 1 : ℕ) : ℤ) * (2 * Real.pi) := by
      simp only [chebyshevRootPhase, chebyshevCellOrientation,
        if_neg (by omega : ¬ Even (2 * k + 1))]
      field_simp [hn]
      push_cast
      ring
    rw [show ((n : ℤ) : ℝ) = (n : ℝ) by norm_num, hangle,
      Real.cos_add_int_mul_two_pi, Real.cos_sub_pi_div_two,
      Real.sin_arcsin huneg hupos]

/-- Derivative of the explicit inverse branch on the open unit interval. -/
theorem chebyshevInverseBranch_hasDerivAt
    {n i : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (chebyshevInverseBranch n i)
      ((-chebyshevCellOrientation i) *
        Real.sin (chebyshevRootPhase n i +
          chebyshevCellOrientation i * Real.arcsin u / (n : ℝ)) /
        ((n : ℝ) * Real.sqrt (1 - u ^ 2))) u := by
  have huNeg : u ≠ -1 := by
    have := (abs_lt.mp hu).1
    linarith
  have huPos : u ≠ 1 := by
    have := (abs_lt.mp hu).2
    linarith
  have hscaled := ((Real.hasDerivAt_arcsin huNeg huPos).const_mul
    (chebyshevCellOrientation i)).div_const (n : ℝ)
  have hangle := hscaled.const_add (chebyshevRootPhase n i)
  have hcos := hangle.cos
  change HasDerivAt (fun x : ℝ => Real.cos (chebyshevRootPhase n i +
    chebyshevCellOrientation i * Real.arcsin x / (n : ℝ))) _ u
  convert hcos using 1
  all_goals field_simp [hn]

/-- For an actual cell index, the branch angle remains strictly between `0` and `pi`. -/
theorem chebyshevInverseBranch_angle_mem_Ioo
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) {u : ℝ} (hu : |u| < 1) :
    chebyshevRootPhase n i +
        chebyshevCellOrientation i * Real.arcsin u / (n : ℝ) ∈
      Set.Ioo (0 : ℝ) Real.pi := by
  have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have huBounds := abs_lt.mp hu
  have hasinLo : -(Real.pi / 2) < Real.arcsin u :=
    Real.neg_pi_div_two_lt_arcsin.mpr huBounds.1
  have hasinHi : Real.arcsin u < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr huBounds.2
  have heps : -(Real.pi / 2) < chebyshevCellOrientation i * Real.arcsin u ∧
      chebyshevCellOrientation i * Real.arcsin u < Real.pi / 2 := by
    rcases chebyshevCellOrientation_mem i with hneg | hpos
    · rw [hneg]
      constructor <;> nlinarith
    · rw [hpos, one_mul]
      exact ⟨hasinLo, hasinHi⟩
  let theta := chebyshevRootPhase n i +
    chebyshevCellOrientation i * Real.arcsin u / (n : ℝ)
  have hscaled : (n : ℝ) * theta =
      (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / 2 +
        chebyshevCellOrientation i * Real.arcsin u := by
    dsimp [theta, chebyshevRootPhase]
    field_simp [hn]
  have hbaseLo : Real.pi / 2 ≤
      (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / 2 := by
    have hipi : 0 ≤ (i : ℝ) * Real.pi :=
      mul_nonneg (Nat.cast_nonneg i) Real.pi_pos.le
    push_cast
    nlinarith
  have hscaledPos : 0 < (n : ℝ) * theta := by
    rw [hscaled]
    nlinarith [hbaseLo, heps.1]
  have hthetaPos : 0 < theta := by
    rcases (mul_pos_iff.mp hscaledPos) with hboth | hboth
    · exact hboth.2
    · exact (not_lt_of_ge hnPos.le hboth.1).elim
  have hiSucc : ((i + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hscaledHi : (n : ℝ) * theta < (n : ℝ) * Real.pi := by
    rw [hscaled]
    calc
      (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / 2 +
          chebyshevCellOrientation i * Real.arcsin u <
        (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / 2 + Real.pi / 2 :=
          by nlinarith [heps.2]
      _ = ((i + 1 : ℕ) : ℝ) * Real.pi := by push_cast; ring
      _ ≤ (n : ℝ) * Real.pi :=
        mul_le_mul_of_nonneg_right hiSucc Real.pi_pos.le
  have hthetaHi : theta < Real.pi := by nlinarith [hscaledHi, hnPos]
  exact ⟨hthetaPos, hthetaHi⟩

theorem chebyshevInverseBranch_sin_pos
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) {u : ℝ} (hu : |u| < 1) :
    0 < Real.sin (chebyshevRootPhase n i +
      chebyshevCellOrientation i * Real.arcsin u / (n : ℝ)) :=
  Real.sin_pos_of_mem_Ioo (chebyshevInverseBranch_angle_mem_Ioo hn hi hu)

/-- The inverse branch has the constant derivative sign `-chebyshevCellOrientation i`
on the open unit interval.  Multiplying by that sign makes the derivative positive. -/
theorem chebyshevInverseBranch_orientation_mul_deriv_pos
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) {u : ℝ} (hu : |u| < 1) :
    0 < (-chebyshevCellOrientation i) *
      deriv (chebyshevInverseBranch n i) u := by
  have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have huBounds := abs_lt.mp hu
  have hrad : 0 < 1 - u ^ 2 := by nlinarith [huBounds.1, huBounds.2]
  have hsqrt : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 hrad
  have hden : 0 < (n : ℝ) * Real.sqrt (1 - u ^ 2) := mul_pos hnPos hsqrt
  have hsin := chebyshevInverseBranch_sin_pos hn hi hu
  rw [(chebyshevInverseBranch_hasDerivAt hn hu).deriv]
  rcases chebyshevCellOrientation_mem i with hneg | hpos
  · rw [hneg] at hsin ⊢
    norm_num at hsin ⊢
    exact div_pos hsin hden
  · rw [hpos] at hsin ⊢
    norm_num at hsin ⊢
    rw [neg_div]
    exact neg_lt_zero.mpr (div_pos hsin hden)

theorem chebyshevInverseBranch_deriv_ne_zero
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) {u : ℝ} (hu : |u| < 1) :
    deriv (chebyshevInverseBranch n i) u ≠ 0 := by
  intro hzero
  have hpos := chebyshevInverseBranch_orientation_mul_deriv_pos hn hi hu
  rw [hzero, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Orientation of the product inverse branch on the `(i,j)` Chebyshev cell. -/
def chebyshevCellJacobianOrientation (i j : ℕ) : ℝ :=
  chebyshevCellOrientation i * chebyshevCellOrientation j

theorem chebyshevCellJacobianOrientation_mem (i j : ℕ) :
    chebyshevCellJacobianOrientation i j = -1 ∨
      chebyshevCellJacobianOrientation i j = 1 := by
  rcases chebyshevCellOrientation_mem i with hi | hi <;>
    rcases chebyshevCellOrientation_mem j with hj | hj <;>
      simp [chebyshevCellJacobianOrientation, hi, hj]

theorem chebyshevCellJacobianOrientation_ne_zero (i j : ℕ) :
    chebyshevCellJacobianOrientation i j ≠ 0 := by
  rcases chebyshevCellJacobianOrientation_mem i j with h | h <;> simp [h]

/-- The two-dimensional inverse branch has the constant Jacobian sign encoded by
`chebyshevCellJacobianOrientation i j`. -/
theorem chebyshevCellJacobianOrientation_mul_deriv_product_pos
    {n m i j : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hi : i < n) (hj : j < m)
    {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    0 < chebyshevCellJacobianOrientation i j *
      (deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch m j) v) := by
  have hiPos := chebyshevInverseBranch_orientation_mul_deriv_pos hn hi hu
  have hjPos := chebyshevInverseBranch_orientation_mul_deriv_pos hm hj hv
  have hprod := mul_pos hiPos hjPos
  dsimp [chebyshevCellJacobianOrientation] at ⊢
  rw [show chebyshevCellOrientation i * chebyshevCellOrientation j *
      (deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch m j) v) =
      ((-chebyshevCellOrientation i) * deriv (chebyshevInverseBranch n i) u) *
        ((-chebyshevCellOrientation j) * deriv (chebyshevInverseBranch m j) v) by ring]
  exact hprod

/-- Paper Eq. (3.5): a mode pulled back through one inverse branch splits into an even cosine
part and an odd sine part. -/
theorem eval_chebyshevInverseBranch_mode
    {n : ℕ} (i a : ℕ) (u : ℝ) :
    (Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i u) =
      Real.cos ((a : ℝ) * chebyshevRootPhase n i) *
          Real.cos (((a : ℝ) / (n : ℝ)) * Real.arcsin u) -
        chebyshevCellOrientation i *
          Real.sin ((a : ℝ) * chebyshevRootPhase n i) *
          Real.sin (((a : ℝ) / (n : ℝ)) * Real.arcsin u) := by
  rw [chebyshevInverseBranch, Polynomial.Chebyshev.T_real_cos]
  have hangle :
      ((a : ℤ) : ℝ) * (chebyshevRootPhase n i +
        chebyshevCellOrientation i * Real.arcsin u / (n : ℝ)) =
        (a : ℝ) * chebyshevRootPhase n i +
          chebyshevCellOrientation i *
            (((a : ℝ) / (n : ℝ)) * Real.arcsin u) := by
    push_cast
    ring
  rw [hangle, Real.cos_add]
  by_cases hi : Even i
  · simp [chebyshevCellOrientation, hi, Real.cos_neg, Real.sin_neg]
  · simp [chebyshevCellOrientation, hi]

theorem chebyshevOddMode_neg (n a : ℕ) (u : ℝ) :
    Real.sin (((a : ℝ) / (n : ℝ)) * Real.arcsin (-u)) =
      -Real.sin (((a : ℝ) / (n : ℝ)) * Real.arcsin u) := by
  rw [Real.arcsin_neg, mul_neg, Real.sin_neg]

theorem chebyshevEvenMode_neg (n a : ℕ) (u : ℝ) :
    Real.cos (((a : ℝ) / (n : ℝ)) * Real.arcsin (-u)) =
      Real.cos (((a : ℝ) / (n : ℝ)) * Real.arcsin u) := by
  rw [Real.arcsin_neg, mul_neg, Real.cos_neg]

/-- Reflection symmetry of the ellipse annihilates every integrable function odd in `u`. -/
theorem integral_ellipticEnergyDisk_eq_zero_of_odd_fst
    {lambda h : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (ellipticEnergyDisk lambda h))
    (hodd : ∀ u v, f (-u, v) = -f (u, v)) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) = 0 := by
  let G : ℝ × ℝ → ℝ := (ellipticEnergyDisk lambda h).indicator f
  have hGint : MeasureTheory.Integrable G :=
    hf.integrable_indicator (measurableSet_ellipticEnergyDisk lambda h)
  have hGodd : ∀ u v, G (-u, v) = -G (u, v) := by
    intro u v
    have hmem : (-u, v) ∈ ellipticEnergyDisk lambda h ↔
        (u, v) ∈ ellipticEnergyDisk lambda h := by
      simp only [ellipticEnergyDisk, Set.mem_ofPred_eq, neg_sq]
    by_cases huv : (u, v) ∈ ellipticEnergyDisk lambda h
    · have hneg := hmem.mpr huv
      simp only [G, Set.indicator_of_mem hneg, Set.indicator_of_mem huv, hodd]
    · have hneg : (-u, v) ∉ ellipticEnergyDisk lambda h := fun H => huv (hmem.mp H)
      simp only [G, Set.indicator_of_notMem hneg, Set.indicator_of_notMem huv, neg_zero]
  have hinner : ∀ v : ℝ, (∫ u : ℝ, G (u, v)) = 0 := by
    intro v
    have H := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => G (u, v)) (-1)
    have hsame : (∫ u : ℝ, G (-u, v)) = ∫ u : ℝ, G (u, v) := by
      simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using H
    have hneg : (∫ u : ℝ, G (-u, v)) = -∫ u : ℝ, G (u, v) := by
      calc
        (∫ u : ℝ, G (-u, v)) = ∫ u : ℝ, -G (u, v) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun u => hGodd u v
        _ = -∫ u : ℝ, G (u, v) := by rw [MeasureTheory.integral_neg]
    linarith
  have hFubini : (∫ z : ℝ × ℝ, G z) = ∫ v : ℝ, ∫ u : ℝ, G (u, v) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod_symm G
      (by simpa only [MeasureTheory.Measure.volume_eq_prod] using hGint)
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
        ∫ z : ℝ × ℝ, G z := by
      change (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
        ∫ z : ℝ × ℝ, (ellipticEnergyDisk lambda h).indicator f z
      rw [MeasureTheory.integral_indicator (measurableSet_ellipticEnergyDisk lambda h)]
    _ = ∫ v : ℝ, ∫ u : ℝ, G (u, v) := hFubini
    _ = 0 := by simp_rw [hinner]; simp

/-- Reflection symmetry of the ellipse annihilates every integrable function odd in `v`. -/
theorem integral_ellipticEnergyDisk_eq_zero_of_odd_snd
    {lambda h : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (ellipticEnergyDisk lambda h))
    (hodd : ∀ u v, f (u, -v) = -f (u, v)) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) = 0 := by
  let G : ℝ × ℝ → ℝ := (ellipticEnergyDisk lambda h).indicator f
  have hGint : MeasureTheory.Integrable G :=
    hf.integrable_indicator (measurableSet_ellipticEnergyDisk lambda h)
  have hGodd : ∀ u v, G (u, -v) = -G (u, v) := by
    intro u v
    have hmem : (u, -v) ∈ ellipticEnergyDisk lambda h ↔
        (u, v) ∈ ellipticEnergyDisk lambda h := by
      simp only [ellipticEnergyDisk, Set.mem_ofPred_eq, neg_sq]
    by_cases huv : (u, v) ∈ ellipticEnergyDisk lambda h
    · have hneg := hmem.mpr huv
      simp only [G, Set.indicator_of_mem hneg, Set.indicator_of_mem huv, hodd]
    · have hneg : (u, -v) ∉ ellipticEnergyDisk lambda h := fun H => huv (hmem.mp H)
      simp only [G, Set.indicator_of_notMem hneg, Set.indicator_of_notMem huv, neg_zero]
  have hinner : ∀ u : ℝ, (∫ v : ℝ, G (u, v)) = 0 := by
    intro u
    have H := MeasureTheory.Measure.integral_comp_mul_left
      (fun v : ℝ => G (u, v)) (-1)
    have hsame : (∫ v : ℝ, G (u, -v)) = ∫ v : ℝ, G (u, v) := by
      simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using H
    have hneg : (∫ v : ℝ, G (u, -v)) = -∫ v : ℝ, G (u, v) := by
      calc
        (∫ v : ℝ, G (u, -v)) = ∫ v : ℝ, -G (u, v) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun v => hGodd u v
        _ = -∫ v : ℝ, G (u, v) := by rw [MeasureTheory.integral_neg]
    linarith
  have hFubini : (∫ z : ℝ × ℝ, G z) = ∫ u : ℝ, ∫ v : ℝ, G (u, v) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod G
      (by simpa only [MeasureTheory.Measure.volume_eq_prod] using hGint)
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
        ∫ z : ℝ × ℝ, G z := by
      change (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
        ∫ z : ℝ × ℝ, (ellipticEnergyDisk lambda h).indicator f z
      rw [MeasureTheory.integral_indicator (measurableSet_ellipticEnergyDisk lambda h)]
    _ = ∫ u : ℝ, ∫ v : ℝ, G (u, v) := hFubini
    _ = 0 := by simp_rw [hinner]; simp

/-- A single Chebyshev tensor mode pulled back to the `(u,v)` coordinates of one cell. -/
noncomputable def chebyshevCellModeIntegrand
    (n i j a b : ℕ) (z : ℝ × ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i z.1) *
    (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval (chebyshevInverseBranch n j z.2)

/-- Paper Eq. (3.9)'s reflection step: after integration on the symmetric ellipse, only the
even--even mode survives, with exactly the discrete-cosine cell weight. -/
theorem integral_chebyshevCellMode_eq_weight_mul_evenMode
    (n i j a b : ℕ) {lambda h : ℝ} (hh : 0 < h) (hlambda : 1 ≤ lambda) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
      chebyshevCellModeIntegrand n i j a b z) =
      (Real.cos ((a : ℝ) * chebyshevRootPhase n i) *
        Real.cos ((b : ℝ) * chebyshevRootPhase n j)) *
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          ellipticModeIntegrand ((a : ℝ) / (n : ℝ)) ((b : ℝ) / (n : ℝ)) z := by
  let alpha : ℝ := (a : ℝ) / (n : ℝ)
  let beta : ℝ := (b : ℝ) / (n : ℝ)
  let A : ℝ := Real.cos ((a : ℝ) * chebyshevRootPhase n i)
  let B : ℝ := Real.cos ((b : ℝ) * chebyshevRootPhase n j)
  let C : ℝ := -chebyshevCellOrientation i *
    Real.sin ((a : ℝ) * chebyshevRootPhase n i)
  let D : ℝ := -chebyshevCellOrientation j *
    Real.sin ((b : ℝ) * chebyshevRootPhase n j)
  let EU : ℝ → ℝ := fun u => Real.cos (alpha * Real.arcsin u)
  let OU : ℝ → ℝ := fun u => Real.sin (alpha * Real.arcsin u)
  let EV : ℝ → ℝ := fun v => Real.cos (beta * Real.arcsin v)
  let OV : ℝ → ℝ := fun v => Real.sin (beta * Real.arcsin v)
  let EE : ℝ × ℝ → ℝ := fun z => EU z.1 * EV z.2
  let EO : ℝ × ℝ → ℝ := fun z => EU z.1 * OV z.2
  let OE : ℝ × ℝ → ℝ := fun z => OU z.1 * EV z.2
  let OO : ℝ × ℝ → ℝ := fun z => OU z.1 * OV z.2
  have hEE : MeasureTheory.IntegrableOn EE (ellipticEnergyDisk lambda h) :=
    continuous_integrableOn_ellipticEnergyDisk (by unfold EE EU EV; fun_prop)
      lambda hh hlambda
  have hEO : MeasureTheory.IntegrableOn EO (ellipticEnergyDisk lambda h) :=
    continuous_integrableOn_ellipticEnergyDisk (by unfold EO EU OV; fun_prop)
      lambda hh hlambda
  have hOE : MeasureTheory.IntegrableOn OE (ellipticEnergyDisk lambda h) :=
    continuous_integrableOn_ellipticEnergyDisk (by unfold OE OU EV; fun_prop)
      lambda hh hlambda
  have hOO : MeasureTheory.IntegrableOn OO (ellipticEnergyDisk lambda h) :=
    continuous_integrableOn_ellipticEnergyDisk (by unfold OO OU OV; fun_prop)
      lambda hh hlambda
  have hEOzero : (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, EO z) = 0 := by
    apply integral_ellipticEnergyDisk_eq_zero_of_odd_snd hEO
    intro u v
    unfold EO OV
    rw [Real.arcsin_neg, mul_neg, Real.sin_neg]
    ring
  have hOEzero : (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, OE z) = 0 := by
    apply integral_ellipticEnergyDisk_eq_zero_of_odd_fst hOE
    intro u v
    unfold OE OU
    rw [Real.arcsin_neg, mul_neg, Real.sin_neg]
    ring
  have hOOzero : (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, OO z) = 0 := by
    apply integral_ellipticEnergyDisk_eq_zero_of_odd_fst hOO
    intro u v
    unfold OO OU
    rw [Real.arcsin_neg, mul_neg, Real.sin_neg]
    ring
  have hdecomp : ∀ z : ℝ × ℝ,
      chebyshevCellModeIntegrand n i j a b z =
        (A * B) * EE z + ((A * D) * EO z + ((C * B) * OE z + (C * D) * OO z)) := by
    intro z
    unfold chebyshevCellModeIntegrand
    rw [eval_chebyshevInverseBranch_mode, eval_chebyshevInverseBranch_mode]
    unfold A B C D EE EO OE OO EU OU EV OV alpha beta
    ring
  have hT1 := hEE.const_mul (A * B)
  have hT2 := hEO.const_mul (A * D)
  have hT3 := hOE.const_mul (C * B)
  have hT4 := hOO.const_mul (C * D)
  have hR34 := hT3.add hT4
  have hRest := hT2.add hR34
  have hAdd34 :
      (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        (C * B) * OE z + (C * D) * OO z) =
      (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, (C * B) * OE z) +
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, (C * D) * OO z := by
    exact MeasureTheory.integral_add hT3 hT4
  have hAddRest :
      (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        (A * D) * EO z + ((C * B) * OE z + (C * D) * OO z)) =
      (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, (A * D) * EO z) +
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          ((C * B) * OE z + (C * D) * OO z) := by
    exact MeasureTheory.integral_add hT2 hR34
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        chebyshevCellModeIntegrand n i j a b z) =
      ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        ((A * B) * EE z + ((A * D) * EO z + ((C * B) * OE z + (C * D) * OO z))) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hdecomp
    _ = (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, (A * B) * EE z) +
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          ((A * D) * EO z + ((C * B) * OE z + (C * D) * OO z)) := by
          exact MeasureTheory.integral_add hT1 hRest
    _ = (A * B) * (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, EE z) +
        ((A * D) * (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, EO z) +
          ((C * B) * (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, OE z) +
            (C * D) * (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, OO z))) := by
          rw [hAddRest, hAdd34]
          simp only [MeasureTheory.integral_const_mul]
    _ = (A * B) * (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, EE z) := by
          rw [hEOzero, hOEzero, hOOzero]
          ring
    _ = (Real.cos ((a : ℝ) * chebyshevRootPhase n i) *
          Real.cos ((b : ℝ) * chebyshevRootPhase n j)) *
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          ellipticModeIntegrand ((a : ℝ) / (n : ℝ)) ((b : ℝ) / (n : ℝ)) z := by
          rfl

/-- The complete single-mode cell formula after reflection and ellipse scaling. This is Paper
Eq. (3.10)--(3.12) before the external Green/change-of-variables orientation sign is attached. -/
theorem integral_chebyshevCellMode_eq_weight_mul_area_mul_analyticKernel
    {n a b : ℕ} (i j : ℕ) {lambda h : ℝ}
    (ha_pos : 0 < a) (ha_lt : a < n) (hb_pos : 0 < b) (hb_lt : b < n)
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
      chebyshevCellModeIntegrand n i j a b z) =
      (Real.cos ((a : ℝ) * chebyshevRootPhase n i) *
        Real.cos ((b : ℝ) * chebyshevRootPhase n j)) *
        (2 * Real.pi * h / Real.sqrt lambda) *
          analyticKernel ((a : ℝ) / (n : ℝ)) ((b : ℝ) / (n : ℝ)) lambda h := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le ha_pos (Nat.le_of_lt ha_lt)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have ha_pos_real : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hb_pos_real : 0 < (b : ℝ) := by exact_mod_cast hb_pos
  have ha_lt_real : (a : ℝ) < (n : ℝ) := by exact_mod_cast ha_lt
  have hb_lt_real : (b : ℝ) < (n : ℝ) := by exact_mod_cast hb_lt
  have halpha_pos : 0 < (a : ℝ) / (n : ℝ) := div_pos ha_pos_real hn_pos
  have halpha_one : (a : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr ha_lt_real
  have hbeta_pos : 0 < (b : ℝ) / (n : ℝ) := div_pos hb_pos_real hn_pos
  have hbeta_one : (b : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr hb_lt_real
  rw [integral_chebyshevCellMode_eq_weight_mul_evenMode n i j a b hh hlambda,
    ellipticModeIntegral_eq_area_mul_analyticKernel
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda hh hhq]
  ring

end Hilbert16.Spikes
