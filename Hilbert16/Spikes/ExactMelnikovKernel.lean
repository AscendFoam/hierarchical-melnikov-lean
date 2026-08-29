import Hilbert16.Spikes.CosArcsin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Hilbert16.Spikes

open MeasureTheory Metric Real

/-- The Euclidean plane used after the ellipse-to-disk normalization in Paper Eq. (3.11). -/
abbrev KernelPlane := EuclideanSpace ℝ (Fin 2)

/--
The `p=q=0` case of the disk-moment calculation: the normalization domain has the standard
two-dimensional Euclidean volume.  The next B2 obligation is the general even-monomial moment.
-/
theorem diskMoment_zero (r : ℝ) :
    volume (ball (0 : KernelPlane) r) =
      ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
  exact EuclideanSpace.volume_ball_fin_two 0 r

/-- The radial factor in the polar-coordinate proof of Paper Eq. (3.11). -/
theorem radialEvenMoment (p q : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ ρ : ℝ in 0..Real.sqrt (2 * h), ρ ^ (2 * p + 2 * q + 1)) =
      (2 * h) ^ (p + q + 1) / (2 * (p + q + 1) : ℝ) := by
  rw [integral_pow]
  have hsqrt : (Real.sqrt (2 * h)) ^ 2 = 2 * h := by
    rw [sq_sqrt]
    positivity
  have hexponent : 2 * p + 2 * q + 1 + 1 = 2 * (p + q + 1) := by omega
  rw [hexponent, show (Real.sqrt (2 * h)) ^ (2 * (p + q + 1)) =
      ((Real.sqrt (2 * h)) ^ 2) ^ (p + q + 1) by rw [pow_mul], hsqrt]
  norm_num
  ring

/-- The finite Wallis product is the normalized half-integer rising factorial. -/
theorem halfPochhammer_div_factorial_eq_prod (m : ℕ) :
    (ascPochhammer ℝ m).eval (1 / 2) / (m.factorial : ℝ) =
      ∏ k ∈ Finset.range m, (2 * (k : ℝ) + 1) / (2 * k + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_natCast, Nat.factorial_succ,
        Finset.prod_range_succ, ← ih]
      push_cast
      have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hfac]
      ring

/-- The one-axis base case of the angular factor, rewritten in the paper's Pochhammer notation. -/
theorem quarterCosEvenMoment (q : ℕ) :
    (∫ θ : ℝ in 0..Real.pi / 2, Real.cos θ ^ (2 * q)) =
      Real.pi / 2 * (ascPochhammer ℝ q).eval (1 / 2) / (q.factorial : ℝ) := by
  rw [EulerSine.integral_cos_pow_eq, integral_sin_pow_even,
    ← halfPochhammer_div_factorial_eq_prod]
  ring

/-- The mixed even angular moment on the first quadrant. -/
noncomputable def quarterEvenAngularMoment (p q : ℕ) : ℝ :=
  ∫ θ : ℝ in 0..Real.pi / 2, Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q)

/-- Integration by parts relates the two ways of moving one quadratic factor. -/
theorem quarterEvenAngularMoment_cross (p q : ℕ) :
    (2 * q + 1 : ℝ) * quarterEvenAngularMoment (p + 1) q =
      (2 * p + 1 : ℝ) * quarterEvenAngularMoment p (q + 1) := by
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (Real.sin ^ (2 * p + 1))
        ((2 * p + 1 : ℝ) * Real.cos x * Real.sin x ^ (2 * p)) x := by
    intro x _
    simpa only [Pi.pow_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_sin x).pow (2 * p + 1)
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (-(Real.cos ^ (2 * q + 1)))
        ((2 * q + 1 : ℝ) * Real.sin x * Real.cos x ^ (2 * q)) x := by
    intro x _
    simpa only [Pi.pow_apply, Pi.neg_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Nat.add_sub_cancel, neg_mul, mul_neg, neg_neg, mul_assoc, mul_left_comm, mul_comm] using
        ((Real.hasDerivAt_cos x).pow (2 * q + 1)).neg
  have huInt : IntervalIntegrable
      (fun x : ℝ => (2 * p + 1 : ℝ) * Real.cos x * Real.sin x ^ (2 * p))
      volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hvInt : IntervalIntegrable
      (fun x : ℝ => (2 * q + 1 : ℝ) * Real.sin x * Real.cos x ^ (2 * q))
      volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    huInt hvInt
  simp [pow_succ] at H
  unfold quarterEvenAngularMoment
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  convert H using 1 <;>
    apply intervalIntegral.integral_congr <;> intro x _ <;>
      simp only [show 2 * (p + 1) = 2 * p + 2 by omega,
        show 2 * (q + 1) = 2 * q + 2 by omega, pow_add] <;> ring

/-- Splitting `1 = sin² + cos²` separates the two adjacent mixed moments. -/
theorem quarterEvenAngularMoment_split (p q : ℕ) :
    quarterEvenAngularMoment p q = quarterEvenAngularMoment (p + 1) q +
      quarterEvenAngularMoment p (q + 1) := by
  have h₁ : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (2 * (p + 1)) * Real.cos x ^ (2 * q))
      volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h₂ : IntervalIntegrable
      (fun x : ℝ => Real.sin x ^ (2 * p) * Real.cos x ^ (2 * (q + 1)))
      volume 0 (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold quarterEvenAngularMoment
  rw [← intervalIntegral.integral_add h₁ h₂]
  apply intervalIntegral.integral_congr
  intro x _
  change Real.sin x ^ (2 * p) * Real.cos x ^ (2 * q) =
    Real.sin x ^ (2 * p + 2) * Real.cos x ^ (2 * q) +
      Real.sin x ^ (2 * p) * Real.cos x ^ (2 * q + 2)
  rw [pow_add, pow_add]
  nth_rw 1 [← mul_one (Real.sin x ^ (2 * p) * Real.cos x ^ (2 * q))]
  rw [← Real.sin_sq_add_cos_sq x]
  ring

/-- The one-step beta-integral recurrence for a mixed even angular moment. -/
theorem quarterEvenAngularMoment_succ_left (p q : ℕ) :
    quarterEvenAngularMoment (p + 1) q =
      (2 * p + 1 : ℝ) / (2 * (p + q + 1)) * quarterEvenAngularMoment p q := by
  have hcross := quarterEvenAngularMoment_cross p q
  have hsplit := quarterEvenAngularMoment_split p q
  have hden : (2 * (p + q + 1) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  nlinarith

/-- The complete first-quadrant beta integral in the paper's Pochhammer normalization. -/
theorem quarterEvenAngularMoment_eq (p q : ℕ) :
    quarterEvenAngularMoment p q =
      Real.pi / 2 * (ascPochhammer ℝ p).eval (1 / 2) *
        (ascPochhammer ℝ q).eval (1 / 2) / ((p + q).factorial : ℝ) := by
  induction p with
  | zero =>
      simpa [quarterEvenAngularMoment] using quarterCosEvenMoment q
  | succ p ih =>
      rw [quarterEvenAngularMoment_succ_left, ih, ascPochhammer_succ_right,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast]
      have hfac : ((p + q).factorial : ℝ) ≠ 0 := by positivity
      have hsum : (p + 1 + q).factorial = (p + q + 1) * (p + q).factorial := by
        rw [show p + 1 + q = (p + q) + 1 by omega, Nat.factorial_succ]
      rw [hsum]
      push_cast
      field_simp [hfac]
      ring

/-- Four congruent quadrants give the angular factor used by polar coordinates. -/
theorem fullEvenAngularMoment_eq_four_quarters (p q : ℕ) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q)) =
        4 * quarterEvenAngularMoment p q := by
  let f : ℝ → ℝ := fun θ => Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hneg : (∫ θ : ℝ in -Real.pi..0, f θ) = ∫ θ : ℝ in 0..Real.pi, f θ := by
    have H := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Real.pi) f
    simpa [f, pow_mul] using H.symm
  have hupper : (∫ θ : ℝ in Real.pi / 2..Real.pi, f θ) =
      quarterEvenAngularMoment p q := by
    have H := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi / 2) f Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at H
    simpa [f, quarterEvenAngularMoment, Real.sin_pi_sub, Real.cos_pi_sub, pow_mul]
      using H.symm
  have hnegInt : IntervalIntegrable f volume (-Real.pi) 0 := hf.intervalIntegrable _ _
  have hposInt : IntervalIntegrable f volume 0 Real.pi := hf.intervalIntegrable _ _
  have hquarterInt : IntervalIntegrable f volume 0 (Real.pi / 2) :=
    hf.intervalIntegrable _ _
  have hupperInt : IntervalIntegrable f volume (Real.pi / 2) Real.pi :=
    hf.intervalIntegrable _ _
  have hquarter : (∫ θ : ℝ in 0..Real.pi / 2, f θ) =
      quarterEvenAngularMoment p q := by
    rfl
  change (∫ θ : ℝ in -Real.pi..Real.pi, f θ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hnegInt hposInt,
    hneg, ← intervalIntegral.integral_add_adjacent_intervals hquarterInt hupperInt,
    hquarter, hupper]
  ring

/-- The full angular beta integral on the polar-coordinate target `(-π, π)`. -/
theorem fullEvenAngularMoment_eq (p q : ℕ) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q)) =
        2 * Real.pi * (ascPochhammer ℝ p).eval (1 / 2) *
          (ascPochhammer ℝ q).eval (1 / 2) / ((p + q).factorial : ℝ) := by
  rw [fullEvenAngularMoment_eq_four_quarters, quarterEvenAngularMoment_eq]
  ring

/-- The separated polar-coordinate moment on the disk of squared radius `2h`. -/
theorem polarEvenMonomialMoment (p q : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z : ℝ × ℝ in
      Set.Ioo (0 : ℝ) (Real.sqrt (2 * h)) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      z.1 ^ (2 * p + 2 * q + 1) *
        (Real.sin z.2 ^ (2 * p) * Real.cos z.2 ^ (2 * q))) =
      Real.pi * (ascPochhammer ℝ p).eval (1 / 2) *
        (ascPochhammer ℝ q).eval (1 / 2) * (2 * h) ^ (p + q + 1) /
          ((p + q + 1).factorial : ℝ) := by
  have hsqrt : 0 ≤ Real.sqrt (2 * h) := Real.sqrt_nonneg _
  have hradial := radialEvenMoment p q hh
  rw [intervalIntegral.integral_of_le hsqrt, integral_Ioc_eq_integral_Ioo] at hradial
  have hangle := fullEvenAngularMoment_eq p q
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hpi,
    integral_Ioc_eq_integral_Ioo] at hangle
  calc
    _ = (∫ r : ℝ in Set.Ioo (0 : ℝ) (Real.sqrt (2 * h)),
          r ^ (2 * p + 2 * q + 1)) *
        (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q)) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod_mul (μ := volume) (ν := volume) (L := ℝ)
        (fun r : ℝ => r ^ (2 * p + 2 * q + 1))
        (fun θ : ℝ => Real.sin θ ^ (2 * p) * Real.cos θ ^ (2 * q))
        (Set.Ioo (0 : ℝ) (Real.sqrt (2 * h))) (Set.Ioo (-Real.pi) Real.pi)
    _ = _ := by
      rw [hradial, hangle]
      have hfac : ((p + q).factorial : ℝ) ≠ 0 := by positivity
      rw [show (p + q + 1).factorial = (p + q + 1) * (p + q).factorial by
        rw [Nat.factorial_succ]]
      push_cast
      field_simp [hfac]

/-- The Cartesian disk `x² + y² < 2h` occurring after the ellipse normalization. -/
def cartesianEnergyDisk (h : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 < 2 * h}

theorem measurableSet_cartesianEnergyDisk (h : ℝ) :
    MeasurableSet (cartesianEnergyDisk h) := by
  apply measurableSet_lt
  · fun_prop
  · fun_prop

/-- On the positive-radius polar target, the Cartesian disk condition is exactly `r < √(2h)`. -/
theorem polarCoord_symm_mem_cartesianEnergyDisk_iff {z : ℝ × ℝ} {h : ℝ}
    (hz : z ∈ polarCoord.target) :
    polarCoord.symm z ∈ cartesianEnergyDisk h ↔ z.1 < Real.sqrt (2 * h) := by
  have hzpos : 0 < z.1 := by
    simpa only [polarCoord_target, Set.mem_prod, Set.mem_Ioi] using hz.1
  rw [cartesianEnergyDisk, Set.mem_ofPred_eq, polarCoord_symm_apply]
  have hradius : (z.1 * Real.cos z.2) ^ 2 + (z.1 * Real.sin z.2) ^ 2 = z.1 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq z.2]
  rw [hradius]
  exact (Real.lt_sqrt hzpos.le).symm

/-- The even Cartesian monomial moment over `x² + y² < 2h`. -/
noncomputable def cartesianEvenMonomialMoment (p q : ℕ) (h : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in cartesianEnergyDisk h, z.2 ^ (2 * p) * z.1 ^ (2 * q)

/--
Paper Eq. (3.11): the exact Cartesian disk moment, proved through Mathlib's polar-coordinate
change-of-variables theorem rather than postulated as a coefficient identity.
-/
theorem cartesianEvenMonomialMoment_eq (p q : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    cartesianEvenMonomialMoment p q h =
      Real.pi * (ascPochhammer ℝ p).eval (1 / 2) *
        (ascPochhammer ℝ q).eval (1 / 2) * (2 * h) ^ (p + q + 1) /
          ((p + q + 1).factorial : ℝ) := by
  classical
  let g : ℝ × ℝ → ℝ := fun z => z.2 ^ (2 * p) * z.1 ^ (2 * q)
  let F : ℝ × ℝ → ℝ := fun z =>
    z.1 • (cartesianEnergyDisk h).indicator g (polarCoord.symm z)
  let rectangle : Set (ℝ × ℝ) :=
    Set.Ioo (0 : ℝ) (Real.sqrt (2 * h)) ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hrectangle : rectangle ⊆ polarCoord.target := by
    intro z hz
    rw [polarCoord_target]
    exact ⟨hz.1.1, hz.2⟩
  have hzero : ∀ z ∈ polarCoord.target \ rectangle, F z = 0 := by
    intro z hz
    have htarget := hz.1
    have hzparts : z.1 ∈ Set.Ioi (0 : ℝ) ∧ z.2 ∈ Set.Ioo (-Real.pi) Real.pi := by
      simpa only [polarCoord_target, Set.mem_prod] using htarget
    have hnotlt : ¬z.1 < Real.sqrt (2 * h) := by
      intro hlt
      exact hz.2 ⟨⟨hzparts.1, hlt⟩, hzparts.2⟩
    have hnotdisk : polarCoord.symm z ∉ cartesianEnergyDisk h := by
      rw [polarCoord_symm_mem_cartesianEnergyDisk_iff htarget]
      exact hnotlt
    simp only [F]
    rw [Set.indicator_apply, if_neg hnotdisk, smul_zero]
  have hpolarRestrict :
      (∫ z : ℝ × ℝ in polarCoord.target, F z) = ∫ z : ℝ × ℝ in rectangle, F z := by
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero polarCoord.open_target.measurableSet
      hrectangle hzero
  have hpointwise : ∀ z ∈ rectangle,
      F z = z.1 ^ (2 * p + 2 * q + 1) *
        (Real.sin z.2 ^ (2 * p) * Real.cos z.2 ^ (2 * q)) := by
    intro z hz
    have htarget : z ∈ polarCoord.target := hrectangle hz
    have hmem : polarCoord.symm z ∈ cartesianEnergyDisk h := by
      rw [polarCoord_symm_mem_cartesianEnergyDisk_iff htarget]
      exact hz.1.2
    simp only [F]
    rw [Set.indicator_apply, if_pos hmem]
    simp only [g, polarCoord_symm_apply, smul_eq_mul, mul_pow]
    rw [show 2 * p + 2 * q + 1 = 1 + 2 * p + 2 * q by omega, pow_add, pow_add]
    ring
  calc
    cartesianEvenMonomialMoment p q h =
        ∫ z : ℝ × ℝ, (cartesianEnergyDisk h).indicator g z := by
      rw [cartesianEvenMonomialMoment, integral_indicator (measurableSet_cartesianEnergyDisk h)]
    _ = ∫ z : ℝ × ℝ in polarCoord.target, F z := by
      exact (integral_comp_polarCoord_symm
        ((cartesianEnergyDisk h).indicator g)).symm
    _ = ∫ z : ℝ × ℝ in rectangle, F z := hpolarRestrict
    _ = ∫ z : ℝ × ℝ in rectangle,
        z.1 ^ (2 * p + 2 * q + 1) *
          (Real.sin z.2 ^ (2 * p) * Real.cos z.2 ^ (2 * q)) := by
      exact setIntegral_congr_fun (by
        exact measurableSet_Ioo.prod measurableSet_Ioo) hpointwise
    _ = _ := polarEvenMonomialMoment p q hh

/-- Each normalized Taylor monomial integrates to the corresponding term of Eq. (3.12). -/
theorem normalizedModeMonomialIntegral (alpha beta lambda : ℝ) (p q : ℕ)
    {h : ℝ} (hh : 0 < h) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta q * (lambda⁻¹) ^ q) *
        (z.2 ^ (2 * p) * z.1 ^ (2 * q))) / (2 * Real.pi * h) =
      (2 * h) ^ (p + q) / ((p + q + 1).factorial : ℝ) *
        formalTwoFZeroCoefficient alpha p * formalTwoFZeroCoefficient beta q *
          (lambda⁻¹) ^ q := by
  rw [MeasureTheory.integral_const_mul]
  change (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta q * (lambda⁻¹) ^ q) *
      cartesianEvenMonomialMoment p q h / (2 * Real.pi * h) = _
  rw [cartesianEvenMonomialMoment_eq p q hh.le,
    cosArcsinCoefficient_eq, cosArcsinCoefficient_eq]
  have hp : (ascPochhammer ℝ p).eval (1 / 2 : ℝ) ≠ 0 :=
    (ascPochhammer_pos p (1 / 2 : ℝ) (by norm_num)).ne'
  have hq : (ascPochhammer ℝ q).eval (1 / 2 : ℝ) ≠ 0 :=
    (ascPochhammer_pos q (1 / 2 : ℝ) (by norm_num)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfac : ((p + q + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hp, hq, hpi, hh.ne', hfac]
  ring

/-- The same monomial integral with the total Taylor degree factored as `h^(p+q)`. -/
theorem normalizedModeMonomialIntegral_eq_taylorTerm
    (alpha beta lambda : ℝ) (p q : ℕ) {h : ℝ} (hh : 0 < h) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta q * (lambda⁻¹) ^ q) *
        (z.2 ^ (2 * p) * z.1 ^ (2 * q))) / (2 * Real.pi * h) =
      (((2 : ℝ) ^ (p + q) / ((p + q + 1).factorial : ℝ)) *
        (formalTwoFZeroCoefficient alpha p * formalTwoFZeroCoefficient beta q *
          (lambda⁻¹) ^ q)) * h ^ (p + q) := by
  rw [normalizedModeMonomialIntegral alpha beta lambda p q hh, mul_pow]
  ring

/-- An even monomial has fixed sign after multiplication by a scalar, so its norm commutes
with integration over the energy disk. -/
theorem integral_norm_const_evenMonomial_eq_norm_integral
    (c : ℝ) (p q : ℕ) {h : ℝ} (_hh : 0 < h) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      ‖c * (z.2 ^ (2 * p) * z.1 ^ (2 * q))‖) =
      ‖∫ z : ℝ × ℝ in cartesianEnergyDisk h,
        c * (z.2 ^ (2 * p) * z.1 ^ (2 * q))‖ := by
  have hmono : ∀ z : ℝ × ℝ, 0 ≤ z.2 ^ (2 * p) * z.1 ^ (2 * q) := by
    intro z
    rw [pow_mul, pow_mul]
    positivity
  have hmoment : 0 ≤ cartesianEvenMonomialMoment p q h := by
    change 0 ≤ ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      z.2 ^ (2 * p) * z.1 ^ (2 * q)
    exact MeasureTheory.integral_nonneg (fun z => hmono z)
  have hnorm : ∀ z : ℝ × ℝ,
      ‖c * (z.2 ^ (2 * p) * z.1 ^ (2 * q))‖ =
        |c| * (z.2 ^ (2 * p) * z.1 ^ (2 * q)) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hmono z)]
  simp_rw [hnorm]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  change |c| * cartesianEvenMonomialMoment p q h =
    |c * cartesianEvenMonomialMoment p q h|
  rw [abs_mul, abs_of_nonneg hmoment]

theorem monomial_integrableOn_cartesianEnergyDisk (p q : ℕ) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun z : ℝ × ℝ => z.2 ^ (2 * p) * z.1 ^ (2 * q))
      (cartesianEnergyDisk h) := by
  let R := Real.sqrt (2 * h)
  let K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R
  have hsubset : cartesianEnergyDisk h ⊆ K := by
    intro z hz
    have hz' : z.1 ^ 2 + z.2 ^ 2 < 2 * h := hz
    have hx2 : z.1 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.2]
    have hy2 : z.2 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.1]
    have hxabs : |z.1| < R := by
      have hxR2 : z.1 ^ 2 < R ^ 2 := by
        dsimp [R]
        rwa [Real.sq_sqrt (by positivity)]
      have hRnonneg : 0 ≤ R := by exact Real.sqrt_nonneg _
      have hRabs : |R| = R := abs_of_nonneg hRnonneg
      simpa only [hRabs] using (sq_lt_sq.mp hxR2)
    have hyabs : |z.2| < R := by
      have hyR2 : z.2 ^ 2 < R ^ 2 := by
        dsimp [R]
        rwa [Real.sq_sqrt (by positivity)]
      have hRnonneg : 0 ≤ R := by exact Real.sqrt_nonneg _
      have hRabs : |R| = R := abs_of_nonneg hRnonneg
      simpa only [hRabs] using (sq_lt_sq.mp hyR2)
    exact ⟨⟨(abs_lt.mp hxabs).1.le, (abs_lt.mp hxabs).2.le⟩,
      ⟨(abs_lt.mp hyabs).1.le, (abs_lt.mp hyabs).2.le⟩⟩
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun z : ℝ × ℝ => z.2 ^ (2 * p) * z.1 ^ (2 * q)) := by
    fun_prop
  exact (hcont.continuousOn.integrableOn_compact hK).mono_set hsubset

/--
The normalized Taylor row from Paper Eq. (3.13), i.e. the coefficient of
`F_alpha(t) * F_beta(t / lambda)`.
-/
noncomputable def formalProductRow (alpha beta lambda : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (m + 1),
    formalTwoFZeroCoefficient alpha p *
      formalTwoFZeroCoefficient beta (m - p) * (lambda⁻¹) ^ (m - p)

@[simp]
theorem formalProductRow_zero (alpha beta lambda : ℝ) :
    formalProductRow alpha beta lambda 0 = 1 := by
  simp [formalProductRow]

theorem formalProductRow_one (alpha beta lambda : ℝ) (hlambda : lambda ≠ 0) :
    formalProductRow alpha beta lambda 1 =
      -(alpha ^ 2) / 4 - beta ^ 2 / (4 * lambda) := by
  simp [formalProductRow, Finset.sum_range_succ]
  field_simp
  ring

/-- The `m`-th antidiagonal polynomial in the product of the two cosine--arcsine series. -/
noncomputable def modeTaylorAntidiagonal
    (alpha beta lambda : ℝ) (m : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑ p ∈ Finset.range (m + 1),
    (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
      (lambda⁻¹) ^ (m - p)) *
        (z.2 ^ (2 * p) * z.1 ^ (2 * (m - p)))

theorem div_sqrt_even_pow {lambda x : ℝ} (hlambda : 0 < lambda) (q : ℕ) :
    (x / Real.sqrt lambda) ^ (2 * q) = (lambda⁻¹) ^ q * x ^ (2 * q) := by
  have hsquare : (Real.sqrt lambda) ^ 2 = lambda := Real.sq_sqrt hlambda.le
  rw [pow_mul, div_pow, hsquare, div_eq_mul_inv, mul_pow]
  ring

/-- The antidiagonal series is the pointwise product of the two cosine--arcsine modes. -/
theorem modeTaylorAntidiagonal_hasSum
    {alpha beta lambda : ℝ} (z : ℝ × ℝ)
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 0 < lambda)
    (hz2 : |z.2| < 1) (hz1 : |z.1 / Real.sqrt lambda| < 1) :
    HasSum (fun m => modeTaylorAntidiagonal alpha beta lambda m z)
      (Real.cos (alpha * Real.arcsin z.2) *
        Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) := by
  let f : ℕ → ℝ := fun p => cosArcsinCoefficient alpha p * z.2 ^ (2 * p)
  let g : ℕ → ℝ := fun q =>
    cosArcsinCoefficient beta q * (z.1 / Real.sqrt lambda) ^ (2 * q)
  have hfa : HasSum f (Real.cos (alpha * Real.arcsin z.2)) := by
    simpa only [f] using cos_mul_arcsin_hasSum halpha_pos halpha_one hz2
  have hga : HasSum g (Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) := by
    simpa only [g] using cos_mul_arcsin_hasSum hbeta_pos hbeta_one hz1
  have hfnorm : Summable (fun p => ‖f p‖) := by
    simpa only [f] using summable_norm_cosArcsinCoefficient halpha_pos halpha_one hz2
  have hgnorm : Summable (fun q => ‖g q‖) := by
    simpa only [g] using summable_norm_cosArcsinCoefficient hbeta_pos hbeta_one hz1
  have hf : Summable f := summable_norm_iff.mp hfnorm
  have hg : Summable g := summable_norm_iff.mp hgnorm
  have hprodNorm : Summable (fun pq : ℕ × ℕ => ‖f pq.1‖ * ‖g pq.2‖) :=
    hfnorm.mul_of_nonneg hgnorm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hprod : Summable (fun pq : ℕ × ℕ => f pq.1 * g pq.2) :=
    summable_norm_iff.mp (by simpa only [norm_mul] using hprodNorm)
  have hrow : Summable (fun m =>
      ∑ p ∈ Finset.range (m + 1), f p * g (m - p)) :=
    summable_sum_mul_range_of_summable_mul hprod
  have hsum := hrow.hasSum
  rw [← hf.tsum_mul_tsum_eq_tsum_sum_range hg hprod, hfa.tsum_eq, hga.tsum_eq] at hsum
  refine HasSum.congr_fun hsum ?_
  intro m
  change modeTaylorAntidiagonal alpha beta lambda m z =
    (∑ p ∈ Finset.range (m + 1),
      (cosArcsinCoefficient alpha p * z.2 ^ (2 * p)) *
        (cosArcsinCoefficient beta (m - p) *
          (z.1 / Real.sqrt lambda) ^ (2 * (m - p))))
  unfold modeTaylorAntidiagonal
  apply Finset.sum_congr rfl
  intro p hp
  rw [div_sqrt_even_pow hlambda]
  ring

/-- On every sufficiently small energy disk, the antidiagonal series sums to the actual mode. -/
theorem modeTaylorAntidiagonal_hasSum_on_disk
    {alpha beta lambda h : ℝ} (z : ℝ × ℝ)
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) (hh : 2 * h < 1)
    (hz : z ∈ cartesianEnergyDisk h) :
    HasSum (fun m => modeTaylorAntidiagonal alpha beta lambda m z)
      (Real.cos (alpha * Real.arcsin z.2) *
        Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) := by
  have hz' : z.1 ^ 2 + z.2 ^ 2 < 2 * h := hz
  have hz1sq : z.1 ^ 2 < 1 := by nlinarith [sq_nonneg z.2]
  have hz2sq : z.2 ^ 2 < 1 := by nlinarith [sq_nonneg z.1]
  have hz1abs : |z.1| < 1 := (sq_lt_one_iff_abs_lt_one z.1).mp hz1sq
  have hz2abs : |z.2| < 1 := (sq_lt_one_iff_abs_lt_one z.2).mp hz2sq
  have hsqrt : 1 ≤ Real.sqrt lambda :=
    (Real.le_sqrt (by norm_num) (le_trans zero_le_one hlambda)).mpr (by simpa using hlambda)
  have hz1scaled : |z.1 / Real.sqrt lambda| < 1 := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_self (abs_nonneg z.1) hsqrt).trans_lt hz1abs
  exact modeTaylorAntidiagonal_hasSum z halpha_pos halpha_one hbeta_pos hbeta_one
    (lt_of_lt_of_le zero_lt_one hlambda) hz2abs hz1scaled

/-- Integrating one finite antidiagonal gives exactly the normalized Taylor row of Eq. (3.12). -/
theorem normalizedModeAntidiagonalIntegral
    (alpha beta lambda : ℝ) (m : ℕ) {h : ℝ} (hh : 0 < h) :
    (∫ z : ℝ × ℝ in cartesianEnergyDisk h,
      modeTaylorAntidiagonal alpha beta lambda m z) / (2 * Real.pi * h) =
      ((2 : ℝ) ^ m / ((m + 1).factorial : ℝ) *
        formalProductRow alpha beta lambda m) * h ^ m := by
  unfold modeTaylorAntidiagonal
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_div]
    unfold formalProductRow
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpm : p ≤ m := Finset.mem_range_succ_iff.mp hp
    rw [normalizedModeMonomialIntegral alpha beta lambda p (m - p) hh]
    rw [Nat.add_sub_of_le hpm]
    ring
  · intro p hp
    exact (monomial_integrableOn_cartesianEnergyDisk p (m - p) hh).const_mul
      (cosArcsinCoefficient alpha p * cosArcsinCoefficient beta (m - p) *
        (lambda⁻¹) ^ (m - p))
end Hilbert16.Spikes
