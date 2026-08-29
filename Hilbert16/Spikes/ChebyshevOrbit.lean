import Hilbert16.Spikes.ChebyshevHamiltonian

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- Counterclockwise angular parametrization of the quadratic energy ellipse in `(u,v)`
coordinates. -/
noncomputable def ellipticOrbitUV (lambda h t : ℝ) : ℝ × ℝ :=
  (Real.sqrt (2 * h) * Real.cos t,
    Real.sqrt (2 * h) / Real.sqrt lambda * Real.sin t)

/-- Its angular velocity. -/
noncomputable def ellipticOrbitUVVelocity (lambda h t : ℝ) : ℝ × ℝ :=
  (-Real.sqrt (2 * h) * Real.sin t,
    Real.sqrt (2 * h) / Real.sqrt lambda * Real.cos t)

theorem ellipticOrbitUV_hasDerivAt
    {lambda h t : ℝ} :
    HasDerivAt (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h t) t := by
  apply HasDerivAt.prodMk
  · simpa [ellipticOrbitUV, ellipticOrbitUVVelocity] using
      (Real.hasDerivAt_cos t).const_mul (Real.sqrt (2 * h))
  · simpa [ellipticOrbitUV, ellipticOrbitUVVelocity] using
      (Real.hasDerivAt_sin t).const_mul (Real.sqrt (2 * h) / Real.sqrt lambda)

theorem ellipticOrbitUV_energy_eq
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h) :
    (ellipticOrbitUV lambda h t).1 ^ 2 +
        lambda * (ellipticOrbitUV lambda h t).2 ^ 2 = 2 * h := by
  have hsqrtLambda : Real.sqrt lambda ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hsqrtH : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  unfold ellipticOrbitUV
  dsimp
  simp only [mul_pow, div_pow, hsqrtH, hsqrtLambda]
  field_simp [hlambda.ne']
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem ellipticOrbitUV_abs_le_one
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    |(ellipticOrbitUV lambda h t).1| ≤ 1 ∧
      |(ellipticOrbitUV lambda h t).2| ≤ 1 := by
  have henergy := ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
  have huNonneg : 0 ≤ (ellipticOrbitUV lambda h t).1 ^ 2 := sq_nonneg _
  have hvNonneg : 0 ≤ (ellipticOrbitUV lambda h t).2 ^ 2 := sq_nonneg _
  have huSq : (ellipticOrbitUV lambda h t).1 ^ 2 ≤ 1 := by
    have hlv : 0 ≤ lambda * (ellipticOrbitUV lambda h t).2 ^ 2 :=
      mul_nonneg (le_trans zero_le_one hlambda) hvNonneg
    nlinarith
  have hvSq : (ellipticOrbitUV lambda h t).2 ^ 2 ≤ 1 := by
    have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hlambda) hvNonneg
    nlinarith
  exact ⟨(sq_le_one_iff_abs_le_one _).mp huSq, (sq_le_one_iff_abs_le_one _).mp hvSq⟩

theorem ellipticOrbitUV_add_two_pi (lambda h t : ℝ) :
    ellipticOrbitUV lambda h (t + 2 * Real.pi) = ellipticOrbitUV lambda h t := by
  ext <;> simp [ellipticOrbitUV]

/-- The explicit closed curve in a chosen Chebyshev cell. -/
noncomputable def chebyshevCellOrbit
    (n i j : ℕ) (lambda h t : ℝ) : ℝ × ℝ :=
  chebyshevCellInverseMap n i j (ellipticOrbitUV lambda h t)

/-- The angular velocity of the explicit cell orbit, obtained by differentiating both inverse
branches. -/
noncomputable def chebyshevCellOrbitVelocity
    (n i j : ℕ) (lambda h t : ℝ) : ℝ × ℝ :=
  (deriv (chebyshevInverseBranch n i) (ellipticOrbitUV lambda h t).1 *
      (ellipticOrbitUVVelocity lambda h t).1,
    deriv (chebyshevInverseBranch n j) (ellipticOrbitUV lambda h t).2 *
      (ellipticOrbitUVVelocity lambda h t).2)

theorem chebyshevCellOrbit_energy_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    chebyshevHamiltonian n lambda (chebyshevCellOrbit n i j lambda h t) = h := by
  have habs := ellipticOrbitUV_abs_le_one hlambda hh hhHalf (t := t)
  rw [show chebyshevCellOrbit n i j lambda h t =
      chebyshevCellInverseMap n i j (ellipticOrbitUV lambda h t) by rfl,
    chebyshevHamiltonian_inverseMap_eq hn habs.1 habs.2]
  rw [ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh]
  ring

theorem chebyshevCellOrbit_add_two_pi
    (n i j : ℕ) (lambda h t : ℝ) :
    chebyshevCellOrbit n i j lambda h (t + 2 * Real.pi) =
      chebyshevCellOrbit n i j lambda h t := by
  simp [chebyshevCellOrbit, ellipticOrbitUV_add_two_pi]

@[simp] theorem chebyshevCellOrbit_fst
    (n i j : ℕ) (lambda h t : ℝ) :
    (chebyshevCellOrbit n i j lambda h t).1 =
      chebyshevInverseBranch n i (ellipticOrbitUV lambda h t).1 := rfl

@[simp] theorem chebyshevCellOrbit_snd
    (n i j : ℕ) (lambda h t : ℝ) :
    (chebyshevCellOrbit n i j lambda h t).2 =
      chebyshevInverseBranch n j (ellipticOrbitUV lambda h t).2 := rfl

theorem chebyshevCellOrbit_fst_branch_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun s => chebyshevInverseBranch n i (ellipticOrbitUV lambda h s).1)
      (chebyshevCellOrbitVelocity n i j lambda h t).1 t := by
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  have huBranch := chebyshevInverseBranch_hasDerivAt (i := i) hn hstrict.1
  have huv := ellipticOrbitUV_hasDerivAt (lambda := lambda) (h := h) (t := t)
  have huComp := huBranch.comp t huv.fst
  rw [← huBranch.deriv] at huComp
  simpa only [chebyshevCellOrbitVelocity, Function.comp_def] using huComp

theorem chebyshevCellOrbit_snd_branch_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun s => chebyshevInverseBranch n j (ellipticOrbitUV lambda h s).2)
      (chebyshevCellOrbitVelocity n i j lambda h t).2 t := by
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  have hvBranch := chebyshevInverseBranch_hasDerivAt (i := j) hn hstrict.2
  have huv := ellipticOrbitUV_hasDerivAt (lambda := lambda) (h := h) (t := t)
  have hvComp := hvBranch.comp t huv.snd
  rw [← hvBranch.deriv] at hvComp
  simpa only [chebyshevCellOrbitVelocity, Function.comp_def] using hvComp

/-- The Hamiltonian vector field `(H_y,-H_x)`. -/
noncomputable def chebyshevHamiltonianVector
    (n : ℕ) (lambda : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (chebyshevHamiltonianDy n lambda z, -chebyshevHamiltonianDx n z)

/-- Exact time-orientation identity. The angular cell curve is the negative Hamiltonian vector
field after multiplication by `sqrt(lambda) T_n'(x) T_n'(y)`. Its sign is therefore the negative
of the cell Jacobian orientation, while the Hamiltonian flow itself is clockwise in the original
plane. -/
theorem chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    (Real.sqrt lambda *
        chebyshevForwardDerivative n (chebyshevCellOrbit n i j lambda h t).1 *
        chebyshevForwardDerivative n (chebyshevCellOrbit n i j lambda h t).2) •
      chebyshevCellOrbitVelocity n i j lambda h t =
        -chebyshevHamiltonianVector n lambda (chebyshevCellOrbit n i j lambda h t) := by
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  have hiInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := i) hn hstrict.1
  have hjInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := j) hn hstrict.2
  have hsqrtPos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)
  have hsqrtSq : Real.sqrt lambda ^ 2 = lambda :=
    Real.sq_sqrt (le_trans zero_le_one hlambda)
  have hiEval := eval_chebyshevInverseBranch hn hstrict.1.le (i := i)
  have hjEval := eval_chebyshevInverseBranch hn hstrict.2.le (i := j)
  have horbitFst : (chebyshevCellOrbit n i j lambda h t).1 =
      chebyshevInverseBranch n i (ellipticOrbitUV lambda h t).1 := rfl
  have horbitSnd : (chebyshevCellOrbit n i j lambda h t).2 =
      chebyshevInverseBranch n j (ellipticOrbitUV lambda h t).2 := rfl
  apply Prod.ext
  · simp only [Prod.smul_fst, Prod.fst_neg, chebyshevHamiltonianVector,
      chebyshevHamiltonianDy, chebyshevCellOrbitVelocity, ellipticOrbitUVVelocity]
    rw [horbitFst, horbitSnd, hjEval]
    change (Real.sqrt lambda * _ * _) * (_ * (-Real.sqrt (2 * h) * Real.sin t)) =
      -(lambda * (Real.sqrt (2 * h) / Real.sqrt lambda * Real.sin t) * _)
    calc
      _ = Real.sqrt lambda *
          (chebyshevForwardDerivative n (chebyshevInverseBranch n i
              (ellipticOrbitUV lambda h t).1) *
            deriv (chebyshevInverseBranch n i) (ellipticOrbitUV lambda h t).1) *
          chebyshevForwardDerivative n (chebyshevInverseBranch n j
            (ellipticOrbitUV lambda h t).2) *
          (-Real.sqrt (2 * h) * Real.sin t) := by ring
      _ = Real.sqrt lambda *
          chebyshevForwardDerivative n (chebyshevInverseBranch n j
            (ellipticOrbitUV lambda h t).2) *
          (-Real.sqrt (2 * h) * Real.sin t) := by rw [hiInv, mul_one]
      _ = -(lambda * (Real.sqrt (2 * h) / Real.sqrt lambda * Real.sin t) *
          chebyshevForwardDerivative n (chebyshevInverseBranch n j
            (ellipticOrbitUV lambda h t).2)) := by
        field_simp [hsqrtPos.ne']
        rw [hsqrtSq]
        ring
  · simp only [Prod.smul_snd, Prod.snd_neg, chebyshevHamiltonianVector,
      chebyshevHamiltonianDx, chebyshevCellOrbitVelocity, ellipticOrbitUVVelocity]
    rw [horbitFst, horbitSnd, hiEval]
    change (Real.sqrt lambda * _ * _) *
        (_ * (Real.sqrt (2 * h) / Real.sqrt lambda * Real.cos t)) =
      -(-(Real.sqrt (2 * h) * Real.cos t * _))
    calc
      _ = Real.sqrt lambda *
          chebyshevForwardDerivative n (chebyshevInverseBranch n i
            (ellipticOrbitUV lambda h t).1) *
          (chebyshevForwardDerivative n (chebyshevInverseBranch n j
              (ellipticOrbitUV lambda h t).2) *
            deriv (chebyshevInverseBranch n j) (ellipticOrbitUV lambda h t).2) *
          (Real.sqrt (2 * h) / Real.sqrt lambda * Real.cos t) := by ring
      _ = Real.sqrt lambda *
          chebyshevForwardDerivative n (chebyshevInverseBranch n i
            (ellipticOrbitUV lambda h t).1) *
          (Real.sqrt (2 * h) / Real.sqrt lambda * Real.cos t) := by rw [hjInv, mul_one]
      _ = -(-(Real.sqrt (2 * h) * Real.cos t *
          chebyshevForwardDerivative n (chebyshevInverseBranch n i
            (ellipticOrbitUV lambda h t).1))) := by
        field_simp [hsqrtPos.ne']

/-- The scalar multiplying the angular velocity has exactly the cell-Jacobian sign. Combined
with `chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector`, this makes the Hamiltonian-time
orientation the negative of the inverse-map orientation. -/
theorem chebyshevCellOrbit_timeFactor_orientation_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    0 < chebyshevCellJacobianOrientation i j *
      (Real.sqrt lambda *
        chebyshevForwardDerivative n (chebyshevCellOrbit n i j lambda h t).1 *
        chebyshevForwardDerivative n (chebyshevCellOrbit n i j lambda h t).2) := by
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  let fi := chebyshevForwardDerivative n
    (chebyshevInverseBranch n i (ellipticOrbitUV lambda h t).1)
  let fj := chebyshevForwardDerivative n
    (chebyshevInverseBranch n j (ellipticOrbitUV lambda h t).2)
  let di := deriv (chebyshevInverseBranch n i) (ellipticOrbitUV lambda h t).1
  let dj := deriv (chebyshevInverseBranch n j) (ellipticOrbitUV lambda h t).2
  let orientation := chebyshevCellJacobianOrientation i j
  have hiInv : fi * di = 1 := by
    exact chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := i) hn hstrict.1
  have hjInv : fj * dj = 1 := by
    exact chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := j) hn hstrict.2
  have hforwardInverse : (fi * fj) * (di * dj) = 1 := by
    calc
      (fi * fj) * (di * dj) = (fi * di) * (fj * dj) := by ring
      _ = 1 := by rw [hiInv, hjInv, one_mul]
  have horientationSq : orientation * orientation = 1 := by
    rcases chebyshevCellJacobianOrientation_mem i j with hneg | hpos
    · simp [orientation, hneg]
    · simp [orientation, hpos]
  have horientationInverse : 0 < orientation * (di * dj) := by
    exact chebyshevCellJacobianOrientation_mul_deriv_product_pos hn hn hi hj
      hstrict.1 hstrict.2
  have horientationForward : 0 < orientation * (fi * fj) := by
    have hproduct : (orientation * (fi * fj)) * (orientation * (di * dj)) = 1 := by
      calc
        _ = (orientation * orientation) * ((fi * fj) * (di * dj)) := by ring
        _ = 1 := by rw [horientationSq, hforwardInverse, one_mul]
    apply pos_of_mul_pos_left
    · rw [hproduct]
      norm_num
    · exact horientationInverse.le
  have hsqrtPos : 0 < Real.sqrt lambda :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)
  rw [chebyshevCellOrbit_fst, chebyshevCellOrbit_snd]
  change 0 < orientation * (Real.sqrt lambda * fi * fj)
  nlinarith [mul_pos hsqrtPos horientationForward]

end Hilbert16.Spikes
