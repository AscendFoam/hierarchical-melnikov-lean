import Hilbert16.Spikes.ChebyshevMelnikov
import Hilbert16.Spikes.ChebyshevPeriodAnnulus

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- An affine angular clock which traverses the explicit Chebyshev oval in
the Hamiltonian orientation.  The checkerboard orientation determines
whether the original angular parametrization must be reversed. -/
noncomputable def chebyshevHamiltonianAngle (i j : ℕ) (t : ℝ) : ℝ :=
  Real.pi / 2 + chebyshevCellJacobianOrientation i j * Real.pi +
    (-chebyshevCellJacobianOrientation i j) * t

/-- The explicit cell oval with its angular clock oriented along the
Hamiltonian flow. -/
noncomputable def chebyshevHamiltonianAngularOrbit
    (n i j : ℕ) (lambda h t : ℝ) : ℝ × ℝ :=
  chebyshevCellOrbit n i j lambda h (chebyshevHamiltonianAngle i j t)

/-- Derivative of `chebyshevHamiltonianAngularOrbit` with respect to its
angular clock. -/
noncomputable def chebyshevHamiltonianAngularVelocity
    (n i j : ℕ) (lambda h t : ℝ) : ℝ × ℝ :=
  (-chebyshevCellJacobianOrientation i j) •
    chebyshevCellOrbitVelocity n i j lambda h
      (chebyshevHamiltonianAngle i j t)

theorem chebyshevHamiltonianAngle_hasDerivAt (i j : ℕ) (t : ℝ) :
    HasDerivAt (chebyshevHamiltonianAngle i j)
      (-chebyshevCellJacobianOrientation i j) t := by
  unfold chebyshevHamiltonianAngle
  simpa using
    ((hasDerivAt_id t).const_mul (-chebyshevCellJacobianOrientation i j)).const_add
      (Real.pi / 2 + chebyshevCellJacobianOrientation i j * Real.pi)

theorem chebyshevHamiltonianAngularOrbit_fst_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    HasDerivAt
      (fun s => (chebyshevHamiltonianAngularOrbit n i j lambda h s).1)
      (chebyshevHamiltonianAngularVelocity n i j lambda h t).1 t := by
  have horbit := chebyshevCellOrbit_fst_branch_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf
    (t := chebyshevHamiltonianAngle i j t)
  have hcomp := horbit.comp t (chebyshevHamiltonianAngle_hasDerivAt i j t)
  simpa [chebyshevHamiltonianAngularOrbit,
    chebyshevHamiltonianAngularVelocity, Function.comp_def,
    Prod.smul_fst, mul_comm] using hcomp

theorem chebyshevHamiltonianAngularOrbit_snd_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    HasDerivAt
      (fun s => (chebyshevHamiltonianAngularOrbit n i j lambda h s).2)
      (chebyshevHamiltonianAngularVelocity n i j lambda h t).2 t := by
  have horbit := chebyshevCellOrbit_snd_branch_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf
    (t := chebyshevHamiltonianAngle i j t)
  have hcomp := horbit.comp t (chebyshevHamiltonianAngle_hasDerivAt i j t)
  simpa [chebyshevHamiltonianAngularOrbit,
    chebyshevHamiltonianAngularVelocity, Function.comp_def,
    Prod.smul_snd, mul_comm] using hcomp

/-- The angular Hamiltonian traversal has the same geometric tangent as the
physical Hamiltonian vector, with a strictly positive scalar time factor. -/
theorem chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    (chebyshevCellJacobianOrientation i j *
        (Real.sqrt lambda *
          chebyshevForwardDerivative n
            (chebyshevHamiltonianAngularOrbit n i j lambda h t).1 *
          chebyshevForwardDerivative n
            (chebyshevHamiltonianAngularOrbit n i j lambda h t).2)) •
      chebyshevHamiltonianAngularVelocity n i j lambda h t =
        chebyshevHamiltonianVector n lambda
          (chebyshevHamiltonianAngularOrbit n i j lambda h t) := by
  let o := chebyshevCellJacobianOrientation i j
  let factor := Real.sqrt lambda *
    chebyshevForwardDerivative n
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).1 *
    chebyshevForwardDerivative n
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).2
  have hbase := chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector
    (i := i) (j := j) hn hlambda hh hhHalf
    (t := chebyshevHamiltonianAngle i j t)
  have hoSq : o * o = 1 := by
    rcases chebyshevCellJacobianOrientation_mem i j with ho | ho <;>
      simp [o, ho]
  change (o * factor) • ((-o) •
      chebyshevCellOrbitVelocity n i j lambda h
        (chebyshevHamiltonianAngle i j t)) = _
  rw [smul_smul]
  have hscalar : (o * factor) * -o = -factor := by
    calc
      (o * factor) * -o = -(o * o) * factor := by ring
      _ = -factor := by rw [hoSq]; ring
  rw [hscalar]
  calc
    (-factor) • chebyshevCellOrbitVelocity n i j lambda h
        (chebyshevHamiltonianAngle i j t) =
        -(factor • chebyshevCellOrbitVelocity n i j lambda h
          (chebyshevHamiltonianAngle i j t)) := by simp
    _ = -(-chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianAngularOrbit n i j lambda h t)) := by
      simpa [factor, chebyshevHamiltonianAngularOrbit] using congrArg Neg.neg hbase
    _ = chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianAngularOrbit n i j lambda h t) := neg_neg _

theorem chebyshevHamiltonianAngular_timeFactor_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    0 < chebyshevCellJacobianOrientation i j *
      (Real.sqrt lambda *
        chebyshevForwardDerivative n
          (chebyshevHamiltonianAngularOrbit n i j lambda h t).1 *
        chebyshevForwardDerivative n
          (chebyshevHamiltonianAngularOrbit n i j lambda h t).2) := by
  exact chebyshevCellOrbit_timeFactor_orientation_pos hn hi hj
    hlambda hh hhHalf (t := chebyshevHamiltonianAngle i j t)

/-- The Hamiltonian-oriented angular traversal closes after exactly one
angular turn. -/
theorem chebyshevHamiltonianAngularOrbit_two_pi_eq_zero
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevHamiltonianAngularOrbit n i j lambda h (2 * Real.pi) =
      chebyshevHamiltonianAngularOrbit n i j lambda h 0 := by
  have hperiod := chebyshevCellOrbit_add_two_pi n i j lambda h
    (-(Real.pi / 2))
  rcases chebyshevCellJacobianOrientation_mem i j with ho | ho
  · rw [chebyshevHamiltonianAngularOrbit, chebyshevHamiltonianAngularOrbit,
      chebyshevHamiltonianAngle, chebyshevHamiltonianAngle, ho]
    convert hperiod using 1 <;> ring
  · rw [chebyshevHamiltonianAngularOrbit, chebyshevHamiltonianAngularOrbit,
      chebyshevHamiltonianAngle, chebyshevHamiltonianAngle, ho]
    convert hperiod.symm using 1 <;> ring

theorem chebyshevHamiltonianAngularOrbit_energy_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    chebyshevHamiltonian n lambda
      (chebyshevHamiltonianAngularOrbit n i j lambda h t) = h := by
  exact chebyshevCellOrbit_energy_eq hn hlambda hh hhHalf

theorem chebyshevHamiltonianAngularOrbit_mem_cellRectangle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhUpper : h < chebyshevCommonEnergyUpper) :
    chebyshevHamiltonianAngularOrbit n i j lambda h t ∈
      chebyshevCellRectangle n i j := by
  exact chebyshevCellOrbit_mem_cellRectangle hn hi hj hlambda hh hhUpper

theorem chebyshevHamiltonianAngularVelocity_ne_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianAngularVelocity n i j lambda h t ≠ 0 := by
  unfold chebyshevHamiltonianAngularVelocity
  exact smul_ne_zero
    (neg_ne_zero.mpr (chebyshevCellJacobianOrientation_ne_zero i j))
    (chebyshevCellOrbitVelocity_ne_zero hn hi hj hlambda hh hhHalf)

/-- The explicitly Hamiltonian-oriented one-turn `P dy` trace, split at the
two angular half-turns. -/
noncomputable def chebyshevHamiltonianAngularPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  parameterizedPdy P (chebyshevHamiltonianAngularOrbit n i j lambda h)
      (chebyshevHamiltonianAngularVelocity n i j lambda h) 0 Real.pi +
    parameterizedPdy P (chebyshevHamiltonianAngularOrbit n i j lambda h)
      (chebyshevHamiltonianAngularVelocity n i j lambda h)
      Real.pi (2 * Real.pi)

/-- The new Hamiltonian-oriented angular trace is exactly W4's previously
compiled orientation convention, for every integrand `P`. -/
theorem chebyshevHamiltonianAngularPdy_eq_hamiltonianOrientedPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) :
    chebyshevHamiltonianAngularPdy n i j P lambda h =
      chebyshevHamiltonianOrientedPdy n i j P lambda h := by
  unfold chebyshevHamiltonianAngularPdy
    chebyshevHamiltonianAngularOrbit chebyshevHamiltonianAngularVelocity
    chebyshevHamiltonianAngle
  rw [parameterizedPdy_comp_affine, parameterizedPdy_comp_affine]
  unfold chebyshevHamiltonianOrientedPdy chebyshevCellAngularPdy
  rcases chebyshevCellJacobianOrientation_mem i j with ho | ho
  · rw [ho]
    ring_nf
  · rw [ho]
    ring_nf
    have hright := parameterizedPdy_symm P
      (chebyshevCellOrbit n i j lambda h)
      (chebyshevCellOrbitVelocity n i j lambda h)
      (Real.pi * (1 / 2)) (Real.pi * (3 / 2))
    have hleft := parameterizedPdy_symm P
      (chebyshevCellOrbit n i j lambda h)
      (chebyshevCellOrbitVelocity n i j lambda h)
      (Real.pi * (-1 / 2)) (Real.pi * (1 / 2))
    rw [hright, hleft]
    ring

/-- Consequently the paper's first Melnikov displacement is the negative of
the concrete, Hamiltonian-oriented one-turn trace. -/
theorem chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianAngularPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) :
    chebyshevFirstMelnikovDisplacement n i j P lambda h =
      -chebyshevHamiltonianAngularPdy n i j P lambda h := by
  rw [chebyshevHamiltonianAngularPdy_eq_hamiltonianOrientedPdy]
  rfl

end Hilbert16.Spikes
