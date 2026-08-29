import Hilbert16.Spikes.ChebyshevOrbitPdy
import Hilbert16.Spikes.EllipticSlice
import Hilbert16.Spikes.ChebyshevDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set MeasureTheory
open scoped Interval

/-- The canonical first-coordinate primitive of a continuous density is jointly continuous in
both physical coordinates. -/
theorem continuous_firstCoordinatePrimitive
    {q : ℝ × ℝ → ℝ} (hq : Continuous q) :
    Continuous (firstCoordinatePrimitive q) := by
  unfold firstCoordinatePrimitive
  let F : (ℝ × ℝ) → ℝ → ℝ := fun z x => q (x, z.2)
  have hF : Continuous F.uncurry := by
    unfold F Function.uncurry
    fun_prop
  simpa only [F] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ)) hF (s := fun z : ℝ × ℝ => z.1) continuous_fst)

theorem continuous_chebyshevDensityMode (n a b : ℕ) :
    Continuous (chebyshevDensityMode n a b) := by
  unfold chebyshevDensityMode chebyshevForwardDerivative
  fun_prop

theorem continuous_finiteChebyshevDensity
    (n : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ) :
    Continuous (finiteChebyshevDensity n support coeff) := by
  unfold finiteChebyshevDensity
  apply continuous_finsetSum support
  intro k hk
  exact continuous_const.mul (continuous_chebyshevDensityMode n k.1 k.2)

/-- The density after cancellation of both forward Chebyshev derivatives against the signed
inverse-branch derivatives. -/
noncomputable def finiteChebyshevPulledDensity
    (n i j : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (z : ℝ × ℝ) : ℝ :=
  ∑ k ∈ support, coeff k * chebyshevCellModeIntegrand n i j k.1 k.2 z

theorem continuous_chebyshevCellModeIntegrand (n i j a b : ℕ) :
    Continuous (chebyshevCellModeIntegrand n i j a b) := by
  unfold chebyshevCellModeIntegrand chebyshevInverseBranch
  fun_prop

theorem continuous_finiteChebyshevPulledDensity
    (n i j : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ) :
    Continuous (finiteChebyshevPulledDensity n i j support coeff) := by
  unfold finiteChebyshevPulledDensity
  apply continuous_finsetSum support
  intro k hk
  exact continuous_const.mul (continuous_chebyshevCellModeIntegrand n i j k.1 k.2)

/-- Pointwise signed-Jacobian cancellation before taking absolute values. -/
theorem chebyshevDensityMode_mul_inverseDerivs
    {n i j a b : ℕ} (hn : n ≠ 0) {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    chebyshevDensityMode n a b (chebyshevCellInverseMap n i j (u, v)) *
        deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch n j) v =
      chebyshevCellModeIntegrand n i j a b (u, v) := by
  have hiInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one
    (i := i) hn hu
  have hjInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one
    (i := j) hn hv
  change
    (chebyshevForwardDerivative n (chebyshevInverseBranch n i u) *
        chebyshevForwardDerivative n (chebyshevInverseBranch n j v) *
          ((Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i u) *
            (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval (chebyshevInverseBranch n j v))) *
      deriv (chebyshevInverseBranch n i) u *
      deriv (chebyshevInverseBranch n j) v = _
  calc
    _ = (chebyshevForwardDerivative n (chebyshevInverseBranch n i u) *
          deriv (chebyshevInverseBranch n i) u) *
        (chebyshevForwardDerivative n (chebyshevInverseBranch n j v) *
          deriv (chebyshevInverseBranch n j) v) *
        ((Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i u) *
          (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval (chebyshevInverseBranch n j v)) := by ring
    _ = chebyshevCellModeIntegrand n i j a b (u, v) := by
      rw [hiInv, hjInv]
      simp [chebyshevCellModeIntegrand]

theorem finiteChebyshevDensity_mul_inverseDerivs
    {n i j : ℕ} (hn : n ≠ 0)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    finiteChebyshevDensity n support coeff (chebyshevCellInverseMap n i j (u, v)) *
        deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch n j) v =
      finiteChebyshevPulledDensity n i j support coeff (u, v) := by
  unfold finiteChebyshevDensity finiteChebyshevPulledDensity
  calc
    (∑ k ∈ support, coeff k * chebyshevDensityMode n k.1 k.2
          (chebyshevCellInverseMap n i j (u, v))) *
          deriv (chebyshevInverseBranch n i) u *
          deriv (chebyshevInverseBranch n j) v =
        ∑ k ∈ support,
          coeff k *
            (chebyshevDensityMode n k.1 k.2 (chebyshevCellInverseMap n i j (u, v)) *
              deriv (chebyshevInverseBranch n i) u *
              deriv (chebyshevInverseBranch n j) v) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = ∑ k ∈ support, coeff k * chebyshevCellModeIntegrand n i j k.1 k.2 (u, v) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [chebyshevDensityMode_mul_inverseDerivs hn hu hv]

/-- The finite pulled density has exactly the analytic-kernel sum, without a cell-orientation
factor; that sign belongs to the Hamiltonian traversal of the physical cell. -/
theorem integral_finiteChebyshevPulledDensity_eq_kernel_sum
    {n i j : ℕ} (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (hfreq : ∀ k ∈ support, 0 < k.1 ∧ k.1 < n ∧ 0 < k.2 ∧ k.2 < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
      finiteChebyshevPulledDensity n i j support coeff z) =
      (2 * Real.pi * h / Real.sqrt lambda) *
        ∑ k ∈ support,
          coeff k *
            (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
              Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
            analyticKernel ((k.1 : ℝ) / (n : ℝ)) ((k.2 : ℝ) / (n : ℝ)) lambda h := by
  have hterms : ∀ k ∈ support,
      Integrable
        (fun z : ℝ × ℝ => coeff k * chebyshevCellModeIntegrand n i j k.1 k.2 z)
        (volume.restrict (ellipticEnergyDisk lambda h)) := by
    intro k hk
    exact continuous_integrableOn_ellipticEnergyDisk
      (continuous_const.mul (continuous_chebyshevCellModeIntegrand n i j k.1 k.2))
      lambda hh hlambda
  unfold finiteChebyshevPulledDensity
  rw [MeasureTheory.integral_finsetSum support hterms]
  calc
    (∑ k ∈ support,
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          coeff k * chebyshevCellModeIntegrand n i j k.1 k.2 z) =
      ∑ k ∈ support,
        coeff k *
          ((Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
              Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
            (2 * Real.pi * h / Real.sqrt lambda) *
              analyticKernel ((k.1 : ℝ) / (n : ℝ))
                ((k.2 : ℝ) / (n : ℝ)) lambda h) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [MeasureTheory.integral_const_mul,
        integral_chebyshevCellMode_eq_weight_mul_area_mul_analyticKernel
          i j (hfreq k hk).1 (hfreq k hk).2.1
            (hfreq k hk).2.2.1 (hfreq k hk).2.2.2 hlambda hh hhq]
    _ = (2 * Real.pi * h / Real.sqrt lambda) *
        ∑ k ∈ support,
          coeff k *
            (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
              Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
            analyticKernel ((k.1 : ℝ) / (n : ℝ))
              ((k.2 : ℝ) / (n : ℝ)) lambda h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Green's formula on the explicit Chebyshev cell orbit, with both inverse-branch derivatives
cancelled against the polynomial density. -/
theorem chebyshevCellAngularPdy_firstCoordinatePrimitive_finiteDensity_eq_integral
    {n i j : ℕ} (hn : n ≠ 0)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    chebyshevCellAngularPdy n i j
        (firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)) lambda h =
      ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        finiteChebyshevPulledDensity n i j support coeff z := by
  have hqcont := continuous_finiteChebyshevDensity n support coeff
  have hPcont := continuous_firstCoordinatePrimitive hqcont
  rw [chebyshevCellAngularPdy_eq_verticalBoundaryPdy hn hPcont hlambda hh
      (by linarith : h < 1 / 2),
    integral_ellipticEnergyDisk_eq_verticalSlices
      (continuous_finiteChebyshevPulledDensity n i j support coeff) hlambda hh]
  unfold ellipticVerticalBoundaryPdy verticalBoundaryPdy
  apply intervalIntegral.integral_congr
  intro v hv
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hBpos : 0 < ellipticVerticalRadius lambda h :=
    ellipticVerticalRadius_pos hlambdaPos hh
  rw [Set.uIcc_of_le (by linarith [hBpos])] at hv
  have hvAbsLe : |v| ≤ ellipticVerticalRadius lambda h := abs_le.mpr hv
  have hvAbs : |v| < 1 := lt_of_le_of_lt hvAbsLe
    (ellipticVerticalRadius_lt_one hlambda hh.le (by linarith : h < 1 / 2))
  have hvSqLe : v ^ 2 ≤ ellipticVerticalRadius lambda h ^ 2 := by
    have hprod : 0 ≤ (ellipticVerticalRadius lambda h - v) *
        (ellipticVerticalRadius lambda h + v) :=
      mul_nonneg (sub_nonneg.mpr hv.2) (by linarith [hv.1])
    nlinarith
  have hvEnergyLe : lambda * v ^ 2 ≤ 2 * h := by
    have hmul : 0 ≤ lambda *
        (ellipticVerticalRadius lambda h ^ 2 - v ^ 2) :=
      mul_nonneg hlambdaPos.le (sub_nonneg.mpr hvSqLe)
    nlinarith [ellipticVerticalRadius_energy hlambdaPos hh.le]
  let R := ellipticRightGraph lambda h v
  have hRnonneg : 0 ≤ R := by
    unfold R ellipticRightGraph
    positivity
  have hRsq : R ^ 2 = 2 * h - lambda * v ^ 2 := by
    exact ellipticRightGraph_sq hvEnergyLe
  have hRlt : R < 1 := by
    have hlvNonneg : 0 ≤ lambda * v ^ 2 :=
      mul_nonneg hlambdaPos.le (sq_nonneg v)
    nlinarith
  have hleft : ellipticLeftGraph lambda h v = -R := by
    rfl
  have hleftRight : ellipticLeftGraph lambda h v ≤ R := by
    rw [hleft]
    linarith
  have hbranchDeriv : ∀ u ∈ Set.uIcc (ellipticLeftGraph lambda h v) R,
      HasDerivAt (chebyshevInverseBranch n i)
        (deriv (chebyshevInverseBranch n i) u) u := by
    intro u hu
    rw [Set.uIcc_of_le hleftRight] at hu
    have huBounds : -R ≤ u ∧ u ≤ R := by
      change -R ≤ u ∧ u ≤ R at hu
      exact hu
    have huAbs : |u| < 1 :=
      lt_of_le_of_lt (abs_le.mpr huBounds) hRlt
    simpa only [(chebyshevInverseBranch_hasDerivAt (i := i) hn huAbs).deriv] using
      chebyshevInverseBranch_hasDerivAt (i := i) hn huAbs
  have hbranchDerivCont : ContinuousOn
      (fun u => deriv (chebyshevInverseBranch n i) u)
      (Set.uIcc (ellipticLeftGraph lambda h v) R) := by
    rw [Set.uIcc_of_le hleftRight, hleft]
    exact continuousOn_deriv_chebyshevInverseBranch hn hRlt
  have hg : Continuous (fun x : ℝ =>
      finiteChebyshevDensity n support coeff
        (x, chebyshevInverseBranch n j v)) := by
    exact hqcont.comp (continuous_id.prodMk continuous_const)
  have hsubst :
      (∫ u in ellipticLeftGraph lambda h v..R,
        finiteChebyshevDensity n support coeff
            (chebyshevInverseBranch n i u, chebyshevInverseBranch n j v) *
          deriv (chebyshevInverseBranch n i) u) =
        ∫ x in chebyshevInverseBranch n i (ellipticLeftGraph lambda h v)..
            chebyshevInverseBranch n i R,
          finiteChebyshevDensity n support coeff
            (x, chebyshevInverseBranch n j v) := by
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := ellipticLeftGraph lambda h v) (b := R)
        hbranchDeriv hbranchDerivCont hg)
  change
    firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)
          (chebyshevInverseBranch n i R, chebyshevInverseBranch n j v) *
        deriv (chebyshevInverseBranch n j) v -
      firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)
          (chebyshevInverseBranch n i (ellipticLeftGraph lambda h v),
            chebyshevInverseBranch n j v) *
        deriv (chebyshevInverseBranch n j) v =
      ∫ u in ellipticLeftGraph lambda h v..R,
        finiteChebyshevPulledDensity n i j support coeff (u, v)
  calc
    _ = (firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)
            (chebyshevInverseBranch n i R, chebyshevInverseBranch n j v) -
          firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)
            (chebyshevInverseBranch n i (ellipticLeftGraph lambda h v),
              chebyshevInverseBranch n j v)) *
        deriv (chebyshevInverseBranch n j) v := by ring
    _ = (∫ x in chebyshevInverseBranch n i (ellipticLeftGraph lambda h v)..
            chebyshevInverseBranch n i R,
          finiteChebyshevDensity n support coeff
            (x, chebyshevInverseBranch n j v)) *
        deriv (chebyshevInverseBranch n j) v := by
      rw [firstCoordinatePrimitive_sub_eq_integral hqcont]
    _ = (∫ u in ellipticLeftGraph lambda h v..R,
          finiteChebyshevDensity n support coeff
              (chebyshevInverseBranch n i u, chebyshevInverseBranch n j v) *
            deriv (chebyshevInverseBranch n i) u) *
        deriv (chebyshevInverseBranch n j) v := by rw [hsubst]
    _ = ∫ u in ellipticLeftGraph lambda h v..R,
          (finiteChebyshevDensity n support coeff
              (chebyshevInverseBranch n i u, chebyshevInverseBranch n j v) *
            deriv (chebyshevInverseBranch n i) u) *
          deriv (chebyshevInverseBranch n j) v := by
      rw [intervalIntegral.integral_mul_const]
    _ = ∫ u in ellipticLeftGraph lambda h v..R,
        finiteChebyshevPulledDensity n i j support coeff (u, v) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hleftRight] at hu
      have huBounds : -R ≤ u ∧ u ≤ R := by
        change -R ≤ u ∧ u ≤ R at hu
        exact hu
      have huAbs : |u| < 1 := lt_of_le_of_lt (abs_le.mpr huBounds) hRlt
      exact finiteChebyshevDensity_mul_inverseDerivs hn support coeff huAbs hvAbs

/-- The counterclockwise angular cell integral of the canonical primitive is the finite
analytic-kernel combination. -/
theorem chebyshevCellAngularPdy_firstCoordinatePrimitive_finiteDensity_eq_kernel_sum
    {n i j : ℕ} (hn : n ≠ 0)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (hfreq : ∀ k ∈ support, 0 < k.1 ∧ k.1 < n ∧ 0 < k.2 ∧ k.2 < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    chebyshevCellAngularPdy n i j
        (firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)) lambda h =
      (2 * Real.pi * h / Real.sqrt lambda) *
        ∑ k ∈ support,
          coeff k *
            (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
              Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
            analyticKernel ((k.1 : ℝ) / (n : ℝ)) ((k.2 : ℝ) / (n : ℝ)) lambda h := by
  rw [chebyshevCellAngularPdy_firstCoordinatePrimitive_finiteDensity_eq_integral
      hn support coeff hlambda hh hhq,
    integral_finiteChebyshevPulledDensity_eq_kernel_sum support coeff hfreq hlambda hh hhq]

/-- The same geometric `P dy` integral with the Hamiltonian-flow orientation. The factor
`-chebyshevCellJacobianOrientation i j` is forced by
`chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector` together with
`chebyshevCellOrbit_timeFactor_orientation_pos`. -/
noncomputable def chebyshevHamiltonianOrientedPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  -chebyshevCellJacobianOrientation i j *
    chebyshevCellAngularPdy n i j P lambda h

/-- First-order energy displacement `-∮ P dy` in Hamiltonian time orientation. -/
noncomputable def chebyshevFirstMelnikovDisplacement
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  -chebyshevHamiltonianOrientedPdy n i j P lambda h

theorem chebyshevFirstMelnikovDisplacement_eq_orientation_mul_angularPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) :
    chebyshevFirstMelnikovDisplacement n i j P lambda h =
      chebyshevCellJacobianOrientation i j *
        chebyshevCellAngularPdy n i j P lambda h := by
  unfold chebyshevFirstMelnikovDisplacement chebyshevHamiltonianOrientedPdy
  ring

/-- Complete one-cell first-Melnikov formula: the Hamiltonian orientation contributes exactly
the checkerboard cell sign, while the analytic part is the compiled finite kernel sum. -/
theorem chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum
    {n i j : ℕ} (hn : n ≠ 0)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (hfreq : ∀ k ∈ support, 0 < k.1 ∧ k.1 < n ∧ 0 < k.2 ∧ k.2 < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    chebyshevFirstMelnikovDisplacement n i j
        (firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)) lambda h =
      chebyshevCellJacobianOrientation i j *
        (2 * Real.pi * h / Real.sqrt lambda) *
          ∑ k ∈ support,
            coeff k *
              (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
                Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
              analyticKernel ((k.1 : ℝ) / (n : ℝ))
                ((k.2 : ℝ) / (n : ℝ)) lambda h := by
  rw [chebyshevFirstMelnikovDisplacement_eq_orientation_mul_angularPdy,
    chebyshevCellAngularPdy_firstCoordinatePrimitive_finiteDensity_eq_kernel_sum
      hn support coeff hfreq hlambda hh hhq]
  ring

/-- The Green/orbit construction agrees exactly with the independently compiled genuine
change-of-variables integral on the physical Chebyshev cell. -/
theorem chebyshevFirstMelnikovDisplacement_finiteDensity_eq_cellIntegral
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (hfreq : ∀ k ∈ support, 0 < k.1 ∧ k.1 < n ∧ 0 < k.2 ∧ k.2 < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    chebyshevFirstMelnikovDisplacement n i j
        (firstCoordinatePrimitive (finiteChebyshevDensity n support coeff)) lambda h =
      ∫ z : ℝ × ℝ in chebyshevCellEnergyRegion n i j lambda h,
        finiteChebyshevDensity n support coeff z := by
  rw [chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum
      hn support coeff hfreq hlambda hh hhq,
    integral_finiteChebyshevDensity_cell_eq_kernel_sum
      hn hi hj support coeff hfreq hlambda hh hhq]

end Hilbert16.Spikes
