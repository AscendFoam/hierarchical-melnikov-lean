import Hilbert16.Spikes.EllipticOrbitPdy

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set
open scoped Interval

/-- The explicit derivative formula for a Chebyshev inverse branch. -/
noncomputable def chebyshevInverseBranchDerivativeFormula (n i : ℕ) (v : ℝ) : ℝ :=
  (-chebyshevCellOrientation i) *
      Real.sin (chebyshevRootPhase n i +
        chebyshevCellOrientation i * Real.arcsin v / (n : ℝ)) /
    ((n : ℝ) * Real.sqrt (1 - v ^ 2))

theorem deriv_chebyshevInverseBranch_eq_formula
    {n i : ℕ} (hn : n ≠ 0) {v : ℝ} (hv : |v| < 1) :
    deriv (chebyshevInverseBranch n i) v =
      chebyshevInverseBranchDerivativeFormula n i v := by
  exact (chebyshevInverseBranch_hasDerivAt (i := i) hn hv).deriv

theorem continuousOn_deriv_chebyshevInverseBranch
    {n i : ℕ} (hn : n ≠ 0) {r : ℝ} (hr1 : r < 1) :
    ContinuousOn (fun v => deriv (chebyshevInverseBranch n i) v) (Set.Icc (-r) r) := by
  have hformula : ContinuousOn (chebyshevInverseBranchDerivativeFormula n i) (Set.Icc (-r) r) := by
    unfold chebyshevInverseBranchDerivativeFormula
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro v hv
      have hvAbsLe : |v| ≤ r := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
      have hvAbs : |v| < 1 := lt_of_le_of_lt hvAbsLe hr1
      have hvSq : v ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one v).2 hvAbs
      apply mul_ne_zero
      · exact_mod_cast hn
      · exact Real.sqrt_ne_zero'.mpr (by linarith)
  apply hformula.congr
  intro v hv
  have hvAbsLe : |v| ≤ r := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  have hvAbs : |v| < 1 := lt_of_le_of_lt hvAbsLe hr1
  exact deriv_chebyshevInverseBranch_eq_formula hn hvAbs

theorem continuous_chebyshevInverseBranch (n i : ℕ) :
    Continuous (chebyshevInverseBranch n i) := by
  unfold chebyshevInverseBranch
  fun_prop

/-- Pullback of the physical one-form coefficient `P(x,y) dy` to `(u,v)` coordinates. -/
noncomputable def chebyshevPulledPdyCoefficient
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  P (chebyshevCellInverseMap n i j z) * deriv (chebyshevInverseBranch n j) z.2

/-- The physical `P dy` integral along the explicit Chebyshev orbit, split into its two angular
half-arcs. -/
noncomputable def chebyshevCellAngularPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  parameterizedPdy P (chebyshevCellOrbit n i j lambda h)
      (chebyshevCellOrbitVelocity n i j lambda h)
      (-(Real.pi / 2)) (Real.pi / 2) +
    parameterizedPdy P (chebyshevCellOrbit n i j lambda h)
      (chebyshevCellOrbitVelocity n i j lambda h)
      (Real.pi / 2) (Real.pi + Real.pi / 2)

theorem chebyshevCellParameterizedPdy_eq_pulled
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h a b : ℝ) :
    parameterizedPdy P (chebyshevCellOrbit n i j lambda h)
        (chebyshevCellOrbitVelocity n i j lambda h) a b =
      parameterizedPdy (chebyshevPulledPdyCoefficient n i j P)
        (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h) a b := by
  unfold parameterizedPdy
  apply intervalIntegral.integral_congr
  intro t ht
  change P (chebyshevCellInverseMap n i j (ellipticOrbitUV lambda h t)) *
      (deriv (chebyshevInverseBranch n j) (ellipticOrbitUV lambda h t).2 *
        (ellipticOrbitUVVelocity lambda h t).2) =
    (P (chebyshevCellInverseMap n i j (ellipticOrbitUV lambda h t)) *
      deriv (chebyshevInverseBranch n j) (ellipticOrbitUV lambda h t).2) *
        (ellipticOrbitUVVelocity lambda h t).2
  ring

theorem chebyshevCellAngularPdy_eq_ellipticAngularPdy
    (n i j : ℕ) (P : ℝ × ℝ → ℝ) (lambda h : ℝ) :
    chebyshevCellAngularPdy n i j P lambda h =
      ellipticAngularPdy (chebyshevPulledPdyCoefficient n i j P) lambda h := by
  unfold chebyshevCellAngularPdy ellipticAngularPdy
  rw [chebyshevCellParameterizedPdy_eq_pulled,
    chebyshevCellParameterizedPdy_eq_pulled]

theorem continuousOn_chebyshevPulledPdyCoefficient_rightGraph
    {n i j : ℕ} (hn : n ≠ 0) {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    ContinuousOn
      (fun v => chebyshevPulledPdyCoefficient n i j P
        (ellipticRightGraph lambda h v, v))
      (Set.uIcc (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)) := by
  have hRadius : 0 ≤ ellipticVerticalRadius lambda h := by
    unfold ellipticVerticalRadius ellipticHorizontalRadius
    positivity
  rw [Set.uIcc_of_le (neg_le_self hRadius)]
  have hderiv := continuousOn_deriv_chebyshevInverseBranch (i := j) hn
    (ellipticVerticalRadius_lt_one hlambda hh hhHalf)
  have hmap : Continuous (fun v => chebyshevCellInverseMap n i j
      (ellipticRightGraph lambda h v, v)) := by
    change Continuous (fun v =>
      (chebyshevInverseBranch n i (ellipticRightGraph lambda h v),
        chebyshevInverseBranch n j v))
    exact ((continuous_chebyshevInverseBranch n i).comp
      (continuous_ellipticRightGraph lambda h)).prodMk
        (continuous_chebyshevInverseBranch n j)
  unfold chebyshevPulledPdyCoefficient
  exact (hP.comp hmap).continuousOn.mul hderiv

theorem continuousOn_chebyshevPulledPdyCoefficient_leftGraph
    {n i j : ℕ} (hn : n ≠ 0) {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    ContinuousOn
      (fun v => chebyshevPulledPdyCoefficient n i j P
        (ellipticLeftGraph lambda h v, v))
      (Set.uIcc (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)) := by
  have hRadius : 0 ≤ ellipticVerticalRadius lambda h := by
    unfold ellipticVerticalRadius ellipticHorizontalRadius
    positivity
  rw [Set.uIcc_of_le (neg_le_self hRadius)]
  have hderiv := continuousOn_deriv_chebyshevInverseBranch (i := j) hn
    (ellipticVerticalRadius_lt_one hlambda hh hhHalf)
  have hmap : Continuous (fun v => chebyshevCellInverseMap n i j
      (ellipticLeftGraph lambda h v, v)) := by
    change Continuous (fun v =>
      (chebyshevInverseBranch n i (ellipticLeftGraph lambda h v),
        chebyshevInverseBranch n j v))
    exact ((continuous_chebyshevInverseBranch n i).comp
      (continuous_ellipticLeftGraph lambda h)).prodMk
        (continuous_chebyshevInverseBranch n j)
  unfold chebyshevPulledPdyCoefficient
  exact (hP.comp hmap).continuousOn.mul hderiv

/-- The physical Chebyshev-orbit `P dy` integral is exactly the vertical two-graph functional of
the pulled one-form coefficient. -/
theorem chebyshevCellAngularPdy_eq_verticalBoundaryPdy
    {n i j : ℕ} (hn : n ≠ 0) {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhHalf : h < 1 / 2) :
    chebyshevCellAngularPdy n i j P lambda h =
      ellipticVerticalBoundaryPdy (chebyshevPulledPdyCoefficient n i j P) lambda h := by
  rw [chebyshevCellAngularPdy_eq_ellipticAngularPdy]
  apply ellipticAngularPdy_eq_verticalBoundaryPdy_of_continuousOn
    (lt_of_lt_of_le zero_lt_one hlambda) hh
  · exact continuousOn_chebyshevPulledPdyCoefficient_rightGraph hn hP hlambda hh.le hhHalf
  · exact continuousOn_chebyshevPulledPdyCoefficient_leftGraph hn hP hlambda hh.le hhHalf

end Hilbert16.Spikes
