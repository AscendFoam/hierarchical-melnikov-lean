import Hilbert16.Spikes.ChebyshevCell
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

namespace Hilbert16.Spikes

open Filter Set
open scoped Topology

/-- Product of the two explicit inverse branches on one Chebyshev cell. -/
noncomputable def chebyshevCellInverseMap (n i j : ℕ) (z : ℝ × ℝ) : ℝ × ℝ :=
  Prod.map (chebyshevInverseBranch n i) (chebyshevInverseBranch n j) z

/-- Fréchet derivative of `chebyshevCellInverseMap`, expressed as a block product. -/
noncomputable def chebyshevCellInverseFDeriv (n i j : ℕ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (deriv (chebyshevInverseBranch n i) z.1)).prodMap
    (ContinuousLinearMap.toSpanSingleton ℝ
      (deriv (chebyshevInverseBranch n j) z.2))

/-- The original `(x,y)` region of a cell, defined as the image of the common elliptic energy
disk under its explicit product inverse branch. -/
def chebyshevCellEnergyRegion (n i j : ℕ) (lambda h : ℝ) : Set (ℝ × ℝ) :=
  chebyshevCellInverseMap n i j '' ellipticEnergyDisk lambda h

/-- The forward derivative `T_n'`, evaluated at a real point. -/
noncomputable def chebyshevForwardDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval x

/-- One original polynomial density mode, including the two forward Chebyshev derivatives whose
product cancels the absolute inverse Jacobian. -/
noncomputable def chebyshevDensityMode (n a b : ℕ) (z : ℝ × ℝ) : ℝ :=
  chebyshevForwardDerivative n z.1 * chebyshevForwardDerivative n z.2 *
    ((Polynomial.Chebyshev.T ℝ (a : ℤ)).eval z.1 *
      (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval z.2)

theorem chebyshevCellInverseFDeriv_det (n i j : ℕ) (z : ℝ × ℝ) :
    (chebyshevCellInverseFDeriv n i j z).det =
      deriv (chebyshevInverseBranch n i) z.1 *
        deriv (chebyshevInverseBranch n j) z.2 := by
  simp [chebyshevCellInverseFDeriv, ContinuousLinearMap.det, LinearMap.det_prodMap]

/-- Every point of the small elliptic disk lies in the open square on which both inverse branches
are differentiable and are genuine inverses. -/
theorem ellipticEnergyDisk_abs_lt_one
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hhq : h < 1 / 4)
    {z : ℝ × ℝ} (hz : z ∈ ellipticEnergyDisk lambda h) :
    |z.1| < 1 ∧ |z.2| < 1 := by
  have henergy : z.1 ^ 2 + lambda * z.2 ^ 2 < 2 * h := hz
  have huSq : z.1 ^ 2 < 1 := by
    have hnonneg : 0 ≤ lambda * z.2 ^ 2 :=
      mul_nonneg (le_trans (by norm_num) hlambda) (sq_nonneg z.2)
    nlinarith
  have hvSq : z.2 ^ 2 < 1 := by
    have hscale : 0 ≤ (lambda - 1) * z.2 ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg z.2)
    have huNonneg := sq_nonneg z.1
    nlinarith
  exact ⟨(sq_lt_one_iff_abs_lt_one z.1).mp huSq,
    (sq_lt_one_iff_abs_lt_one z.2).mp hvSq⟩

theorem chebyshevCellInverseMap_hasFDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {z : ℝ × ℝ}
    (hu : |z.1| < 1) (hv : |z.2| < 1) :
    HasFDerivAt (chebyshevCellInverseMap n i j)
      (chebyshevCellInverseFDeriv n i j z) z := by
  have hiD := chebyshevInverseBranch_hasDerivAt (i := i) hn hu
  have hjD := chebyshevInverseBranch_hasDerivAt (i := j) hn hv
  change HasFDerivAt
    (Prod.map (chebyshevInverseBranch n i) (chebyshevInverseBranch n j))
      (chebyshevCellInverseFDeriv n i j z) z
  simpa only [chebyshevCellInverseFDeriv, hiD.deriv, hjD.deriv] using
    hiD.hasFDerivAt.prodMap z hjD.hasFDerivAt

theorem chebyshevCellInverseMap_injOn_ellipticEnergyDisk
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hhq : h < 1 / 4) :
    Set.InjOn (chebyshevCellInverseMap n i j) (ellipticEnergyDisk lambda h) := by
  intro z hz w hw hzw
  have hzAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hz
  have hwAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hw
  apply Prod.ext
  · have hcoord : chebyshevInverseBranch n i z.1 = chebyshevInverseBranch n i w.1 :=
      congrArg Prod.fst hzw
    calc
      z.1 = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
          (chebyshevInverseBranch n i z.1) :=
        (eval_chebyshevInverseBranch hn (le_of_lt hzAbs.1)).symm
      _ = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
          (chebyshevInverseBranch n i w.1) :=
        congrArg (fun x : ℝ => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x) hcoord
      _ = w.1 := eval_chebyshevInverseBranch hn (le_of_lt hwAbs.1)
  · have hcoord : chebyshevInverseBranch n j z.2 = chebyshevInverseBranch n j w.2 :=
      congrArg Prod.snd hzw
    calc
      z.2 = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
          (chebyshevInverseBranch n j z.2) :=
        (eval_chebyshevInverseBranch hn (le_of_lt hzAbs.2)).symm
      _ = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
          (chebyshevInverseBranch n j w.2) :=
        congrArg (fun x : ℝ => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x) hcoord
      _ = w.2 := eval_chebyshevInverseBranch hn (le_of_lt hwAbs.2)

/-- Differentiating the local right-inverse identity gives exact cancellation between the forward
Chebyshev derivative and the derivative of its inverse branch. -/
theorem chebyshevForwardDerivative_mul_inverseDeriv_eq_one
    {n i : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : |u| < 1) :
    chebyshevForwardDerivative n (chebyshevInverseBranch n i u) *
      deriv (chebyshevInverseBranch n i) u = 1 := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  let branch := chebyshevInverseBranch n i
  have hb := chebyshevInverseBranch_hasDerivAt (i := i) hn hu
  have hcomp := (p.hasDerivAt (branch u)).comp u hb
  rw [← hb.deriv] at hcomp
  change HasDerivAt (fun t : ℝ => p.eval (branch t))
    (p.derivative.eval (branch u) * deriv branch u) u at hcomp
  have huIoo : u ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hu
  have heq : (fun t : ℝ => p.eval (branch t)) =ᶠ[nhds u] fun t => t := by
    filter_upwards [isOpen_Ioo.eventually_mem huIoo] with t ht
    exact eval_chebyshevInverseBranch hn (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  have hid : HasDerivAt (fun t : ℝ => t)
      (p.derivative.eval (branch u) * deriv branch u) u := by
    rw [← heq.hasDerivAt_iff]
    exact hcomp
  simpa only [chebyshevForwardDerivative, p, branch] using
    hid.unique (hasDerivAt_id u)

theorem abs_inverseDeriv_product_eq_cellOrientation_mul
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    |deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch n j) v| =
      chebyshevCellJacobianOrientation i j *
        (deriv (chebyshevInverseBranch n i) u *
          deriv (chebyshevInverseBranch n j) v) := by
  have horient := chebyshevCellJacobianOrientation_mul_deriv_product_pos
    hn hn hi hj hu hv
  rcases chebyshevCellJacobianOrientation_mem i j with hneg | hpos
  · rw [hneg, neg_one_mul] at horient ⊢
    have hprodNeg : deriv (chebyshevInverseBranch n i) u *
        deriv (chebyshevInverseBranch n j) v < 0 := by linarith
    exact abs_of_neg hprodNeg
  · rw [hpos, one_mul] at horient ⊢
    exact abs_of_pos horient

/-- Pointwise Jacobian cancellation for the original density mode. -/
theorem abs_det_inverseFDeriv_smul_densityMode
    {n i j a b : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {z : ℝ × ℝ} (hu : |z.1| < 1) (hv : |z.2| < 1) :
    |(chebyshevCellInverseFDeriv n i j z).det| •
        chebyshevDensityMode n a b (chebyshevCellInverseMap n i j z) =
      chebyshevCellJacobianOrientation i j *
        chebyshevCellModeIntegrand n i j a b z := by
  have hiInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := i) hn hu
  have hjInv := chebyshevForwardDerivative_mul_inverseDeriv_eq_one (i := j) hn hv
  rw [chebyshevCellInverseFDeriv_det,
    abs_inverseDeriv_product_eq_cellOrientation_mul hn hi hj hu hv]
  change chebyshevCellJacobianOrientation i j *
        (deriv (chebyshevInverseBranch n i) z.1 *
          deriv (chebyshevInverseBranch n j) z.2) *
      (chebyshevForwardDerivative n (chebyshevInverseBranch n i z.1) *
        chebyshevForwardDerivative n (chebyshevInverseBranch n j z.2) *
          ((Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i z.1) *
            (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval (chebyshevInverseBranch n j z.2))) = _
  calc
    _ = chebyshevCellJacobianOrientation i j *
        ((chebyshevForwardDerivative n (chebyshevInverseBranch n i z.1) *
            deriv (chebyshevInverseBranch n i) z.1) *
          (chebyshevForwardDerivative n (chebyshevInverseBranch n j z.2) *
            deriv (chebyshevInverseBranch n j) z.2)) *
        ((Polynomial.Chebyshev.T ℝ (a : ℤ)).eval (chebyshevInverseBranch n i z.1) *
          (Polynomial.Chebyshev.T ℝ (b : ℤ)).eval (chebyshevInverseBranch n j z.2)) := by ring
    _ = chebyshevCellJacobianOrientation i j *
        chebyshevCellModeIntegrand n i j a b z := by
      rw [hiInv, hjInv]
      simp [chebyshevCellModeIntegrand]

/-- Genuine set-integral change of variables from the original `(x,y)` Chebyshev cell to the
elliptic `(u,v)` disk. The two polynomial forward derivatives cancel the absolute inverse
Jacobian, leaving exactly the constant cell orientation. -/
theorem integral_chebyshevDensityMode_cell_eq_orientation_mul_pulledBack
    {n i j a b : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in chebyshevCellEnergyRegion n i j lambda h,
      chebyshevDensityMode n a b z) =
      chebyshevCellJacobianOrientation i j *
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          chebyshevCellModeIntegrand n i j a b z := by
  have hfderiv : ∀ z ∈ ellipticEnergyDisk lambda h,
      HasFDerivWithinAt (chebyshevCellInverseMap n i j)
        (chebyshevCellInverseFDeriv n i j z) (ellipticEnergyDisk lambda h) z := by
    intro z hz
    have hzAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hz
    exact (chebyshevCellInverseMap_hasFDerivAt hn hzAbs.1 hzAbs.2).hasFDerivWithinAt
  have hinj := chebyshevCellInverseMap_injOn_ellipticEnergyDisk hn hlambda hhq (i := i) (j := j)
  rw [show chebyshevCellEnergyRegion n i j lambda h =
      chebyshevCellInverseMap n i j '' ellipticEnergyDisk lambda h by rfl,
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      MeasureTheory.volume (measurableSet_ellipticEnergyDisk lambda h) hfderiv hinj]
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        |(chebyshevCellInverseFDeriv n i j z).det| •
          chebyshevDensityMode n a b (chebyshevCellInverseMap n i j z)) =
      ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        chebyshevCellJacobianOrientation i j *
          chebyshevCellModeIntegrand n i j a b z := by
      apply MeasureTheory.setIntegral_congr_fun (measurableSet_ellipticEnergyDisk lambda h)
      intro z hz
      have hzAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hz
      exact abs_det_inverseFDeriv_smul_densityMode hn hi hj hzAbs.1 hzAbs.2
    _ = chebyshevCellJacobianOrientation i j *
        ∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
          chebyshevCellModeIntegrand n i j a b z := by
      rw [MeasureTheory.integral_const_mul]

/-- Each original polynomial density mode is integrable on the curvilinear cell energy region.
The proof transports integrability through the same genuine Jacobian theorem used for the exact
integral identity. -/
theorem chebyshevDensityMode_integrableOn_cell
    {n i j a b : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    MeasureTheory.IntegrableOn (chebyshevDensityMode n a b)
      (chebyshevCellEnergyRegion n i j lambda h) := by
  have hfderiv : ∀ z ∈ ellipticEnergyDisk lambda h,
      HasFDerivWithinAt (chebyshevCellInverseMap n i j)
        (chebyshevCellInverseFDeriv n i j z) (ellipticEnergyDisk lambda h) z := by
    intro z hz
    have hzAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hz
    exact (chebyshevCellInverseMap_hasFDerivAt hn hzAbs.1 hzAbs.2).hasFDerivWithinAt
  have hinj := chebyshevCellInverseMap_injOn_ellipticEnergyDisk hn hlambda hhq (i := i) (j := j)
  rw [show chebyshevCellEnergyRegion n i j lambda h =
      chebyshevCellInverseMap n i j '' ellipticEnergyDisk lambda h by rfl,
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      MeasureTheory.volume (measurableSet_ellipticEnergyDisk lambda h) hfderiv hinj]
  have hmode : MeasureTheory.IntegrableOn
      (chebyshevCellModeIntegrand n i j a b) (ellipticEnergyDisk lambda h) :=
    continuous_integrableOn_ellipticEnergyDisk
      (by unfold chebyshevCellModeIntegrand chebyshevInverseBranch; fun_prop)
      lambda hh hlambda
  have hscaled : MeasureTheory.IntegrableOn
      (fun z => chebyshevCellJacobianOrientation i j *
        chebyshevCellModeIntegrand n i j a b z) (ellipticEnergyDisk lambda h) :=
    hmode.const_mul (chebyshevCellJacobianOrientation i j)
  apply MeasureTheory.IntegrableOn.congr_fun hscaled
  · intro z hz
    have hzAbs := ellipticEnergyDisk_abs_lt_one hlambda hhq hz
    exact (abs_det_inverseFDeriv_smul_densityMode hn hi hj hzAbs.1 hzAbs.2).symm
  · exact measurableSet_ellipticEnergyDisk lambda h

/-- The complete single-mode original-cell area formula. This closes the genuine Chebyshev
change-of-variables part of Paper Eq. (3.8)--(3.12); the external Green/orbit sign remains a
separate convention. -/
theorem integral_chebyshevDensityMode_cell_eq_orientation_mul_weight_mul_kernel
    {n a b i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ}
    (ha_pos : 0 < a) (ha_lt : a < n) (hb_pos : 0 < b) (hb_lt : b < n)
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in chebyshevCellEnergyRegion n i j lambda h,
      chebyshevDensityMode n a b z) =
      chebyshevCellJacobianOrientation i j *
        (Real.cos ((a : ℝ) * chebyshevRootPhase n i) *
          Real.cos ((b : ℝ) * chebyshevRootPhase n j)) *
        (2 * Real.pi * h / Real.sqrt lambda) *
          analyticKernel ((a : ℝ) / (n : ℝ)) ((b : ℝ) / (n : ℝ)) lambda h := by
  rw [integral_chebyshevDensityMode_cell_eq_orientation_mul_pulledBack
      hn hi hj hlambda hhq,
    integral_chebyshevCellMode_eq_weight_mul_area_mul_analyticKernel
      i j ha_pos ha_lt hb_pos hb_lt hlambda hh hhq]
  ring

end Hilbert16.Spikes
