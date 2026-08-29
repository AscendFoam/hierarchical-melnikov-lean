import Hilbert16.Foundations.PeriodicOrbit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option autoImplicit false

namespace Hilbert16

open Set

/-!
# An elementary angular cut for periodic planar curves

The stereographic angle below is single-valued off the positive horizontal
ray.  A periodic differentiable curve with a strictly oriented angular
cross product therefore has to meet that ray.  This is the topological
last mile needed by the local Poincare-section argument, proved using only
one-variable calculus.
-/

/-- The angle coordinate on the complement of the positive horizontal ray.
The formula is total in Lean; its derivative theorem is used only where its
denominator is strictly positive. -/
noncomputable def positiveRayAngle (u v : ℝ) : ℝ :=
  2 * Real.arctan (v / (Real.sqrt (u ^ 2 + v ^ 2) - u))

/-- Derivative of the stereographic angle.  The sign is opposite to the
usual angular cross product because the branch cut is the positive ray. -/
theorem positiveRayAngle_comp_hasDerivAt
    {u v : ℝ → ℝ} {du dv t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t)
    (hrad : 0 < u t ^ 2 + v t ^ 2)
    (hcut : ¬ (v t = 0 ∧ 0 < u t)) :
    HasDerivAt (fun s => positiveRayAngle (u s) (v s))
      (-(u t * dv - v t * du) / (u t ^ 2 + v t ^ 2)) t := by
  let q : ℝ → ℝ := u ^ 2 + v ^ 2
  let radius : ℝ → ℝ := fun s => Real.sqrt (q s)
  have hq : HasDerivAt q (2 * u t * du + 2 * v t * dv) t := by
    simpa [q, two_mul, mul_assoc] using (hu.pow 2).add (hv.pow 2)
  have hqt : q t = u t ^ 2 + v t ^ 2 := by rfl
  have hqne : q t ≠ 0 := by rw [hqt]; exact ne_of_gt hrad
  have hradius : HasDerivAt radius
      ((2 * u t * du + 2 * v t * dv) /
        (2 * Real.sqrt (u t ^ 2 + v t ^ 2))) t := by
    simpa [radius, hqt] using hq.sqrt hqne
  have hrpos : 0 < radius t := by
    simp only [radius, hqt]
    exact Real.sqrt_pos.2 hrad
  have hrsq : radius t ^ 2 = u t ^ 2 + v t ^ 2 := by
    simp only [radius, hqt]
    exact Real.sq_sqrt hrad.le
  have hdenpos : 0 < radius t - u t := by
    by_contra hnot
    have hle : radius t ≤ u t := by linarith
    have hvzero : v t = 0 := by
      nlinarith [sq_nonneg (radius t - u t), sq_nonneg (v t)]
    have hupos : 0 < u t := lt_of_lt_of_le hrpos hle
    exact hcut ⟨hvzero, hupos⟩
  have hdenne : radius t - u t ≠ 0 := ne_of_gt hdenpos
  have hratio : HasDerivAt
      (fun s => v s / (radius s - u s))
      ((dv * (radius t - u t) - v t *
        (((2 * u t * du + 2 * v t * dv) /
          (2 * Real.sqrt (u t ^ 2 + v t ^ 2))) - du)) /
        (radius t - u t) ^ 2) t := by
    exact hv.div (hradius.sub hu) hdenne
  have hatan := hratio.arctan.const_mul 2
  have hsqrtpos : 0 < Real.sqrt (u t ^ 2 + v t ^ 2) := Real.sqrt_pos.2 hrad
  have hdenne' : Real.sqrt (u t ^ 2 + v t ^ 2) - u t ≠ 0 := by
    simpa [radius, q] using hdenne
  have hrsq' : Real.sqrt (u t ^ 2 + v t ^ 2) ^ 2 =
      u t ^ 2 + v t ^ 2 := Real.sq_sqrt hrad.le
  have hcoef :
      2 *
        (1 / (1 + (v t / (radius t - u t)) ^ 2) *
          ((dv * (radius t - u t) - v t *
            ((2 * u t * du + 2 * v t * dv) /
              (2 * Real.sqrt (u t ^ 2 + v t ^ 2)) - du)) /
            (radius t - u t) ^ 2)) =
        -(u t * dv - v t * du) / (u t ^ 2 + v t ^ 2) := by
    simp only [radius, q, Pi.add_apply, Pi.pow_apply]
    have hone : 1 +
        (v t / (Real.sqrt (u t ^ 2 + v t ^ 2) - u t)) ^ 2 ≠ 0 := by
      positivity
    field_simp [hdenne', ne_of_gt hrad, ne_of_gt hsqrtpos, hone]
    ring_nf
    have hrcube : Real.sqrt (u t ^ 2 + v t ^ 2) ^ 3 =
        Real.sqrt (u t ^ 2 + v t ^ 2) * (u t ^ 2 + v t ^ 2) := by
      rw [pow_succ, hrsq']
      ring
    rw [hrcube, hrsq']
    ring
  rw [hcoef] at hatan
  simpa only [positiveRayAngle, radius, q, Pi.add_apply, Pi.pow_apply] using hatan

/-- A differentiable periodic planar trace with angular cross product of one
strict sign must cross the positive horizontal ray during every period. -/
theorem exists_mem_positiveRay_of_periodic_of_angularCross_pos
    {u v du dv : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hu : ∀ t, HasDerivAt u (du t) t)
    (hv : ∀ t, HasDerivAt v (dv t) t)
    (hperiodU : u T = u 0) (hperiodV : v T = v 0)
    (hrad : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < u t ^ 2 + v t ^ 2)
    (hcross : ∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < u t * dv t - v t * du t) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, v t = 0 ∧ 0 < u t := by
  by_contra hno
  push Not at hno
  let theta : ℝ → ℝ := fun t => positiveRayAngle (u t) (v t)
  have htheta : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt theta
        (-(u t * dv t - v t * du t) / (u t ^ 2 + v t ^ 2)) t := by
    intro t ht
    exact positiveRayAngle_comp_hasDerivAt (hu t) (hv t) (hrad t ht)
      (by
        intro h
        exact (not_lt_of_ge (hno t ht h.1)) h.2)
  have hcont : ContinuousOn theta (Set.Icc (0 : ℝ) T) :=
    fun t ht => (htheta t ht).continuousAt.continuousWithinAt
  have hderivNeg : ∀ t ∈ interior (Set.Icc (0 : ℝ) T), deriv theta t < 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := interior_subset ht
    rw [(htheta t ht').deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (hcross t ht')) (hrad t ht')
  have hanti : StrictAntiOn theta (Set.Icc (0 : ℝ) T) :=
    strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) T) hcont hderivNeg
  have hthetaEq : theta T = theta 0 := by
    simp only [theta, hperiodU, hperiodV]
  have hlt := hanti (left_mem_Icc.mpr hT.le) (right_mem_Icc.mpr hT.le) hT
  exact (ne_of_lt hlt) hthetaEq

end Hilbert16
