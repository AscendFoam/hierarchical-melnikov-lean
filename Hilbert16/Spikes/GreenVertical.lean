import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- A canonical primitive in the first coordinate. This is the analytic counterpart of the
paper's polynomial antiderivative `P(x,y)=∫₀ˣ q(s,y) ds`. -/
noncomputable def firstCoordinatePrimitive (q : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..z.1, q (x, z.2)

/-- The `P dy` integral on the positively oriented vertical boundary presentation of a region
`left(y) ≤ x ≤ right(y)`. The right graph is traversed upward and the left graph downward;
horizontal closing pieces, when present, contribute zero to `P dy`. -/
noncomputable def verticalBoundaryPdy
    (P : ℝ × ℝ → ℝ) (left right : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ y in a..b, P (right y, y) - P (left y, y)

/-- Fundamental-theorem form of the vertical Green identity: the difference of the canonical
first-coordinate primitive at two graph points is the oriented inner integral of its density. -/
theorem firstCoordinatePrimitive_sub_eq_integral
    {q : ℝ × ℝ → ℝ} (hq : Continuous q) (left right y : ℝ) :
    firstCoordinatePrimitive q (right, y) - firstCoordinatePrimitive q (left, y) =
      ∫ x in left..right, q (x, y) := by
  have hcont : Continuous (fun x : ℝ => q (x, y)) :=
    hq.comp (Continuous.prodMk_left y)
  have hzeroLeft : IntervalIntegrable (fun x : ℝ => q (x, y))
      MeasureTheory.volume 0 left := hcont.intervalIntegrable 0 left
  have hleftRight : IntervalIntegrable (fun x : ℝ => q (x, y))
      MeasureTheory.volume left right := hcont.intervalIntegrable left right
  have hadd := intervalIntegral.integral_add_adjacent_intervals hzeroLeft hleftRight
  unfold firstCoordinatePrimitive
  linarith

/-- Green's formula for the vertical-boundary presentation, proved from one-dimensional FTC
rather than assumed as a project axiom. This is the reusable bridge for a Chebyshev cell after its
two boundary graphs have been identified. -/
theorem verticalBoundaryPdy_firstCoordinatePrimitive_eq_iteratedIntegral
    {q : ℝ × ℝ → ℝ} (hq : Continuous q)
    (left right : ℝ → ℝ) (a b : ℝ) :
    verticalBoundaryPdy (firstCoordinatePrimitive q) left right a b =
      ∫ y in a..b, ∫ x in left y..right y, q (x, y) := by
  unfold verticalBoundaryPdy
  apply intervalIntegral.integral_congr
  intro y hy
  exact firstCoordinatePrimitive_sub_eq_integral hq (left y) (right y) y

/-- Adding an arbitrary function of `y` to the primitive does not alter a closed `P dy`
boundary integral. -/
theorem verticalBoundaryPdy_add_snd
    (P : ℝ × ℝ → ℝ) (c left right : ℝ → ℝ) (a b : ℝ) :
    verticalBoundaryPdy (fun z => P z + c z.2) left right a b =
      verticalBoundaryPdy P left right a b := by
  unfold verticalBoundaryPdy
  apply intervalIntegral.integral_congr
  intro y hy
  ring

end Hilbert16.Spikes
