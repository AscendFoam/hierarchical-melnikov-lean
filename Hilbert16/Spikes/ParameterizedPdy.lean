import Hilbert16.Spikes.GreenVertical
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set
open scoped Interval

/-- The parameterized integral of the one-form `P dy`. The velocity is explicit so that a
piecewise-smooth curve can be handled without relying on a global `deriv` at its join points. -/
noncomputable def parameterizedPdy
    (P : ℝ × ℝ → ℝ) (curve velocity : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, P (curve t) * (velocity t).2

/-- A graph `x = graph(y)` traversed through an arbitrary differentiable parameter `t`. -/
noncomputable def graphParameterizedPdy
    (P : ℝ × ℝ → ℝ) (graph y y' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  parameterizedPdy P (fun t => (graph (y t), y t)) (fun t => (0, y' t)) a b

/-- One-dimensional substitution for `P dy` on a reparameterized graph. This is the exact bridge
from a curve integral to the graph functional used by `verticalBoundaryPdy`. -/
theorem graphParameterizedPdy_eq_integral
    {P : ℝ × ℝ → ℝ} {graph y y' : ℝ → ℝ} {a b : ℝ}
    (hy : ∀ t ∈ Set.uIcc a b, HasDerivAt y (y' t) t)
    (hy' : ContinuousOn y' (Set.uIcc a b))
    (hP : ContinuousOn (fun u => P (graph u, u)) (y '' [[a, b]])) :
    graphParameterizedPdy P graph y y' a b =
      ∫ u in y a..y b, P (graph u, u) := by
  unfold graphParameterizedPdy parameterizedPdy
  simpa only [Function.comp_def, Prod.snd] using
    (intervalIntegral.integral_comp_mul_deriv' hy hy' hP)

/-- Two arbitrarily reparameterized graph arcs, one from bottom to top and the other from top to
bottom, give exactly `verticalBoundaryPdy`. -/
theorem graphParameterizedPdy_add_eq_verticalBoundaryPdy
    {P : ℝ × ℝ → ℝ} {left right yRight yRight' yLeft yLeft' : ℝ → ℝ}
    {a b rightStart rightEnd leftStart leftEnd : ℝ}
    (hyRight : ∀ t ∈ Set.uIcc rightStart rightEnd,
      HasDerivAt yRight (yRight' t) t)
    (hyRight' : ContinuousOn yRight' (Set.uIcc rightStart rightEnd))
    (hyRightRange : yRight '' [[rightStart, rightEnd]] ⊆ Set.uIcc a b)
    (hPright : ContinuousOn (fun u => P (right u, u)) (Set.uIcc a b))
    (hyLeft : ∀ t ∈ Set.uIcc leftStart leftEnd,
      HasDerivAt yLeft (yLeft' t) t)
    (hyLeft' : ContinuousOn yLeft' (Set.uIcc leftStart leftEnd))
    (hyLeftRange : yLeft '' [[leftStart, leftEnd]] ⊆ Set.uIcc a b)
    (hPleft : ContinuousOn (fun u => P (left u, u)) (Set.uIcc a b))
    (hRightStart : yRight rightStart = a) (hRightEnd : yRight rightEnd = b)
    (hLeftStart : yLeft leftStart = b) (hLeftEnd : yLeft leftEnd = a) :
    graphParameterizedPdy P right yRight yRight' rightStart rightEnd +
        graphParameterizedPdy P left yLeft yLeft' leftStart leftEnd =
      verticalBoundaryPdy P left right a b := by
  rw [graphParameterizedPdy_eq_integral hyRight hyRight' (hPright.mono hyRightRange),
    graphParameterizedPdy_eq_integral hyLeft hyLeft' (hPleft.mono hyLeftRange),
    hRightStart, hRightEnd, hLeftStart, hLeftEnd]
  have hsymm : (∫ u in b..a, P (left u, u)) = -∫ u in a..b, P (left u, u) :=
    intervalIntegral.integral_symm a b
  rw [hsymm]
  unfold verticalBoundaryPdy
  have hright : IntervalIntegrable (fun u => P (right u, u))
      MeasureTheory.volume a b := by
    exact hPright.intervalIntegrable
  have hleft : IntervalIntegrable (fun u => P (left u, u))
      MeasureTheory.volume a b := by
    exact hPleft.intervalIntegrable
  rw [intervalIntegral.integral_sub hright hleft]
  ring

/-- The `P dy` functional ignores the first component of the supplied velocity. -/
theorem parameterizedPdy_congr_velocity_snd
    (P : ℝ × ℝ → ℝ) (curve velocity₁ velocity₂ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hvel : ∀ t ∈ Set.uIcc a b, (velocity₁ t).2 = (velocity₂ t).2) :
    parameterizedPdy P curve velocity₁ a b = parameterizedPdy P curve velocity₂ a b := by
  unfold parameterizedPdy
  apply intervalIntegral.integral_congr
  intro t ht
  change P (curve t) * (velocity₁ t).2 = P (curve t) * (velocity₂ t).2
  rw [hvel t ht]

/-- Congruence of the parameterized `P dy` integral on the integration interval. -/
theorem parameterizedPdy_congr
    (P : ℝ × ℝ → ℝ) (curve₁ curve₂ velocity₁ velocity₂ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hcurve : ∀ t ∈ Set.uIcc a b, curve₁ t = curve₂ t)
    (hvel : ∀ t ∈ Set.uIcc a b, (velocity₁ t).2 = (velocity₂ t).2) :
    parameterizedPdy P curve₁ velocity₁ a b =
      parameterizedPdy P curve₂ velocity₂ a b := by
  unfold parameterizedPdy
  apply intervalIntegral.integral_congr
  intro t ht
  change P (curve₁ t) * (velocity₁ t).2 = P (curve₂ t) * (velocity₂ t).2
  rw [hcurve t ht, hvel t ht]

/-- Reversing the endpoints reverses the `P dy` integral. -/
theorem parameterizedPdy_symm
    (P : ℝ × ℝ → ℝ) (curve velocity : ℝ → ℝ × ℝ) (a b : ℝ) :
    parameterizedPdy P curve velocity b a =
      -parameterizedPdy P curve velocity a b := by
  exact intervalIntegral.integral_symm a b

/-- Exact affine reparametrization of `P dy`.  No regularity hypothesis on
the integrand is needed because the affine parameter map is monotone (in one
of the two possible directions) and Mathlib's interval integral substitution
theorem handles both orientations. -/
theorem parameterizedPdy_comp_affine
    (P : ℝ × ℝ → ℝ) (curve velocity : ℝ → ℝ × ℝ)
    (c d a b : ℝ) :
    parameterizedPdy P (fun t => curve (c + d * t))
        (fun t => d • velocity (c + d * t)) a b =
      parameterizedPdy P curve velocity (c + d * a) (c + d * b) := by
  let f : ℝ → ℝ := fun t => c + d * t
  let f' : ℝ → ℝ := fun _ => d
  let g : ℝ → ℝ := fun u => P (curve u) * (velocity u).2
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    simpa [f, f'] using ((hasDerivAt_id t).const_mul d).const_add c
  rcases le_total 0 d with hd | hd
  · have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := a) (b := b) (f := f) (f' := f') (g := g)
      hf.continuousOn
      (fun t _ => hderiv t)
      (fun _ _ => by simpa [f'] using hd)
    simpa [parameterizedPdy, f, f', g, Function.comp_def,
      Prod.smul_snd, mul_comm, mul_left_comm, mul_assoc] using hsubst
  · have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (a := a) (b := b) (f := f) (f' := f') (g := g)
      hf.continuousOn
      (fun t _ => hderiv t)
      (fun _ _ => by simpa [f'] using hd)
    simpa [parameterizedPdy, f, f', g, Function.comp_def,
      Prod.smul_snd, mul_comm, mul_left_comm, mul_assoc] using hsubst

/-- Change variables in `P dy` along an arbitrary nondecreasing smooth
clock.  This is the form used to compare Hamiltonian time with the explicit
angular clock. -/
theorem parameterizedPdy_comp_of_deriv_nonneg
    (P : ℝ × ℝ → ℝ) (curve velocity : ℝ → ℝ × ℝ)
    (clock clock' : ℝ → ℝ) (a b : ℝ)
    (hclock : ContinuousOn clock [[a, b]])
    (hderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt clock (clock' t) t)
    (hclock' : ∀ t ∈ Set.Ioo (min a b) (max a b), 0 ≤ clock' t) :
    parameterizedPdy P (fun t => curve (clock t))
        (fun t => clock' t • velocity (clock t)) a b =
      parameterizedPdy P curve velocity (clock a) (clock b) := by
  let g : ℝ → ℝ := fun u => P (curve u) * (velocity u).2
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := clock) (f' := clock') (g := g)
    hclock hderiv hclock'
  simpa [parameterizedPdy, g, Function.comp_def, Prod.smul_snd,
    mul_comm, mul_left_comm, mul_assoc] using hsubst

/-- The decreasing-clock counterpart of
`parameterizedPdy_comp_of_deriv_nonneg`. -/
theorem parameterizedPdy_comp_of_deriv_nonpos
    (P : ℝ × ℝ → ℝ) (curve velocity : ℝ → ℝ × ℝ)
    (clock clock' : ℝ → ℝ) (a b : ℝ)
    (hclock : ContinuousOn clock [[a, b]])
    (hderiv : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt clock (clock' t) t)
    (hclock' : ∀ t ∈ Set.Ioo (min a b) (max a b), clock' t ≤ 0) :
    parameterizedPdy P (fun t => curve (clock t))
        (fun t => clock' t • velocity (clock t)) a b =
      parameterizedPdy P curve velocity (clock a) (clock b) := by
  let g : ℝ → ℝ := fun u => P (curve u) * (velocity u).2
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := a) (b := b) (f := clock) (f' := clock') (g := g)
    hclock hderiv hclock'
  simpa [parameterizedPdy, g, Function.comp_def, Prod.smul_snd,
    mul_comm, mul_left_comm, mul_assoc] using hsubst

end Hilbert16.Spikes
