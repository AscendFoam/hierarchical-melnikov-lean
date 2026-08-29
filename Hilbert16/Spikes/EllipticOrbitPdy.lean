import Hilbert16.Spikes.ChebyshevOrbit
import Hilbert16.Spikes.ParameterizedPdy

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set
open scoped Interval

/-- Horizontal semiaxis of the quadratic energy ellipse. -/
noncomputable def ellipticHorizontalRadius (h : ℝ) : ℝ :=
  Real.sqrt (2 * h)

/-- Vertical semiaxis of the quadratic energy ellipse. -/
noncomputable def ellipticVerticalRadius (lambda h : ℝ) : ℝ :=
  ellipticHorizontalRadius h / Real.sqrt lambda

/-- Right vertical graph of the quadratic energy ellipse. -/
noncomputable def ellipticRightGraph (lambda h v : ℝ) : ℝ :=
  Real.sqrt (2 * h - lambda * v ^ 2)

/-- Left vertical graph of the quadratic energy ellipse. -/
noncomputable def ellipticLeftGraph (lambda h v : ℝ) : ℝ :=
  -ellipticRightGraph lambda h v

theorem continuous_ellipticRightGraph (lambda h : ℝ) :
    Continuous (ellipticRightGraph lambda h) := by
  unfold ellipticRightGraph
  fun_prop

theorem continuous_ellipticLeftGraph (lambda h : ℝ) :
    Continuous (ellipticLeftGraph lambda h) := by
  unfold ellipticLeftGraph
  exact (continuous_ellipticRightGraph lambda h).neg

theorem ellipticVerticalRadius_pos
    {lambda h : ℝ} (hlambda : 0 < lambda) (hh : 0 < h) :
    0 < ellipticVerticalRadius lambda h := by
  unfold ellipticVerticalRadius ellipticHorizontalRadius
  positivity

theorem ellipticVerticalRadius_lt_one
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    ellipticVerticalRadius lambda h < 1 := by
  have hhorizontal : ellipticHorizontalRadius h < 1 := by
    unfold ellipticHorizontalRadius
    simpa using Real.sqrt_lt_sqrt (by positivity : 0 ≤ 2 * h) (by nlinarith : 2 * h < 1)
  have hsqrtOne : 1 ≤ Real.sqrt lambda := Real.one_le_sqrt.mpr hlambda
  calc
    ellipticVerticalRadius lambda h ≤ ellipticHorizontalRadius h := by
      unfold ellipticVerticalRadius
      exact div_le_self (Real.sqrt_nonneg _) hsqrtOne
    _ < 1 := hhorizontal

private theorem ellipse_graph_square_identity
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h) :
    2 * h - lambda *
        (ellipticVerticalRadius lambda h * Real.sin t) ^ 2 =
      (ellipticHorizontalRadius h * Real.cos t) ^ 2 := by
  have hsqrtLambda : Real.sqrt lambda ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hsqrtH : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  unfold ellipticVerticalRadius ellipticHorizontalRadius
  simp only [mul_pow, div_pow, hsqrtLambda, hsqrtH]
  field_simp [hlambda.ne']
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem ellipticRightGraph_comp_sin
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ellipticRightGraph lambda h (ellipticVerticalRadius lambda h * Real.sin t) =
      ellipticHorizontalRadius h * Real.cos t := by
  rw [ellipticRightGraph, ellipse_graph_square_identity hlambda hh,
    Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.cos_nonneg_of_mem_Icc ht)

theorem ellipticLeftGraph_comp_sin
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2)) :
    ellipticLeftGraph lambda h (ellipticVerticalRadius lambda h * Real.sin t) =
      ellipticHorizontalRadius h * Real.cos t := by
  rw [ellipticLeftGraph, ellipticRightGraph, ellipse_graph_square_identity hlambda hh,
    Real.sqrt_sq_eq_abs, abs_of_nonpos]
  · ring
  · exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
      (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 ht.2)

theorem ellipticOrbitUV_eq_rightGraph
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ellipticOrbitUV lambda h t =
      (ellipticRightGraph lambda h (ellipticVerticalRadius lambda h * Real.sin t),
        ellipticVerticalRadius lambda h * Real.sin t) := by
  apply Prod.ext
  · exact ellipticRightGraph_comp_sin hlambda hh ht |>.symm
  · rfl

theorem ellipticOrbitUV_eq_leftGraph
    {lambda h t : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2)) :
    ellipticOrbitUV lambda h t =
      (ellipticLeftGraph lambda h (ellipticVerticalRadius lambda h * Real.sin t),
        ellipticVerticalRadius lambda h * Real.sin t) := by
  apply Prod.ext
  · exact ellipticLeftGraph_comp_sin hlambda hh ht |>.symm
  · rfl

theorem ellipticVerticalParam_hasDerivAt (lambda h t : ℝ) :
    HasDerivAt (fun s => ellipticVerticalRadius lambda h * Real.sin s)
      (ellipticVerticalRadius lambda h * Real.cos t) t := by
  simpa using (Real.hasDerivAt_sin t).const_mul (ellipticVerticalRadius lambda h)

theorem ellipticVerticalParam_range
    {lambda h a b : ℝ} (hRadius : 0 ≤ ellipticVerticalRadius lambda h) :
    (fun t => ellipticVerticalRadius lambda h * Real.sin t) '' [[a, b]] ⊆
      Set.uIcc (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h) := by
  intro v hv
  rcases hv with ⟨t, ht, rfl⟩
  rw [Set.uIcc_of_le (neg_le_self hRadius)]
  constructor
  · have hsin := (abs_le.mp (Real.abs_sin_le_one t)).1
    nlinarith
  · have hsin := (abs_le.mp (Real.abs_sin_le_one t)).2
    nlinarith

theorem ellipticVerticalParam_endpoints (lambda h : ℝ) :
    ellipticVerticalRadius lambda h * Real.sin (-(Real.pi / 2)) =
        -ellipticVerticalRadius lambda h ∧
      ellipticVerticalRadius lambda h * Real.sin (Real.pi / 2) =
        ellipticVerticalRadius lambda h ∧
      ellipticVerticalRadius lambda h * Real.sin (Real.pi + Real.pi / 2) =
        -ellipticVerticalRadius lambda h := by
  constructor
  · rw [Real.sin_neg, Real.sin_pi_div_two]
    ring
  constructor
  · rw [Real.sin_pi_div_two, mul_one]
  · rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring

/-- The `Q dv` integral around the ellipse, represented by its two smooth angular half-arcs. -/
noncomputable def ellipticAngularPdy
    (Q : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  parameterizedPdy Q (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h)
      (-(Real.pi / 2)) (Real.pi / 2) +
    parameterizedPdy Q (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h)
      (Real.pi / 2) (Real.pi + Real.pi / 2)

/-- The same `Q dv` integral represented as upward right graph minus upward left graph. -/
noncomputable def ellipticVerticalBoundaryPdy
    (Q : ℝ × ℝ → ℝ) (lambda h : ℝ) : ℝ :=
  verticalBoundaryPdy Q (ellipticLeftGraph lambda h) (ellipticRightGraph lambda h)
    (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)

/-- The angular ellipse integral is exactly the compiled two-graph boundary functional. This is
the explicit Jordan-boundary identification needed by the Chebyshev orbit. -/
theorem ellipticAngularPdy_eq_verticalBoundaryPdy_of_continuousOn
    {Q : ℝ × ℝ → ℝ} {lambda h : ℝ} (hlambda : 0 < lambda) (hh : 0 < h)
    (hQright : ContinuousOn (fun v => Q (ellipticRightGraph lambda h v, v))
      (Set.uIcc (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)))
    (hQleft : ContinuousOn (fun v => Q (ellipticLeftGraph lambda h v, v))
      (Set.uIcc (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h))) :
    ellipticAngularPdy Q lambda h = ellipticVerticalBoundaryPdy Q lambda h := by
  let y : ℝ → ℝ := fun t => ellipticVerticalRadius lambda h * Real.sin t
  let y' : ℝ → ℝ := fun t => ellipticVerticalRadius lambda h * Real.cos t
  have hRadius : 0 ≤ ellipticVerticalRadius lambda h :=
    (ellipticVerticalRadius_pos hlambda hh).le
  have hRightOrder : -(Real.pi / 2) ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hLeftOrder : Real.pi / 2 ≤ Real.pi + Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hrightCurve : ∀ t ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
      ellipticOrbitUV lambda h t = (ellipticRightGraph lambda h (y t), y t) := by
    intro t ht
    apply ellipticOrbitUV_eq_rightGraph hlambda hh.le
    rw [Set.uIcc_of_le hRightOrder] at ht
    exact ht
  have hleftCurve : ∀ t ∈ Set.uIcc (Real.pi / 2) (Real.pi + Real.pi / 2),
      ellipticOrbitUV lambda h t = (ellipticLeftGraph lambda h (y t), y t) := by
    intro t ht
    apply ellipticOrbitUV_eq_leftGraph hlambda hh.le
    rw [Set.uIcc_of_le hLeftOrder] at ht
    exact ht
  have hvelocity : ∀ t, (ellipticOrbitUVVelocity lambda h t).2 = (0, y' t).2 := by
    intro t
    rfl
  have hright :
      parameterizedPdy Q (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h)
          (-(Real.pi / 2)) (Real.pi / 2) =
        graphParameterizedPdy Q (ellipticRightGraph lambda h) y y'
          (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [graphParameterizedPdy] using
      parameterizedPdy_congr Q
        (ellipticOrbitUV lambda h)
        (fun t => (ellipticRightGraph lambda h (y t), y t))
        (ellipticOrbitUVVelocity lambda h) (fun t => (0, y' t))
        (-(Real.pi / 2)) (Real.pi / 2) hrightCurve
        (fun t _ => hvelocity t)
  have hleft :
      parameterizedPdy Q (ellipticOrbitUV lambda h) (ellipticOrbitUVVelocity lambda h)
          (Real.pi / 2) (Real.pi + Real.pi / 2) =
        graphParameterizedPdy Q (ellipticLeftGraph lambda h) y y'
          (Real.pi / 2) (Real.pi + Real.pi / 2) := by
    simpa only [graphParameterizedPdy] using
      parameterizedPdy_congr Q
        (ellipticOrbitUV lambda h)
        (fun t => (ellipticLeftGraph lambda h (y t), y t))
        (ellipticOrbitUVVelocity lambda h) (fun t => (0, y' t))
        (Real.pi / 2) (Real.pi + Real.pi / 2) hleftCurve
        (fun t _ => hvelocity t)
  unfold ellipticAngularPdy ellipticVerticalBoundaryPdy
  rw [hright, hleft]
  apply graphParameterizedPdy_add_eq_verticalBoundaryPdy
  · intro t ht
    exact ellipticVerticalParam_hasDerivAt lambda h t
  · fun_prop
  · simpa only [y] using
      (ellipticVerticalParam_range (a := -(Real.pi / 2)) (b := Real.pi / 2) hRadius)
  · exact hQright
  · intro t ht
    exact ellipticVerticalParam_hasDerivAt lambda h t
  · fun_prop
  · simpa only [y] using
      (ellipticVerticalParam_range (a := Real.pi / 2)
        (b := Real.pi + Real.pi / 2) hRadius)
  · exact hQleft
  · simpa only [y] using (ellipticVerticalParam_endpoints lambda h).1
  · simpa only [y] using (ellipticVerticalParam_endpoints lambda h).2.1
  · simpa only [y] using (ellipticVerticalParam_endpoints lambda h).2.1
  · simpa only [y] using (ellipticVerticalParam_endpoints lambda h).2.2

theorem ellipticAngularPdy_eq_verticalBoundaryPdy
    {Q : ℝ × ℝ → ℝ} (hQ : Continuous Q)
    {lambda h : ℝ} (hlambda : 0 < lambda) (hh : 0 < h) :
    ellipticAngularPdy Q lambda h = ellipticVerticalBoundaryPdy Q lambda h := by
  apply ellipticAngularPdy_eq_verticalBoundaryPdy_of_continuousOn hlambda hh
  · exact hQ.comp_continuousOn
      ((continuous_ellipticRightGraph lambda h).prodMk continuous_id).continuousOn
  · exact hQ.comp_continuousOn
      ((continuous_ellipticLeftGraph lambda h).prodMk continuous_id).continuousOn

end Hilbert16.Spikes
