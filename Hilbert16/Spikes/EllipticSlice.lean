import Hilbert16.Spikes.EllipticOrbitPdy
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set MeasureTheory
open scoped Interval

theorem ellipticVerticalRadius_energy
    {lambda h : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h) :
    lambda * ellipticVerticalRadius lambda h ^ 2 = 2 * h := by
  have hsqrtLambda : Real.sqrt lambda ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hsqrtH : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  unfold ellipticVerticalRadius ellipticHorizontalRadius
  rw [div_pow, hsqrtLambda, hsqrtH]
  field_simp [hlambda.ne']

theorem mem_Ioo_ellipticVerticalRadius_iff
    {lambda h v : ℝ} (hlambda : 0 < lambda) (hh : 0 < h) :
    v ∈ Set.Ioo (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h) ↔
      lambda * v ^ 2 < 2 * h := by
  have hBpos := ellipticVerticalRadius_pos hlambda hh
  have hBenergy := ellipticVerticalRadius_energy hlambda hh.le
  constructor
  · intro hv
    have hvAbs : |v| < ellipticVerticalRadius lambda h := abs_lt.mpr hv
    have hvSq : v ^ 2 < ellipticVerticalRadius lambda h ^ 2 := by
      simpa only [sq_abs] using
        (sq_lt_sq₀ (abs_nonneg v) hBpos.le).2 hvAbs
    nlinarith [mul_pos hlambda (sub_pos.mpr hvSq)]
  · intro hv
    have hvSq : v ^ 2 < ellipticVerticalRadius lambda h ^ 2 := by
      nlinarith [mul_pos hlambda
        (show 0 < ellipticVerticalRadius lambda h ^ 2 - v ^ 2 by
          nlinarith [hBenergy, hv])]
    apply abs_lt.mp
    exact (sq_lt_sq₀ (abs_nonneg v) hBpos.le).1 (by simpa only [sq_abs] using hvSq)

theorem ellipticRightGraph_sq
    {lambda h v : ℝ} (hv : lambda * v ^ 2 ≤ 2 * h) :
    ellipticRightGraph lambda h v ^ 2 = 2 * h - lambda * v ^ 2 := by
  unfold ellipticRightGraph
  exact Real.sq_sqrt (by linarith)

theorem ellipticRightGraph_pos
    {lambda h v : ℝ} (hv : lambda * v ^ 2 < 2 * h) :
    0 < ellipticRightGraph lambda h v := by
  unfold ellipticRightGraph
  exact Real.sqrt_pos.2 (by linarith)

theorem mem_ellipticEnergyDisk_iff_mem_verticalSlice
    {lambda h u v : ℝ} (hlambda : 0 < lambda) (hh : 0 < h)
    (hv : v ∈ Set.Ioo (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)) :
    (u, v) ∈ ellipticEnergyDisk lambda h ↔
      u ∈ Set.Ioo (ellipticLeftGraph lambda h v) (ellipticRightGraph lambda h v) := by
  have hvEnergy := (mem_Ioo_ellipticVerticalRadius_iff hlambda hh).1 hv
  have hRpos := ellipticRightGraph_pos hvEnergy
  have hRsq := ellipticRightGraph_sq hvEnergy.le
  unfold ellipticEnergyDisk ellipticLeftGraph
  change u ^ 2 + lambda * v ^ 2 < 2 * h ↔
    -ellipticRightGraph lambda h v < u ∧ u < ellipticRightGraph lambda h v
  constructor
  · intro hu
    have huSq : u ^ 2 < ellipticRightGraph lambda h v ^ 2 := by
      nlinarith
    have huAbs : |u| < ellipticRightGraph lambda h v :=
      (sq_lt_sq₀ (abs_nonneg u) hRpos.le).1 (by simpa only [sq_abs] using huSq)
    exact abs_lt.mp huAbs
  · intro hu
    have huAbs : |u| < ellipticRightGraph lambda h v := abs_lt.mpr hu
    have huSq : u ^ 2 < ellipticRightGraph lambda h v ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg u) hRpos.le).2 huAbs
    nlinarith

theorem not_mem_ellipticEnergyDisk_of_not_mem_verticalRange
    {lambda h u v : ℝ} (hlambda : 0 < lambda) (hh : 0 < h)
    (hv : v ∉ Set.Ioo (-ellipticVerticalRadius lambda h) (ellipticVerticalRadius lambda h)) :
    (u, v) ∉ ellipticEnergyDisk lambda h := by
  intro huv
  apply hv
  apply (mem_Ioo_ellipticVerticalRadius_iff hlambda hh).2
  have huNonneg := sq_nonneg u
  exact lt_of_le_of_lt (by nlinarith : lambda * v ^ 2 ≤ u ^ 2 + lambda * v ^ 2) huv

/-- Fubini in the exact vertical-slice presentation of the open energy ellipse. -/
theorem integral_ellipticEnergyDisk_eq_verticalSlices
    {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
      ∫ v in -ellipticVerticalRadius lambda h..ellipticVerticalRadius lambda h,
        ∫ u in ellipticLeftGraph lambda h v..ellipticRightGraph lambda h v, f (u, v) := by
  let s := ellipticEnergyDisk lambda h
  let B := ellipticVerticalRadius lambda h
  let inner : ℝ → ℝ := fun v =>
    ∫ u in ellipticLeftGraph lambda h v..ellipticRightGraph lambda h v, f (u, v)
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hBpos : 0 < B := ellipticVerticalRadius_pos hlambdaPos hh
  have hsMeas : MeasurableSet s := measurableSet_ellipticEnergyDisk lambda h
  have hfIntOn : IntegrableOn f s :=
    continuous_integrableOn_ellipticEnergyDisk hf lambda hh hlambda
  have hIndicatorInt : Integrable (s.indicator f) := hfIntOn.integrable_indicator hsMeas
  have hFubini : (∫ z : ℝ × ℝ, s.indicator f z) =
      ∫ v : ℝ, ∫ u : ℝ, s.indicator f (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod_symm (s.indicator f)
      (by simpa only [Measure.volume_eq_prod] using hIndicatorInt)
  have hinner : ∀ v : ℝ, (∫ u : ℝ, s.indicator f (u, v)) =
      (Set.Ioo (-B) B).indicator inner v := by
    intro v
    by_cases hv : v ∈ Set.Ioo (-B) B
    · rw [Set.indicator_of_mem hv]
      have hv' : v ∈ Set.Ioo (-ellipticVerticalRadius lambda h)
          (ellipticVerticalRadius lambda h) := hv
      have hRpos := ellipticRightGraph_pos
        ((mem_Ioo_ellipticVerticalRadius_iff hlambdaPos hh).1 hv')
      calc
        (∫ u : ℝ, s.indicator f (u, v)) =
            ∫ u : ℝ,
              (Set.Ioo (ellipticLeftGraph lambda h v) (ellipticRightGraph lambda h v)).indicator
                (fun u => f (u, v)) u := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          have hfiber := mem_ellipticEnergyDisk_iff_mem_verticalSlice
            (u := u) hlambdaPos hh hv'
          by_cases hu : u ∈ Set.Ioo (ellipticLeftGraph lambda h v)
              (ellipticRightGraph lambda h v)
          · have hus : (u, v) ∈ s := hfiber.2 hu
            simp [Set.indicator_of_mem, hu, hus]
          · have hus : (u, v) ∉ s := fun hus => hu (hfiber.1 hus)
            simp [hu, hus]
        _ = ∫ u in Set.Ioo (ellipticLeftGraph lambda h v)
              (ellipticRightGraph lambda h v), f (u, v) := by
          rw [integral_indicator measurableSet_Ioo]
        _ = inner v := by
          unfold inner
          rw [intervalIntegral.integral_of_le
              (by rw [ellipticLeftGraph]; linarith [hRpos]),
            integral_Ioc_eq_integral_Ioo]
    · rw [Set.indicator_of_notMem hv]
      have hv' : v ∉ Set.Ioo (-ellipticVerticalRadius lambda h)
          (ellipticVerticalRadius lambda h) := hv
      have hzero : (fun u : ℝ => s.indicator f (u, v)) = 0 := by
        funext u
        have huv : (u, v) ∉ s :=
          not_mem_ellipticEnergyDisk_of_not_mem_verticalRange hlambdaPos hh hv'
        simp [huv]
      simp [hzero]
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h, f z) =
        ∫ z : ℝ × ℝ, s.indicator f z := by
      exact (integral_indicator hsMeas).symm
    _ = ∫ v : ℝ, ∫ u : ℝ, s.indicator f (u, v) := hFubini
    _ = ∫ v : ℝ, (Set.Ioo (-B) B).indicator inner v := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = ∫ v in Set.Ioo (-B) B, inner v := by
      rw [integral_indicator measurableSet_Ioo]
    _ = ∫ v in -B..B, inner v := by
      rw [intervalIntegral.integral_of_le (by linarith [hBpos]),
        integral_Ioc_eq_integral_Ioo]
    _ = ∫ v in -ellipticVerticalRadius lambda h..ellipticVerticalRadius lambda h,
        ∫ u in ellipticLeftGraph lambda h v..ellipticRightGraph lambda h v, f (u, v) := rfl

end Hilbert16.Spikes
