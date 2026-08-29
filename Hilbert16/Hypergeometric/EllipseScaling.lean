import Hilbert16.Hypergeometric.ModeIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false

namespace Hilbert16

open MeasureTheory Set
open Spikes

/-! ### The anisotropic ellipse-to-disk scaling in Paper Eq. (3.12) -/

/-- The open ellipse obtained from one Chebyshev cell in the local coordinates `(u,v)`. -/
def ellipticEnergyDisk (lambda h : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + lambda * z.2 ^ 2 < 2 * h}

theorem measurableSet_ellipticEnergyDisk (lambda h : ℝ) :
    MeasurableSet (ellipticEnergyDisk lambda h) := by
  exact measurableSet_lt
    ((measurable_fst.pow_const 2).add (measurable_const.mul (measurable_snd.pow_const 2)))
    measurable_const

/-- The unnormalized even mode on the original ellipse. -/
noncomputable def ellipticModeIntegrand (alpha beta : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.cos (alpha * Real.arcsin z.1) * Real.cos (beta * Real.arcsin z.2)

theorem continuous_ellipticModeIntegrand (alpha beta : ℝ) :
    Continuous (ellipticModeIntegrand alpha beta) := by
  unfold ellipticModeIntegrand
  fun_prop

theorem continuous_integrableOn_ellipticEnergyDisk
    {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (lambda : ℝ) {h : ℝ} (hh : 0 < h) (hlambda : 1 ≤ lambda) :
    IntegrableOn f (ellipticEnergyDisk lambda h) := by
  let R := Real.sqrt (2 * h)
  let K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R
  have hsubset : ellipticEnergyDisk lambda h ⊆ K := by
    intro z hz
    have hz' : z.1 ^ 2 + lambda * z.2 ^ 2 < 2 * h := hz
    have hlambda0 : 0 ≤ lambda := le_trans zero_le_one hlambda
    have hx2 : z.1 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.2]
    have hy2 : z.2 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.1]
    have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
    have hRabs : |R| = R := abs_of_nonneg hRnonneg
    have hxR2 : z.1 ^ 2 < R ^ 2 := by
      dsimp [R]
      rwa [Real.sq_sqrt (by positivity)]
    have hyR2 : z.2 ^ 2 < R ^ 2 := by
      dsimp [R]
      rwa [Real.sq_sqrt (by positivity)]
    have hxabs : |z.1| < R := by simpa only [hRabs] using (sq_lt_sq.mp hxR2)
    have hyabs : |z.2| < R := by simpa only [hRabs] using (sq_lt_sq.mp hyR2)
    exact ⟨⟨(abs_lt.mp hxabs).1.le, (abs_lt.mp hxabs).2.le⟩,
      ⟨(abs_lt.mp hyabs).1.le, (abs_lt.mp hyabs).2.le⟩⟩
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set hsubset

theorem ellipticModeIntegrableOn
    (alpha beta lambda : ℝ) {h : ℝ} (hh : 0 < h) (hlambda : 1 ≤ lambda) :
    IntegrableOn (ellipticModeIntegrand alpha beta) (ellipticEnergyDisk lambda h) :=
  continuous_integrableOn_ellipticEnergyDisk
    (continuous_ellipticModeIntegrand alpha beta) lambda hh hlambda

theorem diskScaledModeIntegrableOn
    (alpha beta lambda : ℝ) {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun z : ℝ × ℝ =>
      Real.cos (alpha * Real.arcsin z.2) *
        Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda)))
      (cartesianEnergyDisk h) := by
  let R := Real.sqrt (2 * h)
  let K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R
  have hsubset : cartesianEnergyDisk h ⊆ K := by
    intro z hz
    have hz' : z.1 ^ 2 + z.2 ^ 2 < 2 * h := hz
    have hx2 : z.1 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.2]
    have hy2 : z.2 ^ 2 < 2 * h := by nlinarith [sq_nonneg z.1]
    have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
    have hRabs : |R| = R := abs_of_nonneg hRnonneg
    have hxR2 : z.1 ^ 2 < R ^ 2 := by
      dsimp [R]
      rwa [Real.sq_sqrt (by positivity)]
    have hyR2 : z.2 ^ 2 < R ^ 2 := by
      dsimp [R]
      rwa [Real.sq_sqrt (by positivity)]
    have hxabs : |z.1| < R := by simpa only [hRabs] using (sq_lt_sq.mp hxR2)
    have hyabs : |z.2| < R := by simpa only [hRabs] using (sq_lt_sq.mp hyR2)
    exact ⟨⟨(abs_lt.mp hxabs).1.le, (abs_lt.mp hxabs).2.le⟩,
      ⟨(abs_lt.mp hyabs).1.le, (abs_lt.mp hyabs).2.le⟩⟩
  have hcontinuous : Continuous (fun z : ℝ × ℝ =>
      Real.cos (alpha * Real.arcsin z.2) *
        Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) := by
    fun_prop
  exact (hcontinuous.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set hsubset

/-- The exact Jacobian factor for `w = sqrt(lambda) * v`, with a coordinate swap chosen to
match `cartesianEnergyDisk`'s `(w,u)` convention. -/
theorem ellipticModeIntegral_eq_inv_sqrt_mul_disk
    (alpha beta lambda : ℝ) {h : ℝ} (hh : 0 < h) (hlambda : 1 ≤ lambda) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
      ellipticModeIntegrand alpha beta z) =
      (Real.sqrt lambda)⁻¹ *
        ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
          Real.cos (alpha * Real.arcsin z.2) *
            Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda)) := by
  let G : ℝ × ℝ → ℝ :=
    (ellipticEnergyDisk lambda h).indicator (ellipticModeIntegrand alpha beta)
  let D : ℝ × ℝ → ℝ :=
    (cartesianEnergyDisk h).indicator (fun z =>
      Real.cos (alpha * Real.arcsin z.2) *
        Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda)))
  have hlambda0 : 0 ≤ lambda := le_trans zero_le_one hlambda
  have hsqrtPos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)
  have hsqrtNe : Real.sqrt lambda ≠ 0 := hsqrtPos.ne'
  have hmem : ∀ u v : ℝ,
      (Real.sqrt lambda * v, u) ∈ cartesianEnergyDisk h ↔
        (u, v) ∈ ellipticEnergyDisk lambda h := by
    intro u v
    unfold cartesianEnergyDisk ellipticEnergyDisk
    change (Real.sqrt lambda * v) ^ 2 + u ^ 2 < 2 * h ↔
      u ^ 2 + lambda * v ^ 2 < 2 * h
    rw [mul_pow, Real.sq_sqrt hlambda0]
    constructor <;> intro H <;> nlinarith
  have hpoint : ∀ u v : ℝ,
      D (Real.sqrt lambda * v, u) = G (u, v) := by
    intro u v
    by_cases hv : (u, v) ∈ ellipticEnergyDisk lambda h
    · have hw := (hmem u v).mpr hv
      simp only [D, G, Set.indicator_of_mem hw, Set.indicator_of_mem hv,
        ellipticModeIntegrand]
      rw [mul_div_cancel_left₀ v hsqrtNe]
    · have hw : (Real.sqrt lambda * v, u) ∉ cartesianEnergyDisk h := by
        exact fun H => hv ((hmem u v).mp H)
      simp only [D, G, Set.indicator_of_notMem hw, Set.indicator_of_notMem hv]
  have hGint : Integrable G := by
    exact (ellipticModeIntegrableOn alpha beta lambda hh hlambda).integrable_indicator
      (measurableSet_ellipticEnergyDisk lambda h)
  have hDint : Integrable D := by
    exact (diskScaledModeIntegrableOn alpha beta lambda hh).integrable_indicator
      (measurableSet_cartesianEnergyDisk h)
  have hGFubini : (∫ z : ℝ × ℝ, G z) = ∫ u : ℝ, ∫ v : ℝ, G (u, v) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod G (by simpa only [Measure.volume_eq_prod] using hGint)
  have hDFubini : (∫ z : ℝ × ℝ, D z) = ∫ u : ℝ, ∫ w : ℝ, D (w, u) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod_symm D (by simpa only [Measure.volume_eq_prod] using hDint)
  have hinner : ∀ u : ℝ,
      (∫ v : ℝ, G (u, v)) =
        (Real.sqrt lambda)⁻¹ * ∫ w : ℝ, D (w, u) := by
    intro u
    have H := Measure.integral_comp_mul_left
      (fun w : ℝ => D (w, u)) (Real.sqrt lambda)
    have hcomp : (fun v : ℝ => D (Real.sqrt lambda * v, u)) =
        fun v : ℝ => G (u, v) := by
      funext v
      exact hpoint u v
    rw [hcomp] at H
    simpa [abs_inv, abs_of_pos hsqrtPos, smul_eq_mul] using H
  calc
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        ellipticModeIntegrand alpha beta z) = ∫ z : ℝ × ℝ, G z := by
      change (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
        ellipticModeIntegrand alpha beta z) =
        ∫ z : ℝ × ℝ,
          (ellipticEnergyDisk lambda h).indicator (ellipticModeIntegrand alpha beta) z
      rw [integral_indicator (measurableSet_ellipticEnergyDisk lambda h)]
    _ = ∫ u : ℝ, ∫ v : ℝ, G (u, v) := hGFubini
    _ = ∫ u : ℝ, (Real.sqrt lambda)⁻¹ * ∫ w : ℝ, D (w, u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = (Real.sqrt lambda)⁻¹ * ∫ u : ℝ, ∫ w : ℝ, D (w, u) := by
      rw [integral_const_mul]
    _ = (Real.sqrt lambda)⁻¹ * ∫ z : ℝ × ℝ, D z := by rw [hDFubini]
    _ = (Real.sqrt lambda)⁻¹ *
        ∫ z : ℝ × ℝ in cartesianEnergyDisk h,
          Real.cos (alpha * Real.arcsin z.2) *
            Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda)) := by
      change (Real.sqrt lambda)⁻¹ * (∫ z : ℝ × ℝ,
        (cartesianEnergyDisk h).indicator (fun z =>
          Real.cos (alpha * Real.arcsin z.2) *
            Real.cos (beta * Real.arcsin (z.1 / Real.sqrt lambda))) z) = _
      rw [integral_indicator (measurableSet_cartesianEnergyDisk h)]

/-- The paper's area-normalized mode integral on the original ellipse. -/
noncomputable def normalizedEllipticModeIntegral
    (alpha beta lambda h : ℝ) : ℝ :=
  (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
    ellipticModeIntegrand alpha beta z) /
    (2 * Real.pi * h / Real.sqrt lambda)

/-- Combining the anisotropic Jacobian with the disk theorem gives the exact unnormalized
ellipse-mode formula in Paper Eq. (3.12). -/
theorem ellipticModeIntegral_eq_area_mul_analyticKernel
    {alpha beta lambda h : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in ellipticEnergyDisk lambda h,
      ellipticModeIntegrand alpha beta z) =
      (2 * Real.pi * h / Real.sqrt lambda) *
        analyticKernel alpha beta lambda h := by
  have hscale := ellipticModeIntegral_eq_inv_sqrt_mul_disk
    alpha beta lambda hh hlambda
  have hkernel := normalizedModeDiskIntegral_eq_analyticKernel
    halpha_pos halpha_one hbeta_pos hbeta_one hlambda hh hhq
  unfold normalizedModeDiskIntegral at hkernel
  have hC : 2 * Real.pi * h ≠ 0 := by positivity
  have hD := (div_eq_iff hC).mp hkernel
  rw [hscale, hD, div_eq_mul_inv]
  ring

/-- After division by the ellipse area factor, the original ellipse mode is exactly the analytic
kernel used by the rank theorem. -/
theorem normalizedEllipticModeIntegral_eq_analyticKernel
    {alpha beta lambda h : ℝ}
    (halpha_pos : 0 < alpha) (halpha_one : alpha < 1)
    (hbeta_pos : 0 < beta) (hbeta_one : beta < 1)
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    normalizedEllipticModeIntegral alpha beta lambda h =
      analyticKernel alpha beta lambda h := by
  rw [normalizedEllipticModeIntegral,
    ellipticModeIntegral_eq_area_mul_analyticKernel
      halpha_pos halpha_one hbeta_pos hbeta_one hlambda hh hhq]
  have hsqrt : Real.sqrt lambda ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)).ne'
  field_simp [Real.pi_ne_zero, hh.ne', hsqrt]

end Hilbert16
