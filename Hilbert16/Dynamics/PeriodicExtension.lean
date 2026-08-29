import Hilbert16.Foundations.PeriodicOrbit
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

namespace Hilbert16

open Set Filter Function Int
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Repeat a closed unit-length segment on the whole real line. -/
private noncomputable def unitPeriodicExtension (c : ℝ → E) (t : ℝ) : E :=
  c (Int.fract t)

private theorem unitPeriodicExtension_periodic (c : ℝ → E) :
    Function.Periodic (unitPeriodicExtension c) 1 := by
  exact (Int.fract_periodic ℝ).comp c

private theorem continuous_unitPeriodicExtension {c : ℝ → E}
    (hc : ContinuousOn c (Set.Icc 0 1)) (hclose : c 1 = c 0) :
    Continuous (unitPeriodicExtension c) := by
  change Continuous (fun t : ℝ => c (Int.fract t))
  simpa [Function.comp_def] using hc.comp_fract'' hclose.symm

private theorem eventually_floor_eq_of_not_int {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    ∀ᶠ y in 𝓝 x, ⌊y⌋ = ⌊x⌋ := by
  have hIco : Set.Ico (⌊x⌋ : ℝ) ((⌊x⌋ : ℝ) + 1) ∈ 𝓝 x := by
    apply Ico_mem_nhds
    · exact (floor_le x).lt_of_ne (Ne.symm hx)
    · exact lt_floor_add_one x
  filter_upwards [hIco] with y hy
  exact floor_eq_on_Ico _ _ hy

/-- The only derivative issue in periodic repetition is an integer seam.
The endpoint equality and equal endpoint velocity make the two one-sided
derivatives glue. -/
private theorem unitPeriodicExtension_hasDerivAt
    {c : ℝ → E} {V : E → E}
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt c (V (c s)) s)
    (hclose : c 1 = c 0) :
    ∀ t : ℝ, HasDerivAt (unitPeriodicExtension c)
      (V (unitPeriodicExtension c t)) t := by
  intro t
  by_cases htInt : t = (⌊t⌋ : ℝ)
  · let n : ℤ := ⌊t⌋
    have ht : t = (n : ℝ) := htInt
    have hrightFloor : ∀ᶠ s in 𝓝[≥] t, ⌊s⌋ = n := by
      simpa [ht] using (tendsto_floor_right_pure n)
    have hrightEq : unitPeriodicExtension c =ᶠ[𝓝[≥] t]
        fun s => c (s - (n : ℝ)) := by
      filter_upwards [hrightFloor] with s hs
      simp [unitPeriodicExtension, Int.fract, hs]
    have hunitAt : unitPeriodicExtension c t = c 0 := by
      simp [unitPeriodicExtension, ht]
    have hrightArg : t - (n : ℝ) = 0 := by simp [ht]
    have hrightBase : HasDerivAt c (V (c 0)) (t - (n : ℝ)) := by
      simpa [hrightArg] using hc 0 ⟨le_rfl, zero_le_one⟩
    have hrightModel : HasDerivAt (fun s => c (s - (n : ℝ))) (V (c 0)) t :=
      HasDerivAt.comp_sub_const t (n : ℝ) hrightBase
    have hright : HasDerivWithinAt (unitPeriodicExtension c) (V (c 0))
        (Set.Ici t) t :=
      hrightModel.hasDerivWithinAt.congr_of_eventuallyEq hrightEq <| by
        exact hunitAt.trans (congrArg c hrightArg).symm
    have hleftFloor : ∀ᶠ s in 𝓝[<] t, ⌊s⌋ = n - 1 := by
      simpa [ht] using (tendsto_floor_left_pure_sub_one n)
    have hleftEq : unitPeriodicExtension c =ᶠ[𝓝[<] t]
        fun s => c (s - ((n : ℝ) - 1)) := by
      filter_upwards [hleftFloor] with s hs
      simp [unitPeriodicExtension, Int.fract, hs]
    have hleftArg : t - ((n : ℝ) - 1) = 1 := by simp [ht]
    have hleftBase : HasDerivAt c (V (c 0))
        (t - ((n : ℝ) - 1)) := by
      have hc1 := hc 1 ⟨zero_le_one, le_rfl⟩
      rw [hclose] at hc1
      simpa [hleftArg] using hc1
    have hleftModel : HasDerivAt (fun s => c (s - ((n : ℝ) - 1)))
        (V (c 0)) t :=
      HasDerivAt.comp_sub_const t ((n : ℝ) - 1) hleftBase
    have hleft : HasDerivWithinAt (unitPeriodicExtension c) (V (c 0))
        (Set.Iio t) t :=
      hleftModel.hasDerivWithinAt.congr_of_eventuallyEq hleftEq <| by
        rw [hunitAt, hleftArg]
        exact hclose.symm
    have hall := hleft.union hright
    rw [Set.Iio_union_Ici] at hall
    simpa [hunitAt] using hall
  · have hfloor : ∀ᶠ s in 𝓝 t, ⌊s⌋ = ⌊t⌋ :=
      eventually_floor_eq_of_not_int htInt
    let r : ℝ := Int.fract t
    have hr0 : 0 < r := Int.fract_pos.2 htInt
    have hr1 : r < 1 := Int.fract_lt_one t
    have heq : unitPeriodicExtension c =ᶠ[𝓝 t]
        fun s => c (s - (⌊t⌋ : ℝ)) := by
      filter_upwards [hfloor] with s hs
      simp [unitPeriodicExtension, Int.fract, hs]
    have harg : t - (⌊t⌋ : ℝ) = r := by rfl
    have hbase : HasDerivAt c (V (c r)) (t - (⌊t⌋ : ℝ)) := by
      simpa [harg] using hc r ⟨hr0.le, hr1.le⟩
    have hmodel : HasDerivAt (fun s => c (s - (⌊t⌋ : ℝ)))
        (V (c r)) t :=
      HasDerivAt.comp_sub_const t (⌊t⌋ : ℝ) hbase
    have hext : unitPeriodicExtension c t = c r := rfl
    simpa [hext] using hmodel.congr_of_eventuallyEq heq

/-- Repeat a closed segment of physical length `T` on the whole real line. -/
noncomputable def periodicExtension (T : ℝ) (c : ℝ → E) (t : ℝ) : E :=
  unitPeriodicExtension (fun s => c (T * s)) (t / T)

@[simp]
theorem periodicExtension_zero (T : ℝ) (c : ℝ → E) :
    periodicExtension T c 0 = c 0 := by
  simp [periodicExtension, unitPeriodicExtension]

theorem periodicExtension_periodic {T : ℝ} (hT : T ≠ 0) (c : ℝ → E) :
    Function.Periodic (periodicExtension T c) T := by
  intro t
  unfold periodicExtension
  have hdiv : (t + T) / T = t / T + 1 := by field_simp
  rw [hdiv]
  exact unitPeriodicExtension_periodic (fun s => c (T * s)) (t / T)

theorem continuous_periodicExtension {T : ℝ} (hT : 0 < T) {c : ℝ → E}
    (hc : ContinuousOn c (Set.Icc 0 T)) (hclose : c T = c 0) :
    Continuous (periodicExtension T c) := by
  have hscaled : ContinuousOn (fun s : ℝ => c (T * s)) (Set.Icc 0 1) := by
    exact hc.comp (continuous_const.mul continuous_id).continuousOn fun s hs =>
      ⟨mul_nonneg hT.le hs.1, by nlinarith [hs.2]⟩
  have hscaledClose : c (T * 1) = c (T * 0) := by simpa using hclose
  have hunit := continuous_unitPeriodicExtension hscaled hscaledClose
  exact hunit.comp (continuous_id.div_const T)

/-- Every point of the global periodic extension already occurs on the
normalized closed segment `s ↦ c (T * s)`, `0 ≤ s ≤ 1`. -/
theorem range_periodicExtension_subset_of_scaled_Icc
    {T : ℝ} (c : ℝ → E) (U : Set E)
    (hscaled : ∀ s ∈ Set.Icc (0 : ℝ) 1, c (T * s) ∈ U) :
    Set.range (periodicExtension T c) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  exact hscaled (Int.fract (t / T))
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem periodicExtension_hasDerivAt
    {T : ℝ} (hT : 0 < T) {c : ℝ → E} {V : E → E}
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivAt c (V (c s)) s)
    (hclose : c T = c 0) :
    ∀ t : ℝ, HasDerivAt (periodicExtension T c)
      (V (periodicExtension T c t)) t := by
  let scaled : ℝ → E := fun s => c (T * s)
  let scaledV : E → E := fun z => T • V z
  have hscaled : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt scaled (scaledV (scaled s)) s := by
    intro s hs
    have hTs : T * s ∈ Set.Icc (0 : ℝ) T :=
      ⟨mul_nonneg hT.le hs.1, by nlinarith [hs.2]⟩
    have hinner : HasDerivAt (fun u : ℝ => T * u) T s :=
      by simpa using (hasDerivAt_id s).const_mul T
    change HasDerivAt scaled (T • V (c (T * s))) s
    simpa only [scaled, Function.comp_def] using (hc (T * s) hTs).scomp s hinner
  have hscaledClose : scaled 1 = scaled 0 := by simpa [scaled] using hclose
  have hunit := unitPeriodicExtension_hasDerivAt hscaled hscaledClose
  intro t
  have houter := hunit (t / T)
  have hinner : HasDerivAt (fun u : ℝ => u / T) T⁻¹ t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const T⁻¹
  have hcomp := houter.scomp t hinner
  have hcancel : T⁻¹ • (T • V (periodicExtension T c t)) =
      V (periodicExtension T c t) := by
    rw [← mul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  change HasDerivAt (periodicExtension T c)
    (T⁻¹ • (T • V (periodicExtension T c t))) t at hcomp
  exact hcomp.congr_deriv hcancel

/-- A nonconstant closed integral-curve segment extends to a global periodic
integral curve of the same autonomous vector field. -/
theorem isPeriodicIntegralCurve_periodicExtension
    {X : PhaseSpace → PhaseSpace} {T : ℝ} (hT : 0 < T)
    {c : ℝ → PhaseSpace}
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt c (X (c s)) s)
    (hclose : c T = c 0)
    (hnonconst : ∃ s ∈ Set.Icc (0 : ℝ) T, c s ≠ c 0) :
    IsPeriodicIntegralCurve X (periodicExtension T c) := by
  refine ⟨T, hT, ?_, periodicExtension_periodic hT.ne' c, ?_⟩
  · intro t
    simpa [autonomousField] using periodicExtension_hasDerivAt hT hc hclose t
  · rcases hnonconst with ⟨s, hs, hsc⟩
    have hsne : s ≠ T := by
      intro hsT
      subst s
      exact hsc hclose
    have hsdiv : s / T ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hT.le, (div_lt_one hT).2 (hs.2.lt_of_ne hsne)⟩
    refine ⟨s, ?_⟩
    have hextS : periodicExtension T c s = c s := by
      simp [periodicExtension, unitPeriodicExtension,
        Int.fract_eq_self.2 hsdiv]
      field_simp
    have hext0 : periodicExtension T c 0 = c 0 := by
      simp [periodicExtension, unitPeriodicExtension]
    rwa [hextS, hext0]

end Hilbert16
