import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Hilbert16

open Filter MeasureTheory Set
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The derivative in the parameter variable of a function on `E × ℝ`. -/
noncomputable def parameterFDeriv (f : E × ℝ → ℝ) (x : E) (t : ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ f (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [FiniteDimensional ℝ E] in
theorem continuous_parameterFDeriv {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    Continuous (Function.uncurry (parameterFDeriv f)) := by
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

/-- A jointly `C¹` integrand remains `C¹` after integration over fixed finite
endpoints.  This packages the compact uniform derivative bound needed by
Mathlib's differentiation-under-the-integral theorem. -/
theorem contDiff_parametricIntervalIntegral_const
    (f : E → ℝ → ℝ) (hf : ContDiff ℝ 1 f.uncurry) (a b : ℝ) :
    ContDiff ℝ 1 (fun x : E ↦ ∫ t in a..b, f x t) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨(fun x ↦ ∫ t in a..b, parameterFDeriv f.uncurry x t), ?_, ?_⟩
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_parameterFDeriv hf) a b
  · intro x₀
    let s : Set E := Metric.closedBall x₀ 1
    let K : Set (E × ℝ) := s ×ˢ Set.uIcc a b
    have hK : IsCompact K :=
      IsCompact.prod (isCompact_closedBall x₀ 1) isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (continuous_parameterFDeriv hf).continuousOn
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := s) (bound := fun _ ↦ C)
    · exact Metric.closedBall_mem_nhds x₀ zero_lt_one
    · exact Eventually.of_forall fun x ↦
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    · exact (hf.continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    · exact ((continuous_parameterFDeriv hf).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx ↦ ?_
      exact hC (x, t) ⟨hx, uIoc_subset_uIcc ht⟩
    · exact continuous_const.intervalIntegrable a b
    · refine Eventually.of_forall fun t _ht x _hx ↦ ?_
      have hfull : HasFDerivAt f.uncurry (fderiv ℝ f.uncurry (x, t)) (x, t) :=
        (hf.differentiable_one.differentiableAt).hasFDerivAt
      simpa [parameterFDeriv, Function.comp_def] using
        hfull.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

/-- Local fixed-endpoint version.  It is enough for the integrand to be
`C¹` on one open tube around the compact parameter fiber
`{x₀} × [[a,b]]`. -/
theorem contDiffAt_parametricIntervalIntegral_const_of_contDiffOn
    (f : E → ℝ → ℝ) {U : Set (E × ℝ)} {x₀ : E} (a b : ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f.uncurry U)
    (hsegment : ({x₀} : Set E) ×ˢ Set.uIcc a b ⊆ U) :
    ContDiffAt ℝ 1 (fun x : E ↦ ∫ t in a..b, f x t) x₀ := by
  obtain ⟨v, w, hvOpen, hwOpen, hxv, hIw, hvwU⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hsegment
  have hx₀v : x₀ ∈ v := hxv (Set.mem_singleton x₀)
  have hvNhd : v ∈ nhds x₀ := hvOpen.mem_nhds hx₀v
  let d : E → E →L[ℝ] ℝ := fun x ↦
    ∫ t in a..b, parameterFDeriv f.uncurry x t
  have hdContinuousOn : ContinuousOn d v := by
    rw [continuousOn_iff_continuous_domRestrict]
    let clamp : ℝ → Set.Icc (min a b) (max a b) :=
      Set.projIcc (min a b) (max a b) min_le_max
    let dc : v → ℝ → E →L[ℝ] ℝ := fun x t ↦
      parameterFDeriv f.uncurry (x : E) (clamp t : ℝ)
    have hdc : Continuous dc.uncurry := by
      rw [continuous_iff_continuousAt]
      intro z
      have hclamp : (clamp z.2 : ℝ) ∈ Set.uIcc a b := by
        simpa only [← Icc_min_max] using (clamp z.2).property
      have hzU : ((z.1 : E), (clamp z.2 : ℝ)) ∈ U :=
        hvwU ⟨z.1.property, hIw hclamp⟩
      have hfd : ContinuousAt (fderiv ℝ f.uncurry)
          ((z.1 : E), (clamp z.2 : ℝ)) :=
        ((hf _ hzU).contDiffAt (hU.mem_nhds hzU)).continuousAt_fderiv one_ne_zero
      have hinput : ContinuousAt
          (fun q : v × ℝ ↦ ((q.1 : E), (clamp q.2 : ℝ))) z :=
        (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
          ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)).continuousAt)
      have hfdcomp : ContinuousAt
          (fun q : v × ℝ ↦ fderiv ℝ f.uncurry
            ((q.1 : E), (clamp q.2 : ℝ))) z := by
        exact Filter.Tendsto.comp hfd hinput
      exact hfdcomp.clm_comp continuousAt_const
    have hdcIntegral : Continuous (fun x : v ↦ ∫ t in a..b, dc x t) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hdc a b
    have heq : (fun x : v ↦ ∫ t in a..b, dc x t) = v.domRestrict d := by
      funext x
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [dc]
      have ht' : t ∈ Set.Icc (min a b) (max a b) := by
        simpa only [Icc_min_max] using ht
      have hclamp : (clamp t : ℝ) = t := by
        exact congrArg Subtype.val (Set.projIcc_of_mem min_le_max ht')
      rw [hclamp]
    rwa [← heq]
  have hdContinuousAt : ContinuousAt d x₀ :=
    (hdContinuousOn x₀ hx₀v).continuousAt hvNhd
  rw [contDiffAt_one_iff]
  refine ⟨d, v, hvNhd, hdContinuousOn, ?_⟩
  intro x hxv'
  obtain ⟨ε, hεpos, hεv⟩ := Metric.isOpen_iff.mp hvOpen x hxv'
  let s : Set E := Metric.closedBall x (ε / 2)
  let K : Set (E × ℝ) := s ×ˢ Set.uIcc a b
  have hsSub : s ⊆ v := by
    intro y hy
    apply hεv
    rw [Metric.mem_closedBall] at hy
    exact hy.trans_lt (half_lt_self hεpos)
  have hKsub : K ⊆ U :=
    (Set.prod_mono hsSub hIw).trans hvwU
  have hK : IsCompact K :=
    IsCompact.prod (isCompact_closedBall x (ε / 2)) isCompact_uIcc
  have hpContinuousOn : ContinuousOn
      (Function.uncurry (parameterFDeriv f.uncurry)) U := by
    exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hpContinuousOn.mono hKsub)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := s) (bound := fun _ ↦ C)
  · exact Metric.closedBall_mem_nhds x (half_pos hεpos)
  · refine mem_of_superset (Metric.closedBall_mem_nhds x (half_pos hεpos)) ?_
    intro y hy
    have hyCont : ContinuousOn (f y) (Set.uIcc a b) := by
      intro t ht
      have hytU : (y, t) ∈ U := hKsub ⟨hy, ht⟩
      simpa [Function.comp_def] using ((hf _ hytU).continuousWithinAt.comp
        (continuousWithinAt_const.prodMk continuousWithinAt_id)
        (fun _ ht' ↦ hKsub ⟨hy, ht'⟩))
    exact hyCont.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc uIoc_subset_uIcc
  · have hxCont : ContinuousOn (f x) (Set.uIcc a b) := by
      intro t ht
      have hxtU : (x, t) ∈ U := hKsub
        ⟨Metric.mem_closedBall_self (le_of_lt (half_pos hεpos)), ht⟩
      simpa [Function.comp_def] using ((hf _ hxtU).continuousWithinAt.comp
        (continuousWithinAt_const.prodMk continuousWithinAt_id)
        (fun _ ht' ↦ hKsub ⟨Metric.mem_closedBall_self
          (le_of_lt (half_pos hεpos)), ht'⟩))
    exact hxCont.intervalIntegrable
  · have hpSlice : ContinuousOn (parameterFDeriv f.uncurry x)
        (Set.uIcc a b) :=
      (hpContinuousOn.mono hKsub).uncurry_left x
        (Metric.mem_closedBall_self (le_of_lt (half_pos hεpos)))
    exact hpSlice.aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc uIoc_subset_uIcc
  · refine Eventually.of_forall fun t ht y hy ↦ ?_
    exact hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
  · exact continuous_const.intervalIntegrable a b
  · refine Eventually.of_forall fun t ht y hy ↦ ?_
    have hytU : (y, t) ∈ U := hKsub ⟨hy, uIoc_subset_uIcc ht⟩
    have hfull : HasFDerivAt f.uncurry (fderiv ℝ f.uncurry (y, t)) (y, t) :=
      ((hf _ hytU).contDiffAt (hU.mem_nhds hytU)).differentiableAt_one.hasFDerivAt
    simpa [parameterFDeriv, Function.comp_def] using
      hfull.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)

/-- A jointly `C¹` integrand with a `C¹` upper endpoint defines a `C¹`
parameter integral.  Rescaling the interval to `[0,1]` reduces this to the
fixed-endpoint theorem above and works uniformly for positive, zero, and
negative endpoint values. -/
theorem contDiff_parametricIntervalIntegral
    (f : E → ℝ → ℝ) (hf : ContDiff ℝ 1 f.uncurry)
    (b : E → ℝ) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (fun x : E ↦ ∫ t in 0..b x, f x t) := by
  let g : E → ℝ → ℝ := fun x r ↦ b x * f x (b x * r)
  have hb' : ContDiff ℝ 1 (fun z : E × ℝ ↦ b z.1) := hb.comp contDiff_fst
  have harg : ContDiff ℝ 1 (fun z : E × ℝ ↦ (z.1, b z.1 * z.2)) :=
    contDiff_fst.prodMk (hb'.mul contDiff_snd)
  have hg : ContDiff ℝ 1 g.uncurry := hb'.mul (hf.comp harg)
  have hfixed := contDiff_parametricIntervalIntegral_const g hg 0 1
  convert hfixed using 1
  funext x
  change (∫ t in 0..b x, f x t) = ∫ r in 0..1, b x * f x (b x * r)
  rw [intervalIntegral.integral_const_mul]
  simpa using (intervalIntegral.smul_integral_comp_mul_left (f x) (b x)
    (a := 0) (b := 1)).symm

/-- Local variable-endpoint version.  The open set only has to cover the
compact fiber from time `0` to the base endpoint `b x₀`; both the endpoint
and the parameter are then allowed to vary in a sufficiently small
neighborhood. -/
theorem contDiffAt_parametricIntervalIntegral_of_contDiffOn
    (f : E → ℝ → ℝ) {U : Set (E × ℝ)} {x₀ : E}
    (b : E → ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f.uncurry U)
    (hb : ContDiffAt ℝ 1 b x₀)
    (hsegment : ({x₀} : Set E) ×ˢ Set.uIcc 0 (b x₀) ⊆ U) :
    ContDiffAt ℝ 1 (fun x : E ↦ ∫ t in 0..b x, f x t) x₀ := by
  obtain ⟨V, hVNhd, hbV⟩ := hb.contDiffOn le_rfl (by simp)
  obtain ⟨O, hOV, hOOpen, hx₀O⟩ := mem_nhds_iff.mp hVNhd
  have hbO : ContDiffOn ℝ 1 b O := hbV.mono hOV
  let ψ : E × ℝ → E × ℝ := fun z ↦ (z.1, b z.1 * z.2)
  let U' : Set (E × ℝ) := (O ×ˢ Set.univ) ∩ ψ ⁻¹' U
  have hU' : IsOpen U' := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hbAt : ContDiffAt ℝ 1 b z.1 :=
      (hbO z.1 hz.1.1).contDiffAt (hOOpen.mem_nhds hz.1.1)
    have hψAt : ContDiffAt ℝ 1 ψ z := by
      exact contDiffAt_fst.prodMk
        ((hbAt.comp z contDiffAt_fst).mul contDiffAt_snd)
    exact inter_mem
      ((hOOpen.prod isOpen_univ).mem_nhds hz.1)
      (hψAt.continuousAt (hU.mem_nhds hz.2))
  let g : E → ℝ → ℝ := fun x r ↦ b x * f x (b x * r)
  have hg : ContDiffOn ℝ 1 g.uncurry U' := by
    intro z hz
    have hbAt : ContDiffAt ℝ 1 b z.1 :=
      (hbO z.1 hz.1.1).contDiffAt (hOOpen.mem_nhds hz.1.1)
    have hbComp : ContDiffAt ℝ 1 (fun q : E × ℝ ↦ b q.1) z :=
      hbAt.comp z contDiffAt_fst
    have hψAt : ContDiffAt ℝ 1 ψ z :=
      contDiffAt_fst.prodMk (hbComp.mul contDiffAt_snd)
    have hfAt : ContDiffAt ℝ 1 f.uncurry (ψ z) :=
      (hf _ hz.2).contDiffAt (hU.mem_nhds hz.2)
    change ContDiffWithinAt ℝ 1
      (fun q : E × ℝ ↦ b q.1 * f q.1 (b q.1 * q.2)) U' z
    exact (hbComp.mul (hfAt.comp z hψAt)).contDiffWithinAt
  have hgSegment : ({x₀} : Set E) ×ˢ Set.uIcc 0 1 ⊆ U' := by
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    have hxEq : x = x₀ := Set.mem_singleton_iff.mp hx
    subst x
    have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using hr
    have htime : b x₀ * r ∈ Set.uIcc 0 (b x₀) := by
      rw [← segment_eq_uIcc]
      simpa [AffineMap.lineMap_apply_ring, mul_comm] using
        (lineMap_mem_segment ℝ (0 : ℝ) (b x₀) hrIcc)
    exact ⟨⟨hx₀O, Set.mem_univ _⟩, hsegment ⟨Set.mem_singleton x₀, htime⟩⟩
  have hfixed := contDiffAt_parametricIntervalIntegral_const_of_contDiffOn
    g 0 1 hU' hg hgSegment
  convert hfixed using 1
  funext x
  change (∫ t in 0..b x, f x t) = ∫ r in 0..1, b x * f x (b x * r)
  rw [intervalIntegral.integral_const_mul]
  simpa using (intervalIntegral.smul_integral_comp_mul_left (f x) (b x)
    (a := 0) (b := 1)).symm

end Hilbert16
