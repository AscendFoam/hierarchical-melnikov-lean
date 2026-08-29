import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option autoImplicit false

namespace Hilbert16

open Filter
open scoped Topology

/-- A continuous real-linear endomorphism of `ℝ` is invertible as soon as it does not kill `1`. -/
theorem ContinuousLinearMap.isInvertible_of_apply_one_ne_zero
    (f : ℝ →L[ℝ] ℝ) (hf : f 1 ≠ 0) : f.IsInvertible := by
  let c : ℝˣ := Units.mk0 (f 1) hf
  refine ⟨ContinuousLinearEquiv.smulLeft c, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change (c : ℝ) * x = f x
  calc
    (c : ℝ) * x = x * f 1 := by simp [c, mul_comm]
    _ = x • f 1 := by rw [smul_eq_mul]
    _ = f (x • (1 : ℝ)) := (f.map_smul x 1).symm
    _ = f x := by simp

/-- Local data supplied by the implicit-function theorem for a scalar zero whose derivative in the
second variable is invertible. The final field is the local uniqueness statement, not merely the
existence of a selected root branch. -/
structure LocalZeroContinuation (F : ℝ × ℝ → ℝ) (u : ℝ × ℝ) where
  root : ℝ → ℝ
  root_at : root u.1 = u.2
  contDiffAt_root : ContDiffAt ℝ 1 root u.1
  eventually_zero : ∀ᶠ mu in 𝓝 u.1, F (mu, root mu) = 0
  eventually_unique : ∀ᶠ v in 𝓝 u, F v = 0 ↔ root v.1 = v.2

/-- A `C¹` scalar equation with an invertible partial derivative in its second variable has a
locally unique `C¹` zero branch. -/
noncomputable def ContDiffAt.localZeroContinuation
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} (hF : ContDiffAt ℝ 1 F u)
    (hzero : F u = 0)
    (hinv : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    LocalZeroContinuation F u where
  root := hF.implicitFunction one_ne_zero hinv
  root_at := hF.implicitFunction_apply_self one_ne_zero hinv
  contDiffAt_root := hF.contDiffAt_implicitFunction one_ne_zero hinv
  eventually_zero := by
    filter_upwards [hF.eventually_apply_implicitFunction one_ne_zero hinv] with mu hmu
    simpa [hzero] using hmu
  eventually_unique := by
    filter_upwards [hF.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv] with v hv
    simpa [hzero] using hv

/-- Scalar specialization of `localZeroContinuation`: it is enough to check that the partial
Fréchet derivative in the root variable is nonzero on `1`. -/
noncomputable def ContDiffAt.localZeroContinuation_of_partial_ne_zero
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} (hF : ContDiffAt ℝ 1 F u)
    (hzero : F u = 0)
    (hpartial :
      (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1 ≠ 0) :
    LocalZeroContinuation F u :=
  ContDiffAt.localZeroContinuation hF hzero
    (ContinuousLinearMap.isInvertible_of_apply_one_ne_zero _ hpartial)

/-- Derivative-level scalar interface: a nonzero ordinary derivative of the second-variable slice
supplies the invertibility hypothesis required by the implicit-function theorem. -/
noncomputable def ContDiffAt.localZeroContinuation_of_hasDerivAt
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} {d : ℝ} (hF : ContDiffAt ℝ 1 F u)
    (hzero : F u = 0) (hslice : HasDerivAt (fun h : ℝ => F (u.1, h)) d u.2)
    (hd : d ≠ 0) : LocalZeroContinuation F u := by
  apply ContDiffAt.localZeroContinuation_of_partial_ne_zero hF hzero
  have hfromF : HasDerivAt (fun h : ℝ => F (u.1, h))
      ((fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1) u.2 := by
    simpa [Function.comp_def] using
      ((hF.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp u.2
        (hasFDerivAt_prodMk_right u.1 u.2)).hasDerivAt
  rw [hfromF.unique hslice]
  exact hd

/-- Along any local zero branch supplied above, the second-variable derivative remains nonzero in
a common neighborhood of the base parameter. -/
theorem LocalZeroContinuation.eventually_hasDerivAt_slice_ne_zero
    {F : ℝ × ℝ → ℝ} {u : ℝ × ℝ} {d : ℝ} (C : LocalZeroContinuation F u)
    (hF : ContDiffAt ℝ 1 F u)
    (hslice : HasDerivAt (fun h : ℝ => F (u.1, h)) d u.2) (hd : d ≠ 0) :
    ∀ᶠ mu in 𝓝 u.1, ∃ dmu : ℝ, dmu ≠ 0 ∧
      HasDerivAt (fun h : ℝ => F (mu, h)) dmu (C.root mu) := by
  let g : ℝ → ℝ × ℝ := fun mu => (mu, C.root mu)
  have hg : Tendsto g (𝓝 u.1) (𝓝 u) := by
    have hpair : ContinuousAt g u.1 :=
      continuousAt_id.prodMk C.contDiffAt_root.continuousAt
    have hgu : g u.1 = u := by
      exact Prod.ext rfl C.root_at
    rw [← hgu]
    exact hpair
  let dh : ℝ × ℝ → ℝ := fun v =>
    (fderiv ℝ F v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1
  have hdhAt : dh u = d := by
    have hfromF : HasDerivAt (fun h : ℝ => F (u.1, h)) (dh u) u.2 := by
      simpa [dh, Function.comp_def] using
        ((hF.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp u.2
          (hasFDerivAt_prodMk_right u.1 u.2)).hasDerivAt
    exact hfromF.unique hslice
  have hdhContinuous : ContinuousAt dh u := by
    have happly : ContinuousAt (fun v : ℝ × ℝ =>
        (fderiv ℝ F v) ((0 : ℝ), (1 : ℝ))) u :=
      (hF.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
    simpa [dh, ContinuousLinearMap.comp_apply] using happly
  have hdhTendsto : Tendsto (fun mu => dh (g mu)) (𝓝 u.1) (𝓝 d) := by
    change Tendsto (dh ∘ g) (𝓝 u.1) (𝓝 d)
    rw [← hdhAt]
    exact hdhContinuous.tendsto.comp hg
  have hdhNe : ∀ᶠ mu in 𝓝 u.1, dh (g mu) ≠ 0 :=
    hdhTendsto.eventually_ne hd
  have hcontDiff : ∀ᶠ mu in 𝓝 u.1, ContDiffAt ℝ 1 F (g mu) :=
    hg.eventually (hF.eventually (by simp))
  filter_upwards [hdhNe, hcontDiff] with mu hne hlocal
  refine ⟨dh (g mu), hne, ?_⟩
  simpa [dh, g, Function.comp_def] using
    ((hlocal.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp (C.root mu)
      (hasFDerivAt_prodMk_right mu (C.root mu))).hasDerivAt

end Hilbert16
