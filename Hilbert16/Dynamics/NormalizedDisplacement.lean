import Hilbert16.Dynamics.SimpleRoot
import Hilbert16.Foundations.PeriodicOrbit

set_option autoImplicit false

namespace Hilbert16

open Filter
open scoped Topology

/-- A return map reconstructed from a normalized displacement `D`, so that the unnormalized
displacement is exactly `mu * D (mu,h)`. -/
def normalizedReturnMap (D : ℝ × ℝ → ℝ) (mu h : ℝ) : ℝ :=
  h + mu * D (mu, h)

theorem normalizedReturnMap_fixed_of_zero {D : ℝ × ℝ → ℝ} {mu h : ℝ}
    (hzero : D (mu, h) = 0) : normalizedReturnMap D mu h = h := by
  simp [normalizedReturnMap, hzero]

theorem normalizedReturnMap_hasDerivAt {D : ℝ × ℝ → ℝ} {mu h d : ℝ}
    (hslice : HasDerivAt (fun e : ℝ => D (mu, e)) d h) :
    HasDerivAt (normalizedReturnMap D mu) (1 + mu * d) h := by
  rw [show normalizedReturnMap D mu =
      id + (fun e : ℝ => mu * D (mu, e)) by
    funext e
    rfl]
  exact (hasDerivAt_id h).add (hslice.const_mul mu)

theorem normalizedReturnMap_multiplier_ne_one {mu d : ℝ} (hmu : mu ≠ 0) (hd : d ≠ 0) :
    1 + mu * d ≠ 1 := by
  intro heq
  have hprod : mu * d = 0 := by linarith
  exact (mul_ne_zero hmu hd) hprod

/-- A nonzero parameter, a normalized-displacement zero, and a nonzero energy derivative give a
fixed point whose Poincaré multiplier is not `1`. -/
theorem normalizedReturnMap_fixed_and_hyperbolic
    {D : ℝ × ℝ → ℝ} {mu h d : ℝ} (hmu : mu ≠ 0)
    (hzero : D (mu, h) = 0) (hslice : HasDerivAt (fun e : ℝ => D (mu, e)) d h)
    (hd : d ≠ 0) :
    normalizedReturnMap D mu h = h ∧
      ∃ rho : ℝ, HasDerivAt (normalizedReturnMap D mu) rho h ∧ rho ≠ 1 := by
  refine ⟨normalizedReturnMap_fixed_of_zero hzero, 1 + mu * d, ?_, ?_⟩
  · exact normalizedReturnMap_hasDerivAt hslice
  · exact normalizedReturnMap_multiplier_ne_one hmu hd

/-- Complete local analytic closure of the simple-Melnikov-zero step. A `C¹` normalized
displacement whose unperturbed energy slice has a simple zero supplies a locally unique `C¹` root
branch; for every sufficiently small nonzero parameter, that root is a fixed point with multiplier
different from `1`. -/
theorem eventually_normalizedReturnMap_fixed_and_hyperbolic
    {D : ℝ × ℝ → ℝ} {h₀ d : ℝ} (hD : ContDiffAt ℝ 1 D (0, h₀))
    (hzero : D (0, h₀) = 0)
    (hslice : HasDerivAt (fun h : ℝ => D (0, h)) d h₀) (hd : d ≠ 0) :
    let C := ContDiffAt.localZeroContinuation_of_hasDerivAt hD hzero hslice hd
    ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      normalizedReturnMap D mu (C.root mu) = C.root mu ∧
        ∃ rho : ℝ, HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) ∧ rho ≠ 1 := by
  let C := ContDiffAt.localZeroContinuation_of_hasDerivAt hD hzero hslice hd
  change ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
    normalizedReturnMap D mu (C.root mu) = C.root mu ∧
      ∃ rho : ℝ, HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) ∧ rho ≠ 1
  have hderiv := C.eventually_hasDerivAt_slice_ne_zero hD hslice hd
  filter_upwards [C.eventually_zero, hderiv] with mu hmuZero hmuDeriv
  intro hmu
  rcases hmuDeriv with ⟨dmu, hdmu, hsliceMu⟩
  exact normalizedReturnMap_fixed_and_hyperbolic hmu hmuZero hsliceMu hdmu

/-- Along any continuous root branch through parameter zero, the derivative
of the planar normalized Poincaré map is positive for all sufficiently small
parameters.  Its explicit value tends to `1`, because it is
`1 + mu * partial₂ D (mu, root mu)`. -/
theorem LocalZeroContinuation.eventually_normalizedReturnMap_multiplier_pos
    {D : ℝ × ℝ → ℝ} {h₀ : ℝ} (C : LocalZeroContinuation D (0, h₀))
    (hD : ContDiffAt ℝ 1 D (0, h₀)) :
    ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ rho : ℝ,
      HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) → 0 < rho := by
  let path : ℝ → ℝ × ℝ := fun mu => (mu, C.root mu)
  have hpath : Tendsto path (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ), h₀)) := by
    have hcont : ContinuousAt path 0 :=
      continuousAt_id.prodMk C.contDiffAt_root.continuousAt
    have hzero : path 0 = (0, h₀) := Prod.ext rfl C.root_at
    rw [← hzero]
    exact hcont
  let partial₂ : ℝ × ℝ → ℝ := fun v =>
    (fderiv ℝ D v ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1
  have hpartial₂ : ContinuousAt partial₂ (0, h₀) := by
    have happly : ContinuousAt (fun v : ℝ × ℝ =>
        (fderiv ℝ D v) ((0 : ℝ), (1 : ℝ))) (0, h₀) :=
      (hD.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
    simpa [partial₂, ContinuousLinearMap.comp_apply] using happly
  have hpartial₂Path : Tendsto (fun mu => partial₂ (path mu))
      (𝓝 (0 : ℝ)) (𝓝 (partial₂ (0, h₀))) :=
    hpartial₂.tendsto.comp hpath
  have hrhoTendsto : Tendsto
      (fun mu => 1 + mu * partial₂ (path mu))
      (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_id.mul hpartial₂Path)
  have hrhoPos : ∀ᶠ mu in 𝓝 (0 : ℝ),
      0 < 1 + mu * partial₂ (path mu) :=
    hrhoTendsto.eventually (isOpen_Ioi.mem_nhds
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num))
  have hcontDiff : ∀ᶠ mu in 𝓝 (0 : ℝ), ContDiffAt ℝ 1 D (path mu) :=
    hpath.eventually (hD.eventually (by simp))
  filter_upwards [hrhoPos, hcontDiff] with mu hpos hlocal
  intro rho hrho
  have hslice : HasDerivAt (fun h : ℝ => D (mu, h))
      (partial₂ (path mu)) (C.root mu) := by
    simpa [partial₂, path, Function.comp_def] using
      ((hlocal.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp (C.root mu)
        (hasFDerivAt_prodMk_right mu (C.root mu))).hasDerivAt
  have hcanonical := normalizedReturnMap_hasDerivAt hslice
  rw [hrho.unique hcanonical]
  exact hpos

/-- Standard one-dimensional spectral form of the simple-root persistence
theorem.  Positivity of the planar multiplier turns `rho ≠ 1` into the
standard condition `|rho| ≠ 1`. -/
theorem eventually_normalizedReturnMap_fixed_and_standardHyperbolic
    {D : ℝ × ℝ → ℝ} {h₀ d : ℝ} (hD : ContDiffAt ℝ 1 D (0, h₀))
    (hzero : D (0, h₀) = 0)
    (hslice : HasDerivAt (fun h : ℝ => D (0, h)) d h₀) (hd : d ≠ 0) :
    let C := ContDiffAt.localZeroContinuation_of_hasDerivAt hD hzero hslice hd
    ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      normalizedReturnMap D mu (C.root mu) = C.root mu ∧
        ∃ rho : ℝ, HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) ∧
          0 < rho ∧ rho ≠ 1 ∧ |rho| ≠ 1 := by
  let C := ContDiffAt.localZeroContinuation_of_hasDerivAt hD hzero hslice hd
  have hlegacy : ∀ᶠ mu in 𝓝 (0 : ℝ), mu ≠ 0 →
      normalizedReturnMap D mu (C.root mu) = C.root mu ∧
        ∃ rho : ℝ, HasDerivAt (normalizedReturnMap D mu) rho (C.root mu) ∧
          rho ≠ 1 := by
    simpa [C] using eventually_normalizedReturnMap_fixed_and_hyperbolic
      hD hzero hslice hd
  have hpos := C.eventually_normalizedReturnMap_multiplier_pos hD
  filter_upwards [hlegacy, hpos] with mu hmu hmuPos
  intro hmuNe
  rcases hmu hmuNe with ⟨hfixed, rho, hrho, hrhoNe⟩
  have hrhoPos : 0 < rho := hmuPos rho hrho
  exact ⟨hfixed, rho, hrho, hrhoPos, hrhoNe,
    abs_ne_one_of_pos_of_ne_one hrhoPos hrhoNe⟩

end Hilbert16
