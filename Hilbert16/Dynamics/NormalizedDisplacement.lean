import Hilbert16.Dynamics.SimpleRoot

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

end Hilbert16
