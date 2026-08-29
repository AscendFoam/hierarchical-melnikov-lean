import Hilbert16.Hierarchy.ThreeAdicRealization

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter
open scoped BigOperators Topology

namespace Hilbert16

/-!
# The concrete three-adic hierarchy as an actual Melnikov displacement
-/

theorem threeAdicModeFrequencyPair_injective {r : ℕ} :
    Function.Injective (@threeAdicModeFrequencyPair r) := by
  rintro ⟨k, l, a, b⟩ ⟨k', l', a', b'⟩ hab
  have hcoord := Prod.ext_iff.mp hab
  have hk : k = k' := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (threeAdicFrequencyValue_ne_of_lt hlt k'.2 a a') hcoord.1
    · exact (threeAdicFrequencyValue_ne_of_lt hgt k.2 a' a) hcoord.1.symm
  subst k'
  have hl : l = l' := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (threeAdicFrequencyValue_ne_of_lt hlt l'.2 b b') hcoord.2
    · exact (threeAdicFrequencyValue_ne_of_lt hgt l.2 b' b) hcoord.2.symm
  subst l'
  have ha : a = a' := threeAdicFrequencyValue_injective hcoord.1
  have hb : b = b' := threeAdicFrequencyValue_injective hcoord.2
  subst a'
  subst b'
  rfl

/-- The finite support of all genuine three-adic tensor frequencies. -/
def threeAdicModeSupport (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ : Finset (ThreeAdicMode r)).image
    (@threeAdicModeFrequencyPair r)

theorem threeAdicModeFrequencyPair_mem_support {r : ℕ} (m : ThreeAdicMode r) :
    threeAdicModeFrequencyPair m ∈ threeAdicModeSupport r := by
  simp [threeAdicModeSupport]

/-- The public mode type is exactly the subtype of its frequency-pair support. -/
noncomputable def threeAdicModeSupportEquiv (r : ℕ) :
    ThreeAdicMode r ≃ ↥(threeAdicModeSupport r) :=
  Equiv.ofBijective
    (fun m => ⟨threeAdicModeFrequencyPair m,
      threeAdicModeFrequencyPair_mem_support m⟩)
    ⟨
      fun m n h => threeAdicModeFrequencyPair_injective (Subtype.ext_iff.mp h),
      fun ab => by
        rcases ab with ⟨ab, hab⟩
        simp only [threeAdicModeSupport, Finset.mem_image, Finset.mem_univ,
          true_and] at hab
        rcases hab with ⟨m, rfl⟩
        exact ⟨m, rfl⟩⟩

@[simp]
theorem threeAdicModeSupportEquiv_apply_val {r : ℕ} (m : ThreeAdicMode r) :
    (threeAdicModeSupportEquiv r m).1 = threeAdicModeFrequencyPair m := rfl

/-- Coefficients on natural frequency pairs induced by one public mode
coefficient family and hierarchy parameter. -/
noncomputable def threeAdicHierarchicalPairCoefficient (r : ℕ) (zeta : ℝ)
    (blockCoeff : ThreeAdicMode r → ℝ) (ab : ℕ × ℕ) : ℝ :=
  if hab : ab ∈ threeAdicModeSupport r then
    let m := (threeAdicModeSupportEquiv r).symm ⟨ab, hab⟩
    zeta ^ threeAdicTensorWeight (m.1, m.2.1) * blockCoeff m
  else 0

theorem threeAdicHierarchicalPairCoefficient_mode {r : ℕ} (zeta : ℝ)
    (blockCoeff : ThreeAdicMode r → ℝ) (m : ThreeAdicMode r) :
    threeAdicHierarchicalPairCoefficient r zeta blockCoeff
        (threeAdicModeFrequencyPair m) =
      zeta ^ threeAdicTensorWeight (m.1, m.2.1) * blockCoeff m := by
  unfold threeAdicHierarchicalPairCoefficient
  rw [dif_pos (threeAdicModeFrequencyPair_mem_support m)]
  change zeta ^ threeAdicTensorWeight
      (((threeAdicModeSupportEquiv r).symm (threeAdicModeSupportEquiv r m)).1,
        ((threeAdicModeSupportEquiv r).symm (threeAdicModeSupportEquiv r m)).2.1) *
      blockCoeff ((threeAdicModeSupportEquiv r).symm (threeAdicModeSupportEquiv r m)) = _
  rw [Equiv.symm_apply_apply]

theorem threeAdicModeSupport_frequency_bounds {r : ℕ}
    (ab : ℕ × ℕ) (hab : ab ∈ threeAdicModeSupport r) :
    0 < ab.1 ∧ ab.1 < 3 ^ r ∧ 0 < ab.2 ∧ ab.2 < 3 ^ r := by
  simp only [threeAdicModeSupport, Finset.mem_image, Finset.mem_univ,
    true_and] at hab
  rcases hab with ⟨m, rfl⟩
  simp only [threeAdicModeFrequencyPair]
  refine ⟨?_, threeAdicFrequencyValue_lt_pow m.1.2 m.2.2.1,
    ?_, threeAdicFrequencyValue_lt_pow m.2.1.2 m.2.2.2⟩
  · exact Nat.mul_pos (threeAdicFrequencyNumerator_pos _) (pow_pos (by decide) _)
  · exact Nat.mul_pos (threeAdicFrequencyNumerator_pos _) (pow_pos (by decide) _)

/-- The finite kernel sum in the compiled one-cell Melnikov formula is
exactly the public mode response produced by the concrete hierarchy. -/
theorem chebyshevFirstMelnikovDisplacement_threeAdic_eq_modeKernelResponse
    {r : ℕ} (_hr : 1 ≤ r) (lambda zeta : ℝ)
    (hlambda : 1 ≤ lambda) (blockCoeff : ThreeAdicMode r → ℝ)
    (c : ThreeAdicTensorCell r) {h : ℝ} (hh : 0 < h) (hhq : h < 1 / 4) :
    Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
        (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
        (Spikes.firstCoordinatePrimitive
          (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
            (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda h =
      Spikes.chebyshevCellJacobianOrientation (threeAdicRowIndex c.2.1)
          (threeAdicRowIndex c.2.2) *
        (2 * Real.pi * h / Real.sqrt lambda) *
          threeAdicModeKernelResponse r lambda zeta blockCoeff c h := by
  rw [Spikes.chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum
    (pow_ne_zero _ (by decide)) (threeAdicModeSupport r)
    (threeAdicHierarchicalPairCoefficient r zeta blockCoeff)
    threeAdicModeSupport_frequency_bounds hlambda hh hhq]
  congr 1
  unfold threeAdicModeSupport
  rw [Finset.sum_image]
  · unfold threeAdicModeKernelResponse
    apply Finset.sum_congr rfl
    intro m _
    rw [threeAdicHierarchicalPairCoefficient_mode]
    unfold threeAdicModeFrequencyPair threeAdicTensorCellWeight
      threeAdicTensorWeight
    push_cast
    rfl
  · exact threeAdicModeFrequencyPair_injective.injOn

/-- A simple kernel root in the certified interval is a simple root of the
actual one-cell first Melnikov displacement. -/
theorem chebyshevFirstMelnikovDisplacement_threeAdic_simpleRoot
    {r : ℕ} (hr : 1 ≤ r) {lambda zeta : ℝ} (hlambda : 1 ≤ lambda)
    (blockCoeff : ThreeAdicMode r → ℝ) (c : ThreeAdicTensorCell r)
    {h d : ℝ} (hh : 0 < h) (hhq : h < 1 / 4)
    (hzero : threeAdicModeKernelResponse r lambda zeta blockCoeff c h = 0)
    (hd : d ≠ 0)
    (hderiv : HasDerivAt
      (threeAdicModeKernelResponse r lambda zeta blockCoeff c) d h) :
    ∃ dM : ℝ, dM ≠ 0 ∧
      HasDerivAt
        (fun u => Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
          (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
          (Spikes.firstCoordinatePrimitive
            (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
              (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda u)
        dM h := by
  let orientation := Spikes.chebyshevCellJacobianOrientation
    (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
  let C : ℝ := orientation * (2 * Real.pi / Real.sqrt lambda)
  have hsqrt : Real.sqrt lambda ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda))
  have hC : C ≠ 0 := by
    unfold C orientation
    exact mul_ne_zero
      (Spikes.chebyshevCellJacobianOrientation_ne_zero _ _)
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hsqrt)
  have hright : HasDerivAt
      (fun u => orientation * (2 * Real.pi * u / Real.sqrt lambda) *
        threeAdicModeKernelResponse r lambda zeta blockCoeff c u)
      (C * (h * d)) h := by
    have hprod := hasDerivAt_id h |>.mul hderiv
    have hprod' : HasDerivAt
        (fun u => u * threeAdicModeKernelResponse r lambda zeta blockCoeff c u)
        (h * d) h := by
      have hprod0 : HasDerivAt
          (id * threeAdicModeKernelResponse r lambda zeta blockCoeff c)
          (h * d) h := by
        simpa [hzero, mul_comm] using hprod
      apply hprod0.congr_of_eventuallyEq
      exact Eventually.of_forall fun u => rfl
    apply (hprod'.const_mul C).congr_of_eventuallyEq
    exact Eventually.of_forall fun u => by
      unfold C orientation
      ring
  have heq :
      (fun u => Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
        (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
        (Spikes.firstCoordinatePrimitive
          (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
            (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda u) =ᶠ[𝓝 h]
      (fun u => orientation * (2 * Real.pi * u / Real.sqrt lambda) *
        threeAdicModeKernelResponse r lambda zeta blockCoeff c u) := by
    filter_upwards [IsOpen.eventually_mem isOpen_Ioo ⟨hh, hhq⟩] with u hu
    exact chebyshevFirstMelnikovDisplacement_threeAdic_eq_modeKernelResponse
      hr lambda zeta hlambda blockCoeff c hu.1 hu.2
  refine ⟨C * (h * d), mul_ne_zero hC (mul_ne_zero hh.ne' hd), ?_⟩
  exact hright.congr_of_eventuallyEq heq

/-- One coefficient family simultaneously gives the required positive simple
zeros of the actual finite-density Melnikov displacement on every marked
three-adic cell. -/
theorem threeAdicMelnikovSimpleRootRealization {r : ℕ} (hr : 1 ≤ r) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (blockCoeff : ThreeAdicMode r → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ),
        ∀ᶠ zeta in 𝓝[>] 0,
          (∀ c, Function.Injective (fun s => root c s zeta)) ∧
          ∀ c, ∀ s : Fin (threeAdicBlockRootCount c.1),
            let h := root c s zeta
            Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
                (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
                (Spikes.firstCoordinatePrimitive
                  (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
                    (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda h = 0 ∧
              0 < h ∧ h < 1 / 4 ∧
              ∃ dM : ℝ, dM ≠ 0 ∧
                HasDerivAt
                  (fun u => Spikes.chebyshevFirstMelnikovDisplacement (3 ^ r)
                    (threeAdicRowIndex c.2.1) (threeAdicRowIndex c.2.2)
                    (Spikes.firstCoordinatePrimitive
                      (Spikes.finiteChebyshevDensity (3 ^ r) (threeAdicModeSupport r)
                        (threeAdicHierarchicalPairCoefficient r zeta blockCoeff))) lambda u)
                  dM h := by
  rcases threeAdicModeKernelRealization r with ⟨Lambda, hLambda, hrealize⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  rcases hrealize lambda hlambda with ⟨blockCoeff, root, hevent⟩
  refine ⟨blockCoeff, root, ?_⟩
  filter_upwards [hevent] with zeta hzeta
  refine ⟨hzeta.1, ?_⟩
  intro c s
  dsimp only
  rcases hzeta.2 c s with ⟨hzero, hpos, hquarter, d, hd, hderiv⟩
  have hMzero := chebyshevFirstMelnikovDisplacement_threeAdic_eq_modeKernelResponse
    hr lambda zeta (hLambda.trans (le_of_lt hlambda)) blockCoeff c hpos hquarter
  rw [hzero, mul_zero] at hMzero
  rcases chebyshevFirstMelnikovDisplacement_threeAdic_simpleRoot
    hr (hLambda.trans (le_of_lt hlambda)) blockCoeff c hpos hquarter
      hzero hd hderiv with ⟨dM, hdM, hMd⟩
  exact ⟨hMzero, hpos, hquarter, dM, hdM, hMd⟩

end Hilbert16
