import Hilbert16.Spikes.ChebyshevChangeOfVariables

set_option autoImplicit false

namespace Hilbert16.Spikes

/-- A finite polynomial density assembled from Chebyshev tensor modes, including the two
`T_n'` factors required by the perturbation in Paper Eq. (3.4). -/
noncomputable def finiteChebyshevDensity
    (n : ℕ) (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (z : ℝ × ℝ) : ℝ :=
  ∑ k ∈ support, coeff k * chebyshevDensityMode n k.1 k.2 z

theorem finiteChebyshevDensity_integrableOn_cell
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    MeasureTheory.IntegrableOn (finiteChebyshevDensity n support coeff)
      (chebyshevCellEnergyRegion n i j lambda h) := by
  unfold finiteChebyshevDensity MeasureTheory.IntegrableOn
  apply MeasureTheory.integrable_finsetSum
  intro k hk
  exact (chebyshevDensityMode_integrableOn_cell
    (a := k.1) (b := k.2) hn hi hj hlambda hh hhq).const_mul (coeff k)

/-- Paper Eq. (3.8)--(3.12) for an arbitrary finite Chebyshev density on one original cell.
Every frequency is required to lie strictly between `0` and `n`, exactly the range used by the
analytic-kernel rank argument. -/
theorem integral_finiteChebyshevDensity_cell_eq_kernel_sum
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    (support : Finset (ℕ × ℕ)) (coeff : ℕ × ℕ → ℝ)
    (hfreq : ∀ k ∈ support, 0 < k.1 ∧ k.1 < n ∧ 0 < k.2 ∧ k.2 < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhq : h < 1 / 4) :
    (∫ z : ℝ × ℝ in chebyshevCellEnergyRegion n i j lambda h,
      finiteChebyshevDensity n support coeff z) =
      chebyshevCellJacobianOrientation i j *
        (2 * Real.pi * h / Real.sqrt lambda) *
          ∑ k ∈ support,
            coeff k *
              (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
                Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
              analyticKernel ((k.1 : ℝ) / (n : ℝ)) ((k.2 : ℝ) / (n : ℝ)) lambda h := by
  have hterms : ∀ k ∈ support,
      MeasureTheory.Integrable
        (fun z : ℝ × ℝ => coeff k * chebyshevDensityMode n k.1 k.2 z)
        (MeasureTheory.volume.restrict (chebyshevCellEnergyRegion n i j lambda h)) := by
    intro k hk
    exact (chebyshevDensityMode_integrableOn_cell
      (a := k.1) (b := k.2) hn hi hj hlambda hh hhq).const_mul (coeff k)
  unfold finiteChebyshevDensity
  rw [MeasureTheory.integral_finsetSum support hterms]
  calc
    (∑ k ∈ support,
        ∫ z : ℝ × ℝ in chebyshevCellEnergyRegion n i j lambda h,
          coeff k * chebyshevDensityMode n k.1 k.2 z) =
      ∑ k ∈ support,
        coeff k *
          (chebyshevCellJacobianOrientation i j *
            (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
              Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
            (2 * Real.pi * h / Real.sqrt lambda) *
              analyticKernel ((k.1 : ℝ) / (n : ℝ))
                ((k.2 : ℝ) / (n : ℝ)) lambda h) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [MeasureTheory.integral_const_mul,
        integral_chebyshevDensityMode_cell_eq_orientation_mul_weight_mul_kernel
          hn hi hj (hfreq k hk).1 (hfreq k hk).2.1
            (hfreq k hk).2.2.1 (hfreq k hk).2.2.2 hlambda hh hhq]
    _ = chebyshevCellJacobianOrientation i j *
        (2 * Real.pi * h / Real.sqrt lambda) *
          ∑ k ∈ support,
            coeff k *
              (Real.cos ((k.1 : ℝ) * chebyshevRootPhase n i) *
                Real.cos ((k.2 : ℝ) * chebyshevRootPhase n j)) *
              analyticKernel ((k.1 : ℝ) / (n : ℝ))
                ((k.2 : ℝ) / (n : ℝ)) lambda h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end Hilbert16.Spikes
