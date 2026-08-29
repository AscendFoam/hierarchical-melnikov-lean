import Hilbert16.Dynamics.PolynomialPerturbation
import Hilbert16.Spikes.GreenVertical

set_option autoImplicit false

namespace Hilbert16

/-!
# Algebraic and analytic first-coordinate primitives agree
-/

@[simp]
theorem mvPolynomialProdEval_zero (z : ℝ × ℝ) :
    mvPolynomialProdEval (0 : MvPolynomial (Fin 2) ℝ) z = 0 := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_X_zero (z : ℝ × ℝ) :
    mvPolynomialProdEval (MvPolynomial.X (0 : Fin 2)) z = z.1 := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_X_one (z : ℝ × ℝ) :
    mvPolynomialProdEval (MvPolynomial.X (1 : Fin 2)) z = z.2 := by
  simp [mvPolynomialProdEval]

/-- Differentiating a bivariate polynomial along its first physical
coordinate evaluates its first partial derivative. -/
theorem mvPolynomialProdEval_firstSlice_hasDerivAt
    (p : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun x => mvPolynomialProdEval p (x, z.2))
      (mvPolynomialProdEval (MvPolynomial.pderiv 0 p) z) z.1 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa only [MvPolynomial.pderiv_C, mvPolynomialProdEval_zero,
        mvPolynomialProdEval_C] using (hasDerivAt_const z.1 a)
  | add p q hp hq =>
      rw [map_add, mvPolynomialProdEval_add]
      refine (hp.add hq).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Pi.add_apply] using
          (mvPolynomialProdEval_add p q (x, z.2))
  | mul_X p i hp =>
      fin_cases i
      · have hmul := hp.mul (hasDerivAt_id z.1)
        have hmul' :
            HasDerivAt ((fun x => mvPolynomialProdEval p (x, z.2)) * id)
              (mvPolynomialProdEval p z +
                z.1 * mvPolynomialProdEval (MvPolynomial.pderiv 0 p) z) z.1 := by
          apply hmul.congr_deriv
          simp only [id_eq, mul_one]
          ring
        have hres :
            HasDerivAt (fun x => mvPolynomialProdEval p (x, z.2) * x)
              (mvPolynomialProdEval p z +
                z.1 * mvPolynomialProdEval (MvPolynomial.pderiv 0 p) z) z.1 := by
          refine hmul'.congr_of_eventuallyEq ?_
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.mul_apply, id_eq, mul_comm]
        simpa [MvPolynomial.pderiv_mul, add_comm, mul_comm] using hres
      · have hmul := hp.mul_const z.2
        have hmul' :
            HasDerivAt (fun x => mvPolynomialProdEval p (x, z.2) * z.2)
              (z.2 * mvPolynomialProdEval (MvPolynomial.pderiv 0 p) z) z.1 := by
          apply hmul.congr_deriv
          ring
        simpa [MvPolynomial.pderiv_mul] using hmul'

/-- The algebraic primitive has zero value on the normalizing line `x=0`. -/
theorem mvPolynomialProdEval_integrateAt_zero
    (p : MvPolynomial (Fin 2) ℝ) (y : ℝ) :
    mvPolynomialProdEval (MvPolynomial.integrateAt 0 p) (0, y) = 0 := by
  unfold MvPolynomial.integrateAt mvPolynomialProdEval
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [MvPolynomial.eval_monomial]
  simp

/-- The normalized algebraic antiderivative evaluates to the canonical
interval-integral primitive used by the Green/Melnikov calculation. -/
theorem mvPolynomialProdEval_integrateAt_eq_firstCoordinatePrimitive
    (p : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (MvPolynomial.integrateAt 0 p) z =
      Spikes.firstCoordinatePrimitive (mvPolynomialProdEval p) z := by
  let F : ℝ → ℝ := fun x =>
    mvPolynomialProdEval (MvPolynomial.integrateAt 0 p) (x, z.2)
  let f : ℝ → ℝ := fun x => mvPolynomialProdEval p (x, z.2)
  have hderiv : ∀ x ∈ Set.uIcc 0 z.1, HasDerivAt F (f x) x := by
    intro x hx
    have hraw := mvPolynomialProdEval_firstSlice_hasDerivAt
      (MvPolynomial.integrateAt 0 p) (x, z.2)
    rw [MvPolynomial.pderiv_integrateAt] at hraw
    exact hraw
  have hf : Continuous f := by
    exact (continuous_mvPolynomialProdEval p).comp (continuous_id.prodMk continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hf.intervalIntegrable 0 z.1)
  have hFzero : F 0 = 0 := mvPolynomialProdEval_integrateAt_zero p z.2
  unfold Spikes.firstCoordinatePrimitive
  change F z.1 = ∫ x in (0 : ℝ)..z.1, f x
  rw [hFTC, hFzero, sub_zero]

end Hilbert16
