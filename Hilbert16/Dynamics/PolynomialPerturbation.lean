import Hilbert16.Dynamics.PerturbedEnergy
import Hilbert16.Degree
import Hilbert16.Spikes.PoincarePersistence
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false

namespace Hilbert16

open Hilbert16.Spikes

/-- Evaluate a bivariate polynomial in the physical product coordinates. -/
noncomputable def mvPolynomialProdEval
    (p : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) : ℝ :=
  MvPolynomial.eval ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z) p

@[simp]
theorem mvPolynomialProdEval_C (c : ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (MvPolynomial.C c) z = c := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_add (p q : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (p + q) z =
      mvPolynomialProdEval p z + mvPolynomialProdEval q z := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_mul (p q : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (p * q) z =
      mvPolynomialProdEval p z * mvPolynomialProdEval q z := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_neg (p : MvPolynomial (Fin 2) ℝ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (-p) z = -mvPolynomialProdEval p z := by
  simp [mvPolynomialProdEval]

@[simp]
theorem mvPolynomialProdEval_chebyshevAt_zero (n : ℕ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (chebyshevAt 0 n) z =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.1 := by
  rw [mvPolynomialProdEval, chebyshevAt, eval_univariateAt]
  rfl

@[simp]
theorem mvPolynomialProdEval_chebyshevAt_one (n : ℕ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (chebyshevAt 1 n) z =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z.2 := by
  rw [mvPolynomialProdEval, chebyshevAt, eval_univariateAt]
  rfl

@[simp]
theorem mvPolynomialProdEval_chebyshevDerivativeAt_zero (n : ℕ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (chebyshevDerivativeAt 0 n) z =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval z.1 := by
  rw [mvPolynomialProdEval, chebyshevDerivativeAt, eval_univariateAt]
  rfl

@[simp]
theorem mvPolynomialProdEval_chebyshevDerivativeAt_one (n : ℕ) (z : ℝ × ℝ) :
    mvPolynomialProdEval (chebyshevDerivativeAt 1 n) z =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval z.2 := by
  rw [mvPolynomialProdEval, chebyshevDerivativeAt, eval_univariateAt]
  rfl

/-- Coordinate evaluation of the public polynomial-vector-field carrier. -/
theorem phaseSpaceProdEquiv_polyVectorField_eval
    (Y : PolyVectorField) (z : PhaseSpace) :
    phaseSpaceProdEquiv (Y.eval z) =
      (mvPolynomialProdEval (Y 0) (phaseSpaceProdEquiv z),
        mvPolynomialProdEval (Y 1) (phaseSpaceProdEquiv z)) := by
  unfold phaseSpaceProdEquiv PolyVectorField.eval mvPolynomialProdEval
  have hcoords :
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)) z =
        ![z.ofLp 0, z.ofLp 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply, hcoords]
  apply Prod.ext <;> rfl

/-- The algebraically audited Hamiltonian polynomial field evaluates to the
same physical Hamiltonian vector used by the dynamics layer. -/
theorem chebyshevHamiltonianPolyVectorField_eval_eq
    (n : ℕ) (lambda : ℝ) (z : PhaseSpace) :
    (chebyshevHamiltonianPolyVectorField n lambda).eval z =
      chebyshevPhaseHamiltonianVector n lambda z := by
  apply phaseSpaceProdEquiv.injective
  rw [phaseSpaceProdEquiv_polyVectorField_eval]
  simp [chebyshevHamiltonianPolyVectorField, chebyshevPhaseHamiltonianVector,
    chebyshevHamiltonianVector, chebyshevHamiltonianDx, chebyshevHamiltonianDy]

/-- The final polynomial field from the degree audit is definitionally the
paper's actual one-component perturbation after evaluation. -/
theorem finalPolyVectorField_eval_eq_perturbedPhaseVector
    (n : ℕ) (lambda mu : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (z : PhaseSpace) :
    (finalPolyVectorField n lambda mu S).eval z =
      chebyshevPerturbedPhaseVector n lambda
        (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu z := by
  apply phaseSpaceProdEquiv.injective
  rw [phaseSpaceProdEquiv_polyVectorField_eval]
  simp [finalPolyVectorField, chebyshevHamiltonianPolyVectorField,
    chebyshevPerturbedPhaseVector, chebyshevPerturbedVector,
    chebyshevHamiltonianDx, chebyshevHamiltonianDy]

/-- Every physical polynomial perturbation coefficient is continuous. -/
theorem continuous_mvPolynomialProdEval (p : MvPolynomial (Fin 2) ℝ) :
    Continuous (mvPolynomialProdEval p) := by
  exact p.continuous_eval.comp
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.continuous

/-- A finite-dimensional multivariate polynomial is smooth to every finite
order. This calculus lemma is kept local because Mathlib currently exposes
continuity, but not a ready-made `ContDiff` theorem, for `MvPolynomial.eval`. -/
theorem contDiff_mvPolynomial_eval (p : MvPolynomial (Fin 2) ℝ) (k : ℕ) :
    ContDiff ℝ k (fun z : Fin 2 → ℝ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa only [MvPolynomial.eval_C] using
        (contDiff_const : ContDiff ℝ k (fun _ : Fin 2 → ℝ => a))
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add, Pi.add_apply] using hp.add hq
  | mul_X p i hp =>
      have hi : ContDiff ℝ k (fun z : Fin 2 → ℝ => z i) := by
        fun_prop
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hi

theorem contDiff_mvPolynomialProdEval (p : MvPolynomial (Fin 2) ℝ) (k : ℕ) :
    ContDiff ℝ k (mvPolynomialProdEval p) := by
  unfold mvPolynomialProdEval
  exact (contDiff_mvPolynomial_eval p k).comp
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.contDiff

/-- Joint `C¹` regularity in `(mu,z)` of the actual perturbation used by the
ODE layer. -/
theorem contDiff_chebyshevPerturbedParameter
    {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 1 P) (n : ℕ) (lambda : ℝ) :
    ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      chebyshevPerturbedPhaseVector n lambda P z.1 z.2) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hprod : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      phaseSpaceProdEquiv z.2) := by fun_prop
  have hx : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      p.eval (phaseSpaceProdEquiv z.2).1) :=
    (contDiff_realPolynomial_eval p).comp (by fun_prop)
  have hdx : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      p.derivative.eval (phaseSpaceProdEquiv z.2).1) :=
    (contDiff_realPolynomial_eval p.derivative).comp (by fun_prop)
  have hy : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      p.eval (phaseSpaceProdEquiv z.2).2) :=
    (contDiff_realPolynomial_eval p).comp (by fun_prop)
  have hdy : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      p.derivative.eval (phaseSpaceProdEquiv z.2).2) :=
    (contDiff_realPolynomial_eval p.derivative).comp (by fun_prop)
  have hPcomp : ContDiff ℝ 1 (fun z : ParameterPhaseSpace =>
      P (phaseSpaceProdEquiv z.2)) := hP.comp hprod
  unfold chebyshevPerturbedPhaseVector chebyshevPerturbedVector
    chebyshevHamiltonianDx chebyshevHamiltonianDy
  exact phaseSpaceProdEquiv.symm.contDiff.comp
    (((contDiff_const.mul hy).mul hdy).add
      (contDiff_fst.mul hPcomp) |>.prodMk (hx.mul hdx).neg)

/-- The degree-audited polynomial perturbation has a genuine local solution
through every parameterized initial point.  This is the actual-field
specialization of Mathlib's Picard local-existence theorem; it does not yet
claim a common-time smooth flow. -/
theorem chebyshevPolynomialPerturbation_exists_local_integralCurve
    (n : ℕ) (lambda mu0 : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (x0 : PhaseSpace) :
    ∃ gamma : ℝ → ParameterPhaseSpace, gamma 0 = (mu0, x0) ∧
      ∃ epsilon > (0 : ℝ),
        IsIntegralCurveOn gamma
          (fun _ z => Spikes.parameterLift
            (fun mu x => chebyshevPerturbedPhaseVector n lambda
              (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x) z)
          (Set.Ioo (-epsilon) epsilon) := by
  let P : ℝ × ℝ → ℝ :=
    mvPolynomialProdEval (chebyshevPPolynomial n S)
  let X : ℝ → PhaseSpace → PhaseSpace :=
    fun mu x => chebyshevPerturbedPhaseVector n lambda P mu x
  apply Spikes.parameterLift_exists_local_integralCurve X mu0 x0
  have hfield : ContDiff ℝ 1 (fun z : ParameterPhaseSpace => X z.1 z.2) := by
    exact contDiff_chebyshevPerturbedParameter
      (contDiff_mvPolynomialProdEval (chebyshevPPolynomial n S) 1) n lambda
  have hlift : ContDiff ℝ 1 (Spikes.parameterLift X) := by
    change ContDiff ℝ 1
      (fun z : ParameterPhaseSpace => ((0 : ℝ), X z.1 z.2))
    exact (contDiff_const : ContDiff ℝ 1
      (fun _ : ParameterPhaseSpace => (0 : ℝ))).prodMk hfield
  exact hlift.contDiffAt

end Hilbert16
