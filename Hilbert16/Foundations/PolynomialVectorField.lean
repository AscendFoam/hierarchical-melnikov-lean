import Hilbert16.Foundations.StateSpace
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false

namespace Hilbert16

/-- A planar polynomial vector field, represented by its two coordinate polynomials as fixed in
Decision D003. -/
abbrev PolyVectorField := Fin 2 → MvPolynomial (Fin 2) ℝ

/-- Evaluate a polynomial vector field on the canonical Euclidean phase space. -/
noncomputable def PolyVectorField.eval (X : PolyVectorField) : PhaseSpace → PhaseSpace :=
  fun x => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
    (fun i => MvPolynomial.eval
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)) x) (X i))

/-- The degree of a planar polynomial vector field is the maximum total degree of its two
coordinate polynomials. -/
noncomputable def PolyVectorField.degree (X : PolyVectorField) : WithBot ℕ :=
  max (MvPolynomial.totalDegree (X 0)) (MvPolynomial.totalDegree (X 1))

theorem PolyVectorField.coordinate_totalDegree_le_degree (X : PolyVectorField) (i : Fin 2) :
    MvPolynomial.totalDegree (X i) ≤ X.degree := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

end Hilbert16
