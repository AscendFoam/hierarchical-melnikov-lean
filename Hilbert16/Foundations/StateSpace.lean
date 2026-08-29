import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

namespace Hilbert16

/-- The canonical phase space for the planar vector fields in the construction. -/
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 2)

/-- Parameter and phase point, used to turn a parameter-dependent ODE into an autonomous ODE. -/
abbrev ParameterPhaseSpace := ℝ × PhaseSpace

/-- The canonical continuous linear coordinate equivalence between the public Euclidean phase
space and the product coordinates used by the explicit Chebyshev calculations. -/
noncomputable def phaseSpaceProdEquiv : PhaseSpace ≃L[ℝ] (ℝ × ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp]
theorem phaseSpaceProdEquiv_symm_apply_fst (z : ℝ × ℝ) :
    phaseSpaceProdEquiv.symm z 0 = z.1 := by
  rfl

@[simp]
theorem phaseSpaceProdEquiv_symm_apply_snd (z : ℝ × ℝ) :
    phaseSpaceProdEquiv.symm z 1 = z.2 := by
  rfl

end Hilbert16
