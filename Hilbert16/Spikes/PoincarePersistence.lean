import Hilbert16.Foundations.PeriodicOrbit
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set

/--
Turn a parameter-dependent planar vector field into an autonomous vector field by adjoining the
equation `mu' = 0`.  Smooth dependence on `mu` will be obtained from the initial-state dependence of
this lifted system.
-/
def parameterLift (X : ℝ → PhaseSpace → PhaseSpace) :
    ParameterPhaseSpace → ParameterPhaseSpace :=
  fun z => (0, X z.1 z.2)

/--
A `C¹` planar vector field has a local integral curve through every base point.  This is the first
locked Mathlib interface for B3; it does not yet assert smooth dependence, a return time, or a
Poincare map.
-/
theorem exists_local_integralCurve (X : PhaseSpace → PhaseSpace) (x0 : PhaseSpace)
    (hX : ContDiffAt ℝ 1 X x0) :
    ∃ gamma : ℝ → PhaseSpace, gamma 0 = x0 ∧ ∃ epsilon > (0 : ℝ),
      IsIntegralCurveOn gamma (autonomousField X) (Ioo (-epsilon) epsilon) := by
  obtain ⟨gamma, hgamma0, epsilon, hepsilon, hgamma⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨gamma, hgamma0, epsilon, hepsilon, ?_⟩
  intro t ht
  exact (hgamma t (by simpa using ht)).hasDerivWithinAt

/--
The same local-existence interface for the parameter-lifted system.  The next B3 obligation is to
prove `C¹` dependence of this flow on the lifted initial point on a common compact time interval.
-/
theorem parameterLift_exists_local_integralCurve
    (X : ℝ → PhaseSpace → PhaseSpace) (mu0 : ℝ) (x0 : PhaseSpace)
    (hX : ContDiffAt ℝ 1 (parameterLift X) (mu0, x0)) :
    ∃ gamma : ℝ → ParameterPhaseSpace, gamma 0 = (mu0, x0) ∧ ∃ epsilon > (0 : ℝ),
      IsIntegralCurveOn gamma (fun _ z => parameterLift X z) (Ioo (-epsilon) epsilon) := by
  obtain ⟨gamma, hgamma0, epsilon, hepsilon, hgamma⟩ :=
    hX.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨gamma, hgamma0, epsilon, hepsilon, ?_⟩
  intro t ht
  exact (hgamma t (by simpa using ht)).hasDerivWithinAt

end Hilbert16.Spikes
