import Hilbert16.Dynamics.ParameterizedFlow

set_option autoImplicit false

namespace Hilbert16

/-- Data required at one unperturbed Chebyshev orbit to construct a local return time from a
genuine parameterized `C¹` flow. -/
structure ChebyshevReturnSetup (X : ℝ → PhaseSpace → PhaseSpace) where
  localFlow : C1LocalFlow X
  n : ℕ
  i : ℕ
  j : ℕ
  lambda : ℝ
  h₀ : ℝ
  T₀ : ℝ
  n_ne_zero : n ≠ 0
  i_lt : i < n
  j_lt : j < n
  lambda_ge_one : 1 ≤ lambda
  h₀_pos : 0 < h₀
  h₀_lt_half : h₀ < 1 / 2
  T₀_pos : 0 < T₀
  return_mem :
    ((0, chebyshevPhaseSectionPoint n i j lambda h₀), T₀) ∈ localFlow.domain
  returns_to_base :
    localFlow.chebyshevByEnergy n i j lambda ((0, h₀), T₀) =
      chebyshevPhaseSectionPoint n i j lambda h₀
  unperturbed_eq : ∀ z : PhaseSpace,
    X 0 z = chebyshevPhaseHamiltonianVector n lambda z

def ChebyshevReturnSetup.base {X : ℝ → PhaseSpace → PhaseSpace}
    (S : ChebyshevReturnSetup X) : (ℝ × ℝ) × ℝ :=
  ((0, S.h₀), S.T₀)

theorem ChebyshevReturnSetup.contDiffAt_flowByEnergy
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ContDiffAt ℝ 1 (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda) S.base := by
  exact S.localFlow.contDiffAt_chebyshevByEnergy S.n S.i S.j S.lambda
    S.h₀_pos S.h₀_lt_half S.return_mem

theorem ChebyshevReturnSetup.section_hasDerivAt_return
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    HasDerivAt
      (fun t : ℝ => chebyshevSectionCoordinate S.n S.j
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, S.h₀), t)))
      (chebyshevSectionFDeriv
        (chebyshevPhaseHamiltonianVector S.n S.lambda
          (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀))) S.T₀ := by
  have hflow := S.localFlow.chebyshevByEnergy_hasDerivAt
    S.n S.i S.j S.lambda 0 S.h₀ S.T₀ S.return_mem
  have hsection := chebyshevSectionCoordinate_hasFDerivAt S.n S.j
    (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, S.h₀), S.T₀))
  have hcomp := hsection.comp S.T₀ hflow.hasFDerivAt
  have hcomp' := hcomp.hasDerivAt
  rw [S.returns_to_base, S.unperturbed_eq] at hcomp'
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hcomp'

theorem ChebyshevReturnSetup.section_return_deriv_ne_zero
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    chebyshevSectionFDeriv
      (chebyshevPhaseHamiltonianVector S.n S.lambda
        (chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀)) ≠ 0 :=
  chebyshevSectionFDeriv_phaseHamiltonianVector_ne_zero
    S.n_ne_zero S.i_lt S.j_lt S.lambda_ge_one S.h₀_pos S.h₀_lt_half

/-- The locally unique `C¹` return-time branch through the unperturbed period `T₀`. -/
noncomputable def ChebyshevReturnSetup.returnTime
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    LocalLevelTime
      (fun z => chebyshevSectionCoordinate S.n S.j
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda z)) S.base :=
  localReturnTime_of_transverseSection S.contDiffAt_flowByEnergy
    ((contDiff_chebyshevSectionCoordinate S.n S.j).contDiffAt)
    S.section_hasDerivAt_return S.section_return_deriv_ne_zero

/-- The scalar Hamiltonian displacement of the constructed local return map. -/
noncomputable def ChebyshevReturnSetup.energyDisplacement
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) : ℝ × ℝ → ℝ :=
  S.returnTime.energyDisplacement
    (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
    (chebyshevPhaseEnergy S.n S.lambda)

theorem ChebyshevReturnSetup.contDiffAt_energyDisplacement
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ContDiffAt ℝ 1 S.energyDisplacement (0, S.h₀) := by
  exact S.returnTime.contDiffAt_energyDisplacement S.contDiffAt_flowByEnergy
    ((contDiff_chebyshevPhaseEnergy S.n S.lambda).contDiffAt)

end Hilbert16
