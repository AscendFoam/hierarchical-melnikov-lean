import Hilbert16.Dynamics.ChebyshevSection
import Hilbert16.Spikes.HamiltonianSectionClock

set_option autoImplicit false

namespace Hilbert16

open Set
open Hilbert16.Spikes

/-- The section-based explicit Hamiltonian-time oval transported to the public
Euclidean phase space used by the Poincaré-return construction. -/
noncomputable def chebyshevHamiltonianSectionPhaseOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (t : ℝ) : PhaseSpace :=
  phaseSpaceProdEquiv.symm
    (chebyshevHamiltonianSectionTimeOrbit
      hn hi hj hlambda hh hhHalf t)

@[simp]
theorem phaseSpaceProdEquiv_chebyshevHamiltonianSectionPhaseOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (t : ℝ) :
    phaseSpaceProdEquiv
        (chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf t) =
      chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf t := by
  simp [chebyshevHamiltonianSectionPhaseOrbit]

/-- At physical time zero the transported orbit is exactly the base point of
the Chebyshev Poincaré section. -/
@[simp]
theorem chebyshevHamiltonianSectionPhaseOrbit_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionPhaseOrbit
        hn hi hj hlambda hh hhHalf 0 =
      chebyshevPhaseSectionPoint n i j lambda h := by
  simp [chebyshevHamiltonianSectionPhaseOrbit,
    chebyshevPhaseSectionPoint, chebyshevPhaseOrbit]

/-- After its strictly positive physical period the transported orbit returns
to the same Poincaré-section base point. -/
@[simp]
theorem chebyshevHamiltonianSectionPhaseOrbit_period
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionPhaseOrbit
        hn hi hj hlambda hh hhHalf
          (chebyshevHamiltonianSectionPeriod n i j lambda h) =
      chebyshevPhaseSectionPoint n i j lambda h := by
  simp [chebyshevHamiltonianSectionPhaseOrbit,
    chebyshevPhaseSectionPoint, chebyshevPhaseOrbit]

/-- First-coordinate Hamilton equation for the explicit orbit after transport
to the public phase space. -/
theorem chebyshevHamiltonianSectionPhaseOrbit_fst_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (phaseSpaceProdEquiv
        (chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf s)).1)
      ((phaseSpaceProdEquiv
        (chebyshevPhaseHamiltonianVector n lambda
          (chebyshevHamiltonianSectionPhaseOrbit
            hn hi hj hlambda hh hhHalf t))).1) t := by
  simpa [chebyshevPhaseHamiltonianVector] using
    chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt
      hn hi hj hlambda hh hhHalf ht

/-- Second-coordinate Hamilton equation for the explicit orbit after
transport to the public phase space. -/
theorem chebyshevHamiltonianSectionPhaseOrbit_snd_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (phaseSpaceProdEquiv
        (chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf s)).2)
      ((phaseSpaceProdEquiv
        (chebyshevPhaseHamiltonianVector n lambda
          (chebyshevHamiltonianSectionPhaseOrbit
            hn hi hj hlambda hh hhHalf t))).2) t := by
  simpa [chebyshevPhaseHamiltonianVector] using
    chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt
      hn hi hj hlambda hh hhHalf ht

theorem continuousOn_chebyshevHamiltonianSectionPhaseOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    ContinuousOn
      (chebyshevHamiltonianSectionPhaseOrbit hn hi hj hlambda hh hhHalf)
      (Set.Icc (0 : ℝ)
        (chebyshevHamiltonianSectionPeriod n i j lambda h)) := by
  apply Continuous.continuousOn
  have hfst : Continuous (fun t : ℝ =>
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).1) :=
    continuous_iff_continuousAt.mpr fun t =>
      (chebyshevHamiltonianAngularOrbit_fst_hasDerivAt
        (i := i) (j := j) hn hlambda hh hhHalf (t := t)).continuousAt
  have hsnd : Continuous (fun t : ℝ =>
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).2) :=
    continuous_iff_continuousAt.mpr fun t =>
      (chebyshevHamiltonianAngularOrbit_snd_hasDerivAt
        (i := i) (j := j) hn hlambda hh hhHalf (t := t)).continuousAt
  have horbit : Continuous
      (chebyshevHamiltonianAngularOrbit n i j lambda h) :=
    hfst.prodMk hsnd
  have hangle : Continuous (fun t : ℝ =>
      chebyshevHamiltonianSectionAngularStart i j +
        chebyshevHamiltonianSectionPhysicalOffset
          hn hi hj hlambda hh hhHalf t) :=
    continuous_const.add
      (continuous_chebyshevHamiltonianSectionPhysicalOffset
        hn hi hj hlambda hh hhHalf)
  exact phaseSpaceProdEquiv.symm.continuous.comp (horbit.comp hangle)

end Hilbert16
