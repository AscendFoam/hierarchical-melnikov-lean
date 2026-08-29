import Hilbert16.Spikes.HamiltonianAngularTrace
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set
open scoped Topology

/-- Positive scalar relating the Hamiltonian-oriented angular velocity to
the physical Hamiltonian vector. -/
noncomputable def chebyshevHamiltonianAngularTimeFactor
    (n i j : ℕ) (lambda h t : ℝ) : ℝ :=
  chebyshevCellJacobianOrientation i j *
    (Real.sqrt lambda *
      chebyshevForwardDerivative n
        (chebyshevHamiltonianAngularOrbit n i j lambda h t).1 *
      chebyshevForwardDerivative n
        (chebyshevHamiltonianAngularOrbit n i j lambda h t).2)

/-- Physical Hamiltonian time elapsed per unit of the oriented angular
parameter. -/
noncomputable def chebyshevHamiltonianAngularTimeDensity
    (n i j : ℕ) (lambda h t : ℝ) : ℝ :=
  (chebyshevHamiltonianAngularTimeFactor n i j lambda h t)⁻¹

/-- Physical Hamiltonian time elapsed from angular parameter `0` to `s`. -/
noncomputable def chebyshevHamiltonianAngularTime
    (n i j : ℕ) (lambda h s : ℝ) : ℝ :=
  ∫ u in 0..s, chebyshevHamiltonianAngularTimeDensity n i j lambda h u

/-- The physical duration of one full oriented angular turn. -/
noncomputable def chebyshevHamiltonianAngularPeriod
    (n i j : ℕ) (lambda h : ℝ) : ℝ :=
  chebyshevHamiltonianAngularTime n i j lambda h (2 * Real.pi)

theorem continuous_chebyshevHamiltonianAngularOrbit
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianAngularOrbit n i j lambda h) := by
  apply Continuous.prodMk
  · rw [continuous_iff_continuousAt]
    intro t
    exact (chebyshevHamiltonianAngularOrbit_fst_hasDerivAt
      (i := i) (j := j) hn hlambda hh hhHalf).continuousAt
  · rw [continuous_iff_continuousAt]
    intro t
    exact (chebyshevHamiltonianAngularOrbit_snd_hasDerivAt
      (i := i) (j := j) hn hlambda hh hhHalf).continuousAt

theorem continuous_chebyshevHamiltonianAngularTimeFactor
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianAngularTimeFactor n i j lambda h) := by
  have horbit := continuous_chebyshevHamiltonianAngularOrbit
    (i := i) (j := j) hn hlambda hh hhHalf
  have hx : Continuous (fun t => chebyshevForwardDerivative n
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).1) := by
    exact (Polynomial.continuous
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative).comp
      horbit.fst
  have hy : Continuous (fun t => chebyshevForwardDerivative n
      (chebyshevHamiltonianAngularOrbit n i j lambda h t).2) := by
    exact (Polynomial.continuous
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative).comp
      horbit.snd
  unfold chebyshevHamiltonianAngularTimeFactor
  exact continuous_const.mul ((continuous_const.mul hx).mul hy)

theorem chebyshevHamiltonianAngularTimeFactor_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    0 < chebyshevHamiltonianAngularTimeFactor n i j lambda h t := by
  exact chebyshevHamiltonianAngular_timeFactor_pos hn hi hj
    hlambda hh hhHalf

theorem continuous_chebyshevHamiltonianAngularTimeDensity
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianAngularTimeDensity n i j lambda h) := by
  unfold chebyshevHamiltonianAngularTimeDensity
  exact (continuous_chebyshevHamiltonianAngularTimeFactor hn hlambda hh hhHalf).inv₀
    (fun t => (chebyshevHamiltonianAngularTimeFactor_pos hn hi hj
      hlambda hh hhHalf).ne')

theorem chebyshevHamiltonianAngularTimeDensity_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    0 < chebyshevHamiltonianAngularTimeDensity n i j lambda h t := by
  exact inv_pos.mpr (chebyshevHamiltonianAngularTimeFactor_pos
    hn hi hj hlambda hh hhHalf)

@[simp]
theorem chebyshevHamiltonianAngularTime_zero
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevHamiltonianAngularTime n i j lambda h 0 = 0 := by
  simp [chebyshevHamiltonianAngularTime]

theorem chebyshevHamiltonianAngularTime_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    HasDerivAt (chebyshevHamiltonianAngularTime n i j lambda h)
      (chebyshevHamiltonianAngularTimeDensity n i j lambda h t) t := by
  let density := chebyshevHamiltonianAngularTimeDensity n i j lambda h
  have hcont : Continuous density :=
    continuous_chebyshevHamiltonianAngularTimeDensity hn hi hj
      hlambda hh hhHalf
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 t)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt

theorem strictMono_chebyshevHamiltonianAngularTime
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    StrictMono (chebyshevHamiltonianAngularTime n i j lambda h) := by
  let density := chebyshevHamiltonianAngularTimeDensity n i j lambda h
  have hcont : Continuous density :=
    continuous_chebyshevHamiltonianAngularTimeDensity hn hi hj
      hlambda hh hhHalf
  intro a b hab
  have hpos : 0 < ∫ u in a..b, density u :=
    intervalIntegral.intervalIntegral_pos_of_pos (hcont.intervalIntegrable a b)
      (fun t => chebyshevHamiltonianAngularTimeDensity_pos
        hn hi hj hlambda hh hhHalf) hab
  have hadd :
      (∫ u in 0..a, density u) + (∫ u in a..b, density u) =
        ∫ u in 0..b, density u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a b)
  change (∫ u in 0..a, density u) < ∫ u in 0..b, density u
  rw [← hadd]
  linarith

theorem chebyshevHamiltonianAngularPeriod_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    0 < chebyshevHamiltonianAngularPeriod n i j lambda h := by
  have hmono := strictMono_chebyshevHamiltonianAngularTime
    hn hi hj hlambda hh hhHalf
  have hlt := hmono (show (0 : ℝ) < 2 * Real.pi by positivity)
  simpa [chebyshevHamiltonianAngularPeriod] using hlt

theorem continuous_chebyshevHamiltonianAngularTime
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianAngularTime n i j lambda h) := by
  exact intervalIntegral.differentiable_integral_of_continuous
    (continuous_chebyshevHamiltonianAngularTimeDensity
      hn hi hj hlambda hh hhHalf) |>.continuous

/-- The positive integrated clock is an order isomorphism from one angular
turn onto the corresponding physical-time interval. -/
noncomputable def chebyshevHamiltonianAngularTimeOrderIso
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Set.Icc (0 : ℝ) (2 * Real.pi) ≃o
      Set.Icc (0 : ℝ) (chebyshevHamiltonianAngularPeriod n i j lambda h) := by
  let time := chebyshevHamiltonianAngularTime n i j lambda h
  have hmono : StrictMono time :=
    strictMono_chebyshevHamiltonianAngularTime hn hi hj hlambda hh hhHalf
  have hcont : Continuous time :=
    continuous_chebyshevHamiltonianAngularTime hn hi hj hlambda hh hhHalf
  have himage : time '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      Set.Icc (0 : ℝ) (chebyshevHamiltonianAngularPeriod n i j lambda h) := by
    simpa [time, chebyshevHamiltonianAngularPeriod] using
      hcont.image_Icc_of_strictMono
        (a := (0 : ℝ)) (b := 2 * Real.pi) hmono
  exact ((hmono.strictMonoOn _).orderIso time _).trans
    (OrderIso.setCongr _ _ himage)

/-- Extend the inverse positive clock constantly outside its physical
one-period interval.  On the interior this is the genuine inverse of
`chebyshevHamiltonianAngularTime`. -/
noncomputable def chebyshevHamiltonianPhysicalAngle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) : ℝ → ℝ :=
  Set.IccExtend
    (chebyshevHamiltonianAngularPeriod_pos
      hn hi hj hlambda hh hhHalf).le
    (fun tau =>
      ↑((chebyshevHamiltonianAngularTimeOrderIso
        hn hi hj hlambda hh hhHalf).symm tau))

theorem continuous_chebyshevHamiltonianPhysicalAngle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianPhysicalAngle
      hn hi hj hlambda hh hhHalf) := by
  unfold chebyshevHamiltonianPhysicalAngle
  apply Continuous.Icc_extend'
  exact continuous_subtype_val.comp
    (chebyshevHamiltonianAngularTimeOrderIso
      hn hi hj hlambda hh hhHalf).symm.continuous

theorem chebyshevHamiltonianAngularTime_physicalAngle_eq_of_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Icc (0 : ℝ)
      (chebyshevHamiltonianAngularPeriod n i j lambda h)) :
    chebyshevHamiltonianAngularTime n i j lambda h
        (chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf t) = t := by
  let period := chebyshevHamiltonianAngularPeriod n i j lambda h
  let e := chebyshevHamiltonianAngularTimeOrderIso
    hn hi hj hlambda hh hhHalf
  have hperiod : 0 ≤ period :=
    (chebyshevHamiltonianAngularPeriod_pos
      hn hi hj hlambda hh hhHalf).le
  have hproj : Set.projIcc (0 : ℝ) period hperiod t = ⟨t, ht⟩ :=
    Set.projIcc_of_mem hperiod ht
  change chebyshevHamiltonianAngularTime n i j lambda h
      (↑(e.symm (Set.projIcc 0 period hperiod t))) = t
  rw [hproj]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)

/-- On one angular turn, the extended inverse clock is also a right
inverse. -/
theorem chebyshevHamiltonianPhysicalAngle_angularTime_eq_of_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h s : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (hs : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
        (chebyshevHamiltonianAngularTime n i j lambda h s) = s := by
  let time := chebyshevHamiltonianAngularTime n i j lambda h
  have hmono : StrictMono time :=
    strictMono_chebyshevHamiltonianAngularTime hn hi hj hlambda hh hhHalf
  have htimeMem : time s ∈ Set.Icc (0 : ℝ)
      (chebyshevHamiltonianAngularPeriod n i j lambda h) := by
    constructor
    · simpa [time, chebyshevHamiltonianAngularTime_zero] using
        hmono.monotone hs.1
    · simpa [time, chebyshevHamiltonianAngularPeriod] using
        hmono.monotone hs.2
  apply hmono.injective
  exact chebyshevHamiltonianAngularTime_physicalAngle_eq_of_mem
    hn hi hj hlambda hh hhHalf htimeMem

theorem chebyshevHamiltonianPhysicalAngle_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf t ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) := by
  let period := chebyshevHamiltonianAngularPeriod n i j lambda h
  let e := chebyshevHamiltonianAngularTimeOrderIso
    hn hi hj hlambda hh hhHalf
  have hperiod : 0 ≤ period :=
    (chebyshevHamiltonianAngularPeriod_pos
      hn hi hj hlambda hh hhHalf).le
  change ((e.symm (Set.projIcc 0 period hperiod t) :
    Set.Icc (0 : ℝ) (2 * Real.pi))).1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
  exact (e.symm (Set.projIcc 0 period hperiod t)).property

theorem chebyshevHamiltonianPhysicalAngle_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianAngularPeriod n i j lambda h)) :
    HasDerivAt
      (chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf)
      (chebyshevHamiltonianAngularTimeFactor n i j lambda h
        (chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf t)) t := by
  let angle := chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
  have hcont : ContinuousAt angle t :=
    (continuous_chebyshevHamiltonianPhysicalAngle
      hn hi hj hlambda hh hhHalf).continuousAt
  have htime := chebyshevHamiltonianAngularTime_hasDerivAt
    hn hi hj hlambda hh hhHalf (t := angle t)
  have hdensity : chebyshevHamiltonianAngularTimeDensity n i j lambda h
      (angle t) ≠ 0 :=
    (chebyshevHamiltonianAngularTimeDensity_pos
      hn hi hj hlambda hh hhHalf).ne'
  have hinverse : ∀ᶠ y in 𝓝 t,
      chebyshevHamiltonianAngularTime n i j lambda h (angle y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact chebyshevHamiltonianAngularTime_physicalAngle_eq_of_mem
      hn hi hj hlambda hh hhHalf hy
  have hderiv := htime.of_local_left_inverse hcont hdensity hinverse
  simpa [angle, chebyshevHamiltonianAngularTimeDensity] using hderiv

@[simp]
theorem chebyshevHamiltonianPhysicalAngle_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf 0 = 0 := by
  have hmono := strictMono_chebyshevHamiltonianAngularTime
    hn hi hj hlambda hh hhHalf
  apply hmono.injective
  rw [chebyshevHamiltonianAngularTime_physicalAngle_eq_of_mem
    hn hi hj hlambda hh hhHalf]
  · exact (chebyshevHamiltonianAngularTime_zero n i j lambda h).symm
  · exact ⟨le_rfl, (chebyshevHamiltonianAngularPeriod_pos
      hn hi hj hlambda hh hhHalf).le⟩

@[simp]
theorem chebyshevHamiltonianPhysicalAngle_period
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
        (chebyshevHamiltonianAngularPeriod n i j lambda h) =
      2 * Real.pi := by
  have hmono := strictMono_chebyshevHamiltonianAngularTime
    hn hi hj hlambda hh hhHalf
  apply hmono.injective
  rw [chebyshevHamiltonianAngularTime_physicalAngle_eq_of_mem
    hn hi hj hlambda hh hhHalf]
  · rfl
  · exact ⟨(chebyshevHamiltonianAngularPeriod_pos
      hn hi hj hlambda hh hhHalf).le, le_rfl⟩

/-- Angular location, in the Hamiltonian-oriented clock, of the horizontal
section point used by the Poincaré construction. -/
noncomputable def chebyshevHamiltonianSectionAngularStart (i j : ℕ) : ℝ :=
  Real.pi + chebyshevCellJacobianOrientation i j * Real.pi / 2

theorem chebyshevHamiltonianSectionAngularStart_mem_Icc (i j : ℕ) :
    chebyshevHamiltonianSectionAngularStart i j ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) := by
  rcases chebyshevCellJacobianOrientation_mem i j with ho | ho <;>
    simp [chebyshevHamiltonianSectionAngularStart, ho] <;>
    constructor <;> nlinarith [Real.pi_pos]

theorem chebyshevHamiltonianAngle_sectionAngularStart
    (i j : ℕ) :
    chebyshevHamiltonianAngle i j
      (chebyshevHamiltonianSectionAngularStart i j) = 0 := by
  rcases chebyshevCellJacobianOrientation_mem i j with ho | ho <;>
    simp [chebyshevHamiltonianAngle,
      chebyshevHamiltonianSectionAngularStart, ho] <;> ring

theorem chebyshevHamiltonianAngularOrbit_sectionAngularStart
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevHamiltonianAngularOrbit n i j lambda h
        (chebyshevHamiltonianSectionAngularStart i j) =
      chebyshevCellOrbit n i j lambda h 0 := by
  unfold chebyshevHamiltonianAngularOrbit
  rw [chebyshevHamiltonianAngle_sectionAngularStart]

/-- The explicit oval parametrized by physical Hamiltonian time. -/
noncomputable def chebyshevHamiltonianTimeOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (t : ℝ) : ℝ × ℝ :=
  chebyshevHamiltonianAngularOrbit n i j lambda h
    (chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf t)

/-- The already constructed physical-time solution passes through the
horizontal-section base point at the elapsed time assigned to its explicit
angular phase. -/
theorem chebyshevHamiltonianTimeOrbit_sectionPoint
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianTimeOrbit hn hi hj hlambda hh hhHalf
        (chebyshevHamiltonianAngularTime n i j lambda h
          (chebyshevHamiltonianSectionAngularStart i j)) =
      chebyshevCellOrbit n i j lambda h 0 := by
  unfold chebyshevHamiltonianTimeOrbit
  rw [chebyshevHamiltonianPhysicalAngle_angularTime_eq_of_mem
    hn hi hj hlambda hh hhHalf
    (chebyshevHamiltonianSectionAngularStart_mem_Icc i j)]
  exact chebyshevHamiltonianAngularOrbit_sectionAngularStart n i j lambda h

theorem chebyshevHamiltonianTimeOrbit_fst_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianAngularPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianTimeOrbit
        hn hi hj hlambda hh hhHalf s).1)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianTimeOrbit
          hn hi hj hlambda hh hhHalf t)).1 t := by
  let angle := chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
  have hcomp := (chebyshevHamiltonianAngularOrbit_fst_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf
    (t := angle t)).scomp t
      (chebyshevHamiltonianPhysicalAngle_hasDerivAt
        hn hi hj hlambda hh hhHalf ht)
  have hvector := congrArg Prod.fst
    (chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
      (i := i) (j := j) hn hlambda hh hhHalf (t := angle t))
  have hderivEq :
      chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t) •
          (chebyshevHamiltonianAngularVelocity n i j lambda h (angle t)).1 =
        (chebyshevHamiltonianVector n lambda
          (chebyshevHamiltonianAngularOrbit n i j lambda h (angle t))).1 := by
    simpa [chebyshevHamiltonianAngularTimeFactor, Prod.smul_fst] using hvector
  apply (hcomp.congr_deriv hderivEq).congr_of_eventuallyEq
  filter_upwards with s
  rfl

theorem chebyshevHamiltonianTimeOrbit_snd_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianAngularPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianTimeOrbit
        hn hi hj hlambda hh hhHalf s).2)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianTimeOrbit
          hn hi hj hlambda hh hhHalf t)).2 t := by
  let angle := chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
  have hcomp := (chebyshevHamiltonianAngularOrbit_snd_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf
    (t := angle t)).scomp t
      (chebyshevHamiltonianPhysicalAngle_hasDerivAt
        hn hi hj hlambda hh hhHalf ht)
  have hvector := congrArg Prod.snd
    (chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
      (i := i) (j := j) hn hlambda hh hhHalf (t := angle t))
  have hderivEq :
      chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t) •
          (chebyshevHamiltonianAngularVelocity n i j lambda h (angle t)).2 =
        (chebyshevHamiltonianVector n lambda
          (chebyshevHamiltonianAngularOrbit n i j lambda h (angle t))).2 := by
    simpa [chebyshevHamiltonianAngularTimeFactor, Prod.smul_snd] using hvector
  apply (hcomp.congr_deriv hderivEq).congr_of_eventuallyEq
  filter_upwards with s
  rfl

/-- The physical Hamiltonian vector field is continuous as a polynomial
map of the phase-space coordinates. -/
theorem continuous_chebyshevHamiltonianVector (n : ℕ) (lambda : ℝ) :
    Continuous (chebyshevHamiltonianVector n lambda) := by
  unfold chebyshevHamiltonianVector chebyshevHamiltonianDy
    chebyshevHamiltonianDx
  fun_prop

/-- Solving the positive time-factor identity for angular velocity. -/
theorem chebyshevHamiltonianAngularVelocity_eq_timeDensity_smul_vector
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianAngularVelocity n i j lambda h t =
      chebyshevHamiltonianAngularTimeDensity n i j lambda h t •
        chebyshevHamiltonianVector n lambda
          (chebyshevHamiltonianAngularOrbit n i j lambda h t) := by
  let factor := chebyshevHamiltonianAngularTimeFactor n i j lambda h t
  have hfactor : 0 < factor :=
    chebyshevHamiltonianAngularTimeFactor_pos
      hn hi hj hlambda hh hhHalf
  have hvector := chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
    (i := i) (j := j) hn hlambda hh hhHalf (t := t)
  change factor • chebyshevHamiltonianAngularVelocity n i j lambda h t =
    chebyshevHamiltonianVector n lambda
      (chebyshevHamiltonianAngularOrbit n i j lambda h t) at hvector
  change chebyshevHamiltonianAngularVelocity n i j lambda h t =
    factor⁻¹ • chebyshevHamiltonianVector n lambda
      (chebyshevHamiltonianAngularOrbit n i j lambda h t)
  rw [← hvector, smul_smul, inv_mul_cancel₀ hfactor.ne', one_smul]

/-- Under the oval hypotheses, the Hamiltonian-oriented angular velocity
is continuous.  The proof avoids continuity of `deriv` by solving the
positive time-factor identity. -/
theorem continuous_chebyshevHamiltonianAngularVelocity
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianAngularVelocity n i j lambda h) := by
  have hdensity := continuous_chebyshevHamiltonianAngularTimeDensity
    hn hi hj hlambda hh hhHalf
  have hvector := (continuous_chebyshevHamiltonianVector n lambda).comp
    (continuous_chebyshevHamiltonianAngularOrbit
      (i := i) (j := j) hn hlambda hh hhHalf)
  have hcontinuous : Continuous (fun t =>
      chebyshevHamiltonianAngularTimeDensity n i j lambda h t •
        chebyshevHamiltonianVector n lambda
          (chebyshevHamiltonianAngularOrbit n i j lambda h t)) :=
    hdensity.smul hvector
  apply hcontinuous.congr
  intro t
  exact (chebyshevHamiltonianAngularVelocity_eq_timeDensity_smul_vector
    hn hi hj hlambda hh hhHalf).symm

/-- A continuous integrand lets the two half-turn definitions of the
angular trace recombine into the canonical single one-turn integral. -/
theorem chebyshevHamiltonianAngularPdy_eq_oneTurn
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianAngularPdy n i j P lambda h =
      parameterizedPdy P
        (chebyshevHamiltonianAngularOrbit n i j lambda h)
        (chebyshevHamiltonianAngularVelocity n i j lambda h)
        0 (2 * Real.pi) := by
  let integrand : ℝ → ℝ := fun t =>
    P (chebyshevHamiltonianAngularOrbit n i j lambda h t) *
      (chebyshevHamiltonianAngularVelocity n i j lambda h t).2
  have hcontinuous : Continuous integrand :=
    (hP.comp (continuous_chebyshevHamiltonianAngularOrbit
      (i := i) (j := j) hn hlambda hh hhHalf)).mul
      (continuous_chebyshevHamiltonianAngularVelocity
        hn hi hj hlambda hh hhHalf).snd
  have hfirst : IntervalIntegrable integrand MeasureTheory.volume
      (0 : ℝ) Real.pi := hcontinuous.intervalIntegrable 0 Real.pi
  have hsecond : IntervalIntegrable integrand MeasureTheory.volume
      Real.pi (2 * Real.pi) :=
    hcontinuous.intervalIntegrable Real.pi (2 * Real.pi)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfirst hsecond
  unfold chebyshevHamiltonianAngularPdy parameterizedPdy
  exact hsplit

/-- The actual one-period `P dy` trace of the explicit Hamiltonian-time
solution, with velocity supplied by the Hamiltonian vector field. -/
noncomputable def chebyshevHamiltonianTimePdy
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    (P : ℝ × ℝ → ℝ) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) : ℝ :=
  parameterizedPdy P
    (chebyshevHamiltonianTimeOrbit hn hi hj hlambda hh hhHalf)
    (fun t => chebyshevHamiltonianVector n lambda
      (chebyshevHamiltonianTimeOrbit hn hi hj hlambda hh hhHalf t))
    0 (chebyshevHamiltonianAngularPeriod n i j lambda h)

/-- Positive-clock substitution identifies the genuine Hamiltonian-time
trace with the already compiled Hamiltonian-oriented angular trace. -/
theorem chebyshevHamiltonianTimePdy_eq_angularPdy
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianTimePdy hn hi hj P hlambda hh hhHalf =
      chebyshevHamiltonianAngularPdy n i j P lambda h := by
  let period := chebyshevHamiltonianAngularPeriod n i j lambda h
  let angle := chebyshevHamiltonianPhysicalAngle hn hi hj hlambda hh hhHalf
  let factor : ℝ → ℝ := fun t =>
    chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t)
  have hperiod : 0 < period :=
    chebyshevHamiltonianAngularPeriod_pos hn hi hj hlambda hh hhHalf
  have hsubst := parameterizedPdy_comp_of_deriv_nonneg P
    (chebyshevHamiltonianAngularOrbit n i j lambda h)
    (chebyshevHamiltonianAngularVelocity n i j lambda h)
    angle factor 0 period
    ((continuous_chebyshevHamiltonianPhysicalAngle
      hn hi hj hlambda hh hhHalf).continuousOn)
    (fun t ht => by
      apply chebyshevHamiltonianPhysicalAngle_hasDerivAt
        hn hi hj hlambda hh hhHalf
      simpa [min_eq_left hperiod.le, max_eq_right hperiod.le] using ht)
    (fun t _ => (chebyshevHamiltonianAngularTimeFactor_pos
      hn hi hj hlambda hh hhHalf).le)
  have hleft :
      chebyshevHamiltonianTimePdy hn hi hj P hlambda hh hhHalf =
        parameterizedPdy P
          (fun t => chebyshevHamiltonianAngularOrbit n i j lambda h (angle t))
          (fun t => factor t •
            chebyshevHamiltonianAngularVelocity n i j lambda h (angle t))
          0 period := by
    unfold chebyshevHamiltonianTimePdy
    apply parameterizedPdy_congr
    · intro t _
      rfl
    · intro t _
      exact congrArg Prod.snd
        (chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
          (i := i) (j := j) hn hlambda hh hhHalf (t := angle t)).symm
  rw [hleft, hsubst]
  simpa [angle, period] using
    (chebyshevHamiltonianAngularPdy_eq_oneTurn
      hn hi hj hP hlambda hh hhHalf).symm

/-- Therefore W4's first Melnikov displacement is exactly minus the
`P dy` trace of the explicit genuine Hamiltonian-time solution. -/
theorem chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianTimePdy
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevFirstMelnikovDisplacement n i j P lambda h =
      -chebyshevHamiltonianTimePdy hn hi hj P hlambda hh hhHalf := by
  rw [chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianAngularPdy,
    chebyshevHamiltonianTimePdy_eq_angularPdy hn hi hj hP hlambda hh hhHalf]

end Hilbert16.Spikes
