import Hilbert16.Spikes.HamiltonianTimeClock

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set
open scoped Topology

/-- The Hamiltonian-oriented angular oval is genuinely `2*pi`-periodic,
not merely equal at the two endpoints of one chosen turn. -/
theorem chebyshevHamiltonianAngularOrbit_add_two_pi
    (n i j : ℕ) (lambda h t : ℝ) :
    chebyshevHamiltonianAngularOrbit n i j lambda h (t + 2 * Real.pi) =
      chebyshevHamiltonianAngularOrbit n i j lambda h t := by
  rcases chebyshevCellJacobianOrientation_mem i j with ho | ho
  · have hp := chebyshevCellOrbit_add_two_pi n i j lambda h
      (chebyshevHamiltonianAngle i j t)
    rw [chebyshevHamiltonianAngularOrbit,
      chebyshevHamiltonianAngularOrbit]
    simp only [chebyshevHamiltonianAngle, ho] at hp ⊢
    convert hp using 1 <;> ring
  · have hp := chebyshevCellOrbit_add_two_pi n i j lambda h
      (chebyshevHamiltonianAngle i j (t + 2 * Real.pi))
    rw [chebyshevHamiltonianAngularOrbit,
      chebyshevHamiltonianAngularOrbit]
    simp only [chebyshevHamiltonianAngle, ho] at hp ⊢
    convert hp.symm using 1 <;> ring

theorem chebyshevCellOrbitVelocity_add_two_pi
    (n i j : ℕ) (lambda h t : ℝ) :
    chebyshevCellOrbitVelocity n i j lambda h (t + 2 * Real.pi) =
      chebyshevCellOrbitVelocity n i j lambda h t := by
  ext <;> simp [chebyshevCellOrbitVelocity, ellipticOrbitUV,
    ellipticOrbitUVVelocity]

theorem chebyshevHamiltonianAngularTimeFactor_add_two_pi
    (n i j : ℕ) (lambda h t : ℝ) :
    chebyshevHamiltonianAngularTimeFactor n i j lambda h (t + 2 * Real.pi) =
      chebyshevHamiltonianAngularTimeFactor n i j lambda h t := by
  simp only [chebyshevHamiltonianAngularTimeFactor,
    chebyshevHamiltonianAngularOrbit_add_two_pi]

theorem chebyshevHamiltonianAngularTimeDensity_add_two_pi
    (n i j : ℕ) (lambda h t : ℝ) :
    chebyshevHamiltonianAngularTimeDensity n i j lambda h (t + 2 * Real.pi) =
      chebyshevHamiltonianAngularTimeDensity n i j lambda h t := by
  simp [chebyshevHamiltonianAngularTimeDensity,
    chebyshevHamiltonianAngularTimeFactor_add_two_pi]

theorem chebyshevHamiltonianAngularVelocity_add_two_pi
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianAngularVelocity n i j lambda h (t + 2 * Real.pi) =
      chebyshevHamiltonianAngularVelocity n i j lambda h t := by
  rw [chebyshevHamiltonianAngularVelocity_eq_timeDensity_smul_vector
    hn hi hj hlambda hh hhHalf,
    chebyshevHamiltonianAngularVelocity_eq_timeDensity_smul_vector
      hn hi hj hlambda hh hhHalf]
  rw [chebyshevHamiltonianAngularOrbit_add_two_pi]
  rw [chebyshevHamiltonianAngularTimeDensity_add_two_pi]

/-- Physical time elapsed from the Poincaré-section angular phase after
an additional angular offset `s`. -/
noncomputable def chebyshevHamiltonianSectionAngularTime
    (n i j : ℕ) (lambda h s : ℝ) : ℝ :=
  chebyshevHamiltonianAngularTime n i j lambda h
      (chebyshevHamiltonianSectionAngularStart i j + s) -
    chebyshevHamiltonianAngularTime n i j lambda h
      (chebyshevHamiltonianSectionAngularStart i j)

/-- Positive physical period measured from the section phase. -/
noncomputable def chebyshevHamiltonianSectionPeriod
    (n i j : ℕ) (lambda h : ℝ) : ℝ :=
  chebyshevHamiltonianSectionAngularTime n i j lambda h (2 * Real.pi)

@[simp]
theorem chebyshevHamiltonianSectionAngularTime_zero
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevHamiltonianSectionAngularTime n i j lambda h 0 = 0 := by
  simp [chebyshevHamiltonianSectionAngularTime]

theorem chebyshevHamiltonianSectionAngularTime_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h s : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    HasDerivAt (chebyshevHamiltonianSectionAngularTime n i j lambda h)
      (chebyshevHamiltonianAngularTimeDensity n i j lambda h
        (chebyshevHamiltonianSectionAngularStart i j + s)) s := by
  have houter := chebyshevHamiltonianAngularTime_hasDerivAt
    hn hi hj hlambda hh hhHalf
    (t := chebyshevHamiltonianSectionAngularStart i j + s)
  have hinner : HasDerivAt
      (fun u : ℝ => chebyshevHamiltonianSectionAngularStart i j + u) 1 s := by
    simpa using (hasDerivAt_id s).const_add
      (chebyshevHamiltonianSectionAngularStart i j)
  have hcomp := houter.comp s hinner
  have hshift := hcomp.const_add
    (-chebyshevHamiltonianAngularTime n i j lambda h
      (chebyshevHamiltonianSectionAngularStart i j))
  have hshift' := hshift.congr_deriv (mul_one _)
  apply hshift'.congr_of_eventuallyEq
  filter_upwards with u
  simp [chebyshevHamiltonianSectionAngularTime, Function.comp_def,
    sub_eq_add_neg, add_comm]

theorem continuous_chebyshevHamiltonianSectionAngularTime
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianSectionAngularTime n i j lambda h) := by
  have htime := continuous_chebyshevHamiltonianAngularTime
    hn hi hj hlambda hh hhHalf
  unfold chebyshevHamiltonianSectionAngularTime
  exact (htime.comp (continuous_const.add continuous_id)).sub continuous_const

theorem strictMono_chebyshevHamiltonianSectionAngularTime
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    StrictMono (chebyshevHamiltonianSectionAngularTime n i j lambda h) := by
  have hmono := strictMono_chebyshevHamiltonianAngularTime
    hn hi hj hlambda hh hhHalf
  intro a b hab
  unfold chebyshevHamiltonianSectionAngularTime
  have hab' : chebyshevHamiltonianSectionAngularStart i j + a <
      chebyshevHamiltonianSectionAngularStart i j + b :=
    by simpa [add_comm] using
      (add_lt_add_left hab (chebyshevHamiltonianSectionAngularStart i j))
  exact sub_lt_sub_right (hmono hab') _

theorem chebyshevHamiltonianSectionPeriod_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    0 < chebyshevHamiltonianSectionPeriod n i j lambda h := by
  rw [← chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
  exact strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf (by nlinarith [Real.pi_pos])

/-- The shifted positive clock is an order isomorphism from one angular
turn based at the section to its physical-time period. -/
noncomputable def chebyshevHamiltonianSectionTimeOrderIso
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Set.Icc (0 : ℝ) (2 * Real.pi) ≃o
      Set.Icc (0 : ℝ) (chebyshevHamiltonianSectionPeriod n i j lambda h) := by
  let time := chebyshevHamiltonianSectionAngularTime n i j lambda h
  have hmono : StrictMono time :=
    strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf
  have hcont : Continuous time :=
    continuous_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf
  have himage : time '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      Set.Icc (0 : ℝ) (chebyshevHamiltonianSectionPeriod n i j lambda h) := by
    simpa [time, chebyshevHamiltonianSectionPeriod] using
      hcont.image_Icc_of_strictMono
        (a := (0 : ℝ)) (b := 2 * Real.pi) hmono
  exact ((hmono.strictMonoOn _).orderIso time _).trans
    (OrderIso.setCongr _ _ himage)

/-- A padded section-clock equivalence.  The extra angular room makes physical
time zero and the full return period interior points of the inverse clock's
domain, which is the form needed by ODE uniqueness at the initial time. -/
noncomputable def chebyshevHamiltonianSectionPaddedTimeOrderIso
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Set.Icc (-1 : ℝ) (2 * Real.pi + 1) ≃o
      Set.Icc
        (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
        (chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1)) := by
  let time := chebyshevHamiltonianSectionAngularTime n i j lambda h
  have hmono : StrictMono time :=
    strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf
  have hcont : Continuous time :=
    continuous_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf
  have himage : time '' Set.Icc (-1 : ℝ) (2 * Real.pi + 1) =
      Set.Icc (time (-1)) (time (2 * Real.pi + 1)) := by
    exact hcont.image_Icc_of_strictMono hmono
  exact ((hmono.strictMonoOn _).orderIso time _).trans
    (OrderIso.setCongr _ _ himage)

/-- Total extension of the inverse section clock.  On the physical
one-period interval it is the genuine angular offset from the section. -/
noncomputable def chebyshevHamiltonianSectionPhysicalOffset
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) : ℝ → ℝ :=
  Set.IccExtend
    ((strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf).monotone
        (by nlinarith [Real.pi_pos]))
    (fun tau => ↑((chebyshevHamiltonianSectionPaddedTimeOrderIso
      hn hi hj hlambda hh hhHalf).symm tau))

theorem continuous_chebyshevHamiltonianSectionPhysicalOffset
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    Continuous (chebyshevHamiltonianSectionPhysicalOffset
      hn hi hj hlambda hh hhHalf) := by
  unfold chebyshevHamiltonianSectionPhysicalOffset
  apply Continuous.Icc_extend'
  exact continuous_subtype_val.comp
    (chebyshevHamiltonianSectionPaddedTimeOrderIso
      hn hi hj hlambda hh hhHalf).symm.continuous

theorem chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_padded_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Icc
      (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
      (chebyshevHamiltonianSectionAngularTime n i j lambda h
        (2 * Real.pi + 1))) :
    chebyshevHamiltonianSectionAngularTime n i j lambda h
        (chebyshevHamiltonianSectionPhysicalOffset
          hn hi hj hlambda hh hhHalf t) = t := by
  let lower := chebyshevHamiltonianSectionAngularTime n i j lambda h (-1)
  let upper := chebyshevHamiltonianSectionAngularTime n i j lambda h
    (2 * Real.pi + 1)
  let e := chebyshevHamiltonianSectionPaddedTimeOrderIso
    hn hi hj hlambda hh hhHalf
  have hlowerUpper : lower ≤ upper :=
    (strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf).monotone (by nlinarith [Real.pi_pos])
  have hproj : Set.projIcc lower upper hlowerUpper t = ⟨t, ht⟩ :=
    Set.projIcc_of_mem hlowerUpper ht
  change chebyshevHamiltonianSectionAngularTime n i j lambda h
      (↑(e.symm (Set.projIcc lower upper hlowerUpper t))) = t
  rw [hproj]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)

theorem chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Icc (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    chebyshevHamiltonianSectionAngularTime n i j lambda h
        (chebyshevHamiltonianSectionPhysicalOffset
          hn hi hj hlambda hh hhHalf t) = t := by
  apply chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_padded_mem
    hn hi hj hlambda hh hhHalf
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  constructor
  · exact (calc
      chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) <
          chebyshevHamiltonianSectionAngularTime n i j lambda h 0 :=
        hmono (by norm_num)
      _ = 0 := chebyshevHamiltonianSectionAngularTime_zero n i j lambda h
      _ ≤ t := ht.1).le
  · exact (calc
      t ≤ chebyshevHamiltonianSectionPeriod n i j lambda h := ht.2
      _ = chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi) := rfl
      _ < chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1) := hmono (by norm_num)).le

theorem chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt_of_padded_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo
      (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
      (chebyshevHamiltonianSectionAngularTime n i j lambda h
        (2 * Real.pi + 1))) :
    HasDerivAt
      (chebyshevHamiltonianSectionPhysicalOffset
        hn hi hj hlambda hh hhHalf)
      (chebyshevHamiltonianAngularTimeFactor n i j lambda h
        (chebyshevHamiltonianSectionAngularStart i j +
          chebyshevHamiltonianSectionPhysicalOffset
            hn hi hj hlambda hh hhHalf t)) t := by
  let offset := chebyshevHamiltonianSectionPhysicalOffset
    hn hi hj hlambda hh hhHalf
  have hcont : ContinuousAt offset t :=
    (continuous_chebyshevHamiltonianSectionPhysicalOffset
      hn hi hj hlambda hh hhHalf).continuousAt
  have htime := chebyshevHamiltonianSectionAngularTime_hasDerivAt
    hn hi hj hlambda hh hhHalf (s := offset t)
  have hdensity : chebyshevHamiltonianAngularTimeDensity n i j lambda h
      (chebyshevHamiltonianSectionAngularStart i j + offset t) ≠ 0 :=
    (chebyshevHamiltonianAngularTimeDensity_pos
      hn hi hj hlambda hh hhHalf).ne'
  have hinverse : ∀ᶠ y in 𝓝 t,
      chebyshevHamiltonianSectionAngularTime n i j lambda h (offset y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_padded_mem
      hn hi hj hlambda hh hhHalf hy
  have hderiv := htime.of_local_left_inverse hcont hdensity hinverse
  simpa [offset, chebyshevHamiltonianAngularTimeDensity] using hderiv

theorem chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    HasDerivAt
      (chebyshevHamiltonianSectionPhysicalOffset
        hn hi hj hlambda hh hhHalf)
      (chebyshevHamiltonianAngularTimeFactor n i j lambda h
        (chebyshevHamiltonianSectionAngularStart i j +
          chebyshevHamiltonianSectionPhysicalOffset
            hn hi hj hlambda hh hhHalf t)) t := by
  apply chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt_of_padded_mem
    hn hi hj hlambda hh hhHalf
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  constructor
  · calc
      chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) < 0 := by
        rw [← chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
        exact hmono (by norm_num)
      _ < t := ht.1
  · calc
      t < chebyshevHamiltonianSectionPeriod n i j lambda h := ht.2
      _ = chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi) := rfl
      _ < chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1) := hmono (by norm_num)

@[simp]
theorem chebyshevHamiltonianSectionPhysicalOffset_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionPhysicalOffset
      hn hi hj hlambda hh hhHalf 0 = 0 := by
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  apply hmono.injective
  rw [chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_mem
    hn hi hj hlambda hh hhHalf]
  · exact (chebyshevHamiltonianSectionAngularTime_zero n i j lambda h).symm
  · exact ⟨le_rfl, (chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh hhHalf).le⟩

@[simp]
theorem chebyshevHamiltonianSectionPhysicalOffset_period
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionPhysicalOffset hn hi hj hlambda hh hhHalf
        (chebyshevHamiltonianSectionPeriod n i j lambda h) =
      2 * Real.pi := by
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  apply hmono.injective
  rw [chebyshevHamiltonianSectionAngularTime_physicalOffset_eq_of_mem
    hn hi hj hlambda hh hhHalf]
  · rfl
  · exact ⟨(chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh hhHalf).le, le_rfl⟩

/-- The explicit Hamiltonian-time oval with time zero placed at the
Poincaré-section base point. -/
noncomputable def chebyshevHamiltonianSectionTimeOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (t : ℝ) : ℝ × ℝ :=
  chebyshevHamiltonianAngularOrbit n i j lambda h
    (chebyshevHamiltonianSectionAngularStart i j +
      chebyshevHamiltonianSectionPhysicalOffset
        hn hi hj hlambda hh hhHalf t)

@[simp]
theorem chebyshevHamiltonianSectionTimeOrbit_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionTimeOrbit hn hi hj hlambda hh hhHalf 0 =
      chebyshevCellOrbit n i j lambda h 0 := by
  simp [chebyshevHamiltonianSectionTimeOrbit,
    chebyshevHamiltonianAngularOrbit_sectionAngularStart]

@[simp]
theorem chebyshevHamiltonianSectionTimeOrbit_period
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionTimeOrbit hn hi hj hlambda hh hhHalf
        (chebyshevHamiltonianSectionPeriod n i j lambda h) =
      chebyshevCellOrbit n i j lambda h 0 := by
  rw [chebyshevHamiltonianSectionTimeOrbit,
    chebyshevHamiltonianSectionPhysicalOffset_period]
  rw [chebyshevHamiltonianAngularOrbit_add_two_pi]
  exact chebyshevHamiltonianAngularOrbit_sectionAngularStart n i j lambda h

theorem chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt_of_padded_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo
      (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
      (chebyshevHamiltonianSectionAngularTime n i j lambda h
        (2 * Real.pi + 1))) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf s).1)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianSectionTimeOrbit
          hn hi hj hlambda hh hhHalf t)).1 t := by
  let offset := chebyshevHamiltonianSectionPhysicalOffset
    hn hi hj hlambda hh hhHalf
  let angle : ℝ → ℝ := fun s =>
    chebyshevHamiltonianSectionAngularStart i j + offset s
  have hoffset := chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt_of_padded_mem
    hn hi hj hlambda hh hhHalf ht
  have hangle : HasDerivAt angle
      (chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t)) t := by
    simpa [angle] using hoffset.const_add
      (chebyshevHamiltonianSectionAngularStart i j)
  have hcomp := (chebyshevHamiltonianAngularOrbit_fst_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf (t := angle t)).scomp t hangle
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

theorem chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf s).1)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianSectionTimeOrbit
          hn hi hj hlambda hh hhHalf t)).1 t := by
  apply chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt_of_padded_mem
    hn hi hj hlambda hh hhHalf
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  constructor
  · calc
      chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) < 0 := by
        rw [← chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
        exact hmono (by norm_num)
      _ < t := ht.1
  · calc
      t < chebyshevHamiltonianSectionPeriod n i j lambda h := ht.2
      _ = chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi) := rfl
      _ < chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1) := hmono (by norm_num)

theorem chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt_of_padded_mem
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo
      (chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
      (chebyshevHamiltonianSectionAngularTime n i j lambda h
        (2 * Real.pi + 1))) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf s).2)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianSectionTimeOrbit
          hn hi hj hlambda hh hhHalf t)).2 t := by
  let offset := chebyshevHamiltonianSectionPhysicalOffset
    hn hi hj hlambda hh hhHalf
  let angle : ℝ → ℝ := fun s =>
    chebyshevHamiltonianSectionAngularStart i j + offset s
  have hoffset := chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt_of_padded_mem
    hn hi hj hlambda hh hhHalf ht
  have hangle : HasDerivAt angle
      (chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t)) t := by
    simpa [angle] using hoffset.const_add
      (chebyshevHamiltonianSectionAngularStart i j)
  have hcomp := (chebyshevHamiltonianAngularOrbit_snd_hasDerivAt
    (i := i) (j := j) hn hlambda hh hhHalf (t := angle t)).scomp t hangle
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

theorem chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2)
    (ht : t ∈ Set.Ioo (0 : ℝ)
      (chebyshevHamiltonianSectionPeriod n i j lambda h)) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s => (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf s).2)
      (chebyshevHamiltonianVector n lambda
        (chebyshevHamiltonianSectionTimeOrbit
          hn hi hj hlambda hh hhHalf t)).2 t := by
  apply chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt_of_padded_mem
    hn hi hj hlambda hh hhHalf
  have hmono := strictMono_chebyshevHamiltonianSectionAngularTime
    hn hi hj hlambda hh hhHalf
  constructor
  · calc
      chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) < 0 := by
        rw [← chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
        exact hmono (by norm_num)
      _ < t := ht.1
  · calc
      t < chebyshevHamiltonianSectionPeriod n i j lambda h := ht.2
      _ = chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi) := rfl
      _ < chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1) := hmono (by norm_num)

/-- The one-period `P dy` trace of the explicit physical-time solution whose
time origin is the Poincare-section base point. -/
noncomputable def chebyshevHamiltonianSectionTimePdy
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    (P : ℝ × ℝ → ℝ) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) : ℝ :=
  parameterizedPdy P
    (chebyshevHamiltonianSectionTimeOrbit hn hi hj hlambda hh hhHalf)
    (fun t => chebyshevHamiltonianVector n lambda
      (chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf t))
    0 (chebyshevHamiltonianSectionPeriod n i j lambda h)

/-- Shifting the physical clock to the section does not change the one-turn
Hamiltonian `P dy` trace. -/
theorem chebyshevHamiltonianSectionTimePdy_eq_angularPdy
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) :
    chebyshevHamiltonianSectionTimePdy hn hi hj P hlambda hh hhHalf =
      chebyshevHamiltonianAngularPdy n i j P lambda h := by
  let period := chebyshevHamiltonianSectionPeriod n i j lambda h
  let offset := chebyshevHamiltonianSectionPhysicalOffset
    hn hi hj hlambda hh hhHalf
  let angle : ℝ → ℝ := fun t =>
    chebyshevHamiltonianSectionAngularStart i j + offset t
  let factor : ℝ → ℝ := fun t =>
    chebyshevHamiltonianAngularTimeFactor n i j lambda h (angle t)
  have hperiod : 0 < period :=
    chebyshevHamiltonianSectionPeriod_pos hn hi hj hlambda hh hhHalf
  have hangleCont : Continuous angle :=
    continuous_const.add
      (continuous_chebyshevHamiltonianSectionPhysicalOffset
        hn hi hj hlambda hh hhHalf)
  have hsubst := parameterizedPdy_comp_of_deriv_nonneg P
    (chebyshevHamiltonianAngularOrbit n i j lambda h)
    (chebyshevHamiltonianAngularVelocity n i j lambda h)
    angle factor 0 period hangleCont.continuousOn
    (fun t ht => by
      have hoffset := chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt
        hn hi hj hlambda hh hhHalf
          (by simpa [min_eq_left hperiod.le, max_eq_right hperiod.le] using ht)
      simpa [angle, factor] using hoffset.const_add
        (chebyshevHamiltonianSectionAngularStart i j))
    (fun t _ => (chebyshevHamiltonianAngularTimeFactor_pos
      hn hi hj hlambda hh hhHalf).le)
  have hleft :
      chebyshevHamiltonianSectionTimePdy hn hi hj P hlambda hh hhHalf =
        parameterizedPdy P
          (fun t => chebyshevHamiltonianAngularOrbit n i j lambda h (angle t))
          (fun t => factor t •
            chebyshevHamiltonianAngularVelocity n i j lambda h (angle t))
          0 period := by
    unfold chebyshevHamiltonianSectionTimePdy
    apply parameterizedPdy_congr
    · intro t _
      rfl
    · intro t _
      exact congrArg Prod.snd
        (chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector
          (i := i) (j := j) hn hlambda hh hhHalf (t := angle t)).symm
  rw [hleft, hsubst]
  have hangleZero : angle 0 = chebyshevHamiltonianSectionAngularStart i j := by
    simp [angle, offset]
  have hanglePeriod : angle period =
      chebyshevHamiltonianSectionAngularStart i j + 2 * Real.pi := by
    simp [angle, offset, period]
  let integrand : ℝ → ℝ := fun t =>
    P (chebyshevHamiltonianAngularOrbit n i j lambda h t) *
      (chebyshevHamiltonianAngularVelocity n i j lambda h t).2
  have hintegrandPeriodic : Function.Periodic integrand (2 * Real.pi) := by
    intro t
    simp only [integrand]
    rw [show chebyshevHamiltonianAngularOrbit n i j lambda h
        (t + 2 * Real.pi) =
        chebyshevHamiltonianAngularOrbit n i j lambda h t from
      chebyshevHamiltonianAngularOrbit_add_two_pi n i j lambda h t]
    rw [chebyshevHamiltonianAngularVelocity_add_two_pi
      hn hi hj hlambda hh hhHalf]
  have hshift := hintegrandPeriodic.intervalIntegral_add_eq
    (chebyshevHamiltonianSectionAngularStart i j) 0
  have hshiftPdy :
      parameterizedPdy P
          (chebyshevHamiltonianAngularOrbit n i j lambda h)
          (chebyshevHamiltonianAngularVelocity n i j lambda h)
          (chebyshevHamiltonianSectionAngularStart i j)
          (chebyshevHamiltonianSectionAngularStart i j + 2 * Real.pi) =
        parameterizedPdy P
          (chebyshevHamiltonianAngularOrbit n i j lambda h)
          (chebyshevHamiltonianAngularVelocity n i j lambda h)
          0 (2 * Real.pi) := by
    simpa [parameterizedPdy, integrand] using hshift
  rw [hangleZero, hanglePeriod, hshiftPdy]
  exact (chebyshevHamiltonianAngularPdy_eq_oneTurn
    hn hi hj hP hlambda hh hhHalf).symm

end Hilbert16.Spikes
