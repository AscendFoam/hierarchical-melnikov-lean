import Hilbert16.Dynamics.SmoothLocalFlowContinuation

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

/-- Restrict the `k`-th continuation chart to the open time strip of radius
one step about its mesh center.  Nonconsecutive strips are disjoint. -/
def smoothPicardRestrictedStepChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) : Set (ℝ × ParameterPhaseSpace) :=
  smoothPicardStepChartDomain n lambda S delta k ∩
    Prod.fst ⁻¹' Set.Ioo
      ((k : ℝ) * delta - delta) ((k : ℝ) * delta + delta)

theorem isOpen_smoothPicardRestrictedStepChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    IsOpen (smoothPicardRestrictedStepChartDomain n lambda S delta k) := by
  exact (isOpen_smoothPicardStepChartDomain n lambda S delta k).inter
    (isOpen_Ioo.preimage continuous_fst)

/-- The restricted chart in the `(initial state, time)` argument order used
by `C1LocalFlow`. -/
def smoothPicardFiniteChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) : Set (ParameterPhaseSpace × ℝ) :=
  (fun p : ParameterPhaseSpace × ℝ => (p.2, p.1)) ⁻¹'
    smoothPicardRestrictedStepChartDomain n lambda S delta k

noncomputable def smoothPicardFiniteChart
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    ParameterPhaseSpace × ℝ → ParameterPhaseSpace :=
  fun p => smoothPicardStepChart n lambda S delta k (p.2, p.1)

theorem isOpen_smoothPicardFiniteChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    IsOpen (smoothPicardFiniteChartDomain n lambda S delta k) := by
  exact (isOpen_smoothPicardRestrictedStepChartDomain n lambda S delta k).preimage
    (continuous_snd.prodMk continuous_fst)

theorem contDiffOn_smoothPicardFiniteChart
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    ContDiffOn ℝ 1 (smoothPicardFiniteChart n lambda S delta k)
      (smoothPicardFiniteChartDomain n lambda S delta k) := by
  have hswap : ContDiff ℝ 1
      (fun p : ParameterPhaseSpace × ℝ => (p.2, p.1)) := by
    fun_prop
  exact (contDiffOn_smoothPicardStepChart n lambda S delta k).comp
    hswap.contDiffOn (fun _ hp => hp.1)

/-- Two open strips of radius `delta` can overlap only when their natural
indices are equal or consecutive. -/
theorem smoothPicard_strip_indices_eq_or_adjacent
    {delta t : ℝ} (hdelta : 0 < delta) {k l : ℕ}
    (hk : t ∈ Set.Ioo ((k : ℝ) * delta - delta)
      ((k : ℝ) * delta + delta))
    (hl : t ∈ Set.Ioo ((l : ℝ) * delta - delta)
      ((l : ℝ) * delta + delta)) :
    k = l ∨ k + 1 = l ∨ l + 1 = k := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · by_cases hsucc : k + 1 = l
    · exact Or.inr (Or.inl hsucc)
    · have htwo : k + 2 ≤ l := by omega
      have hcast : ((k + 2 : ℕ) : ℝ) ≤ (l : ℝ) := by
        exact_mod_cast htwo
      have hmul := mul_le_mul_of_nonneg_right hcast hdelta.le
      push_cast at hmul
      exfalso
      nlinarith [hk.2, hl.1]
  · exact Or.inl hkl
  · by_cases hsucc : l + 1 = k
    · exact Or.inr (Or.inr hsucc)
    · have htwo : l + 2 ≤ k := by omega
      have hcast : ((l + 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast htwo
      have hmul := mul_le_mul_of_nonneg_right hcast hdelta.le
      push_cast at hmul
      exfalso
      nlinarith [hk.1, hl.2]

/-- Restricted finite charts agree on every overlap. -/
theorem smoothPicardFiniteChart_eq_of_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {k l : ℕ}
    {p : ParameterPhaseSpace × ℝ}
    (hk : p ∈ smoothPicardFiniteChartDomain n lambda S delta k)
    (hl : p ∈ smoothPicardFiniteChartDomain n lambda S delta l) :
    smoothPicardFiniteChart n lambda S delta k p =
      smoothPicardFiniteChart n lambda S delta l p := by
  rcases smoothPicard_strip_indices_eq_or_adjacent hdelta hk.2 hl.2 with
    hEq | hNext | hPrev
  · subst l
    rfl
  · subst l
    exact smoothPicardStepChart_eq_next_of_mem hk.1 hl.1
  · subst k
    exact (smoothPicardStepChart_eq_next_of_mem hl.1 hk.1).symm

/-- Open union of the first `N+1` restricted continuation charts. -/
def smoothPicardFiniteContinuationDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (N : ℕ) : Set (ParameterPhaseSpace × ℝ) :=
  ⋃ k : Fin (N + 1), smoothPicardFiniteChartDomain n lambda S delta k

theorem isOpen_smoothPicardFiniteContinuationDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (N : ℕ) :
    IsOpen (smoothPicardFiniteContinuationDomain n lambda S delta N) := by
  exact isOpen_iUnion fun k =>
    isOpen_smoothPicardFiniteChartDomain n lambda S delta k

/-- Select one chart containing a point of the finite continuation domain. -/
noncomputable def smoothPicardFiniteChartIndex
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (N : ℕ) (p : ParameterPhaseSpace × ℝ) : Fin (N + 1) := by
  classical
  exact if hp : p ∈ smoothPicardFiniteContinuationDomain n lambda S delta N then
      Classical.choose (Set.mem_iUnion.mp hp)
    else ⟨0, Nat.zero_lt_succ N⟩

theorem smoothPicardFiniteChartIndex_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {N : ℕ} {p : ParameterPhaseSpace × ℝ}
    (hp : p ∈ smoothPicardFiniteContinuationDomain n lambda S delta N) :
    p ∈ smoothPicardFiniteChartDomain n lambda S delta
      (smoothPicardFiniteChartIndex n lambda S delta N p) := by
  rw [smoothPicardFiniteChartIndex, dif_pos hp]
  exact Classical.choose_spec (Set.mem_iUnion.mp hp)

/-- The choice-independent lifted endpoint on the finite chart union. -/
noncomputable def smoothPicardFiniteLiftedFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (N : ℕ) :
    ParameterPhaseSpace × ℝ → ParameterPhaseSpace :=
  fun p => smoothPicardFiniteChart n lambda S delta
    (smoothPicardFiniteChartIndex n lambda S delta N p) p

theorem smoothPicardFiniteLiftedFlow_eq_chart
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N : ℕ}
    {k : Fin (N + 1)} {p : ParameterPhaseSpace × ℝ}
    (hp : p ∈ smoothPicardFiniteChartDomain n lambda S delta k) :
    smoothPicardFiniteLiftedFlow n lambda S delta N p =
      smoothPicardFiniteChart n lambda S delta k p := by
  have hpUnion : p ∈
      smoothPicardFiniteContinuationDomain n lambda S delta N :=
    Set.mem_iUnion.mpr ⟨k, hp⟩
  have hchosen := smoothPicardFiniteChartIndex_mem hpUnion
  exact smoothPicardFiniteChart_eq_of_mem hdelta hchosen hp

theorem contDiffOn_smoothPicardFiniteLiftedFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (N : ℕ) :
    ContDiffOn ℝ 1 (smoothPicardFiniteLiftedFlow n lambda S delta N)
      (smoothPicardFiniteContinuationDomain n lambda S delta N) := by
  intro p hp
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  have hchart : ContDiffAt ℝ 1 (smoothPicardFiniteChart n lambda S delta k) p :=
    (contDiffOn_smoothPicardFiniteChart n lambda S delta k p hpk).contDiffAt
      ((isOpen_smoothPicardFiniteChartDomain n lambda S delta k).mem_nhds hpk)
  have heq : Filter.EventuallyEq (nhds p)
      (smoothPicardFiniteLiftedFlow n lambda S delta N)
      (smoothPicardFiniteChart n lambda S delta k) := by
    filter_upwards [
      (isOpen_smoothPicardFiniteChartDomain n lambda S delta k).eventually_mem hpk]
      with q hq
    exact smoothPicardFiniteLiftedFlow_eq_chart hdelta hq
  exact (hchart.congr_of_eventuallyEq heq).contDiffWithinAt

theorem smoothPicardFiniteContinuationDomain_zero_mem
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (N : ℕ)
    (z : ParameterPhaseSpace) :
    (z, (0 : ℝ)) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N := by
  let k₀ : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  apply Set.mem_iUnion.mpr
  refine ⟨k₀, ?_⟩
  constructor
  · simpa [k₀] using smoothPicardStepChart_center_mem
      (show z ∈ smoothPicardStepAdmissible n lambda S delta 0 by simp)
  · simpa [k₀] using hdelta

theorem smoothPicardFiniteLiftedFlow_zero
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    {delta : ℝ} (hdelta : 0 < delta) (N : ℕ)
    (z : ParameterPhaseSpace) :
    smoothPicardFiniteLiftedFlow n lambda S delta N (z, 0) = z := by
  let k₀ : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  have hk₀ : (z, (0 : ℝ)) ∈
      smoothPicardFiniteChartDomain n lambda S delta k₀ := by
    constructor
    · simpa [k₀] using smoothPicardStepChart_center_mem
        (show z ∈ smoothPicardStepAdmissible n lambda S delta 0 by simp)
    · simpa [k₀] using hdelta
  rw [smoothPicardFiniteLiftedFlow_eq_chart hdelta hk₀]
  simpa [k₀, smoothPicardFiniteChart, smoothPicardStepChart] using
    smoothPicardLiftedFlow_zero n lambda S z

theorem smoothPicardFiniteLiftedFlow_fst
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N : ℕ}
    {p : ParameterPhaseSpace × ℝ}
    (hp : p ∈ smoothPicardFiniteContinuationDomain n lambda S delta N) :
    (smoothPicardFiniteLiftedFlow n lambda S delta N p).1 = p.1.1 := by
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  rw [smoothPicardFiniteLiftedFlow_eq_chart hdelta hpk]
  exact smoothPicardStepChart_fst hpk.1

theorem smoothPicardFiniteLiftedFlow_time_hasDerivAt
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N : ℕ}
    {z : ParameterPhaseSpace} {t : ℝ}
    (hp : (z, t) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N) :
    HasDerivAt
      (fun s : ℝ => smoothPicardFiniteLiftedFlow n lambda S delta N (z, s))
      (chebyshevLiftedField n lambda S
        (smoothPicardFiniteLiftedFlow n lambda S delta N (z, t))) t := by
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  have hraw := smoothPicardStepChart_time_hasDerivAt hpk.1
  have heq : Filter.EventuallyEq (nhds t)
      (fun s : ℝ => smoothPicardFiniteLiftedFlow n lambda S delta N (z, s))
      (fun s : ℝ => smoothPicardFiniteChart n lambda S delta k (z, s)) := by
    have hopen := isOpen_smoothPicardFiniteChartDomain n lambda S delta k
    have hinput : Continuous (fun s : ℝ => (z, s)) :=
      continuous_const.prodMk continuous_id
    filter_upwards [hinput.continuousAt.eventually_mem (hopen.mem_nhds hpk)] with s hs
    exact smoothPicardFiniteLiftedFlow_eq_chart hdelta hs
  have hcongr := hraw.congr_of_eventuallyEq heq
  rw [smoothPicardFiniteLiftedFlow_eq_chart hdelta hpk]
  simpa [smoothPicardFiniteChart] using hcongr

theorem smoothPicardFiniteChart_center_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {k : ℕ}
    {z : ParameterPhaseSpace}
    (hz : z ∈ smoothPicardStepAdmissible n lambda S delta k) :
    (z, (k : ℝ) * delta) ∈
      smoothPicardFiniteChartDomain n lambda S delta k := by
  constructor
  · exact smoothPicardStepChart_center_mem hz
  · constructor <;> nlinarith

/-- Every already-completed mesh segment belongs to the finite chart union. -/
theorem smoothPicardFiniteContinuationDomain_mesh_segment_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N k : ℕ} (hkN : k ≤ N)
    {z : ParameterPhaseSpace}
    (hz : z ∈ smoothPicardStepAdmissible n lambda S delta k) :
    ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * delta),
      (z, t) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N := by
  induction k with
  | zero =>
      intro t ht
      have ht0 : t = 0 := by simpa using ht
      subst t
      exact smoothPicardFiniteContinuationDomain_zero_mem
        n lambda S hdelta N z
  | succ k ih =>
      intro t ht
      have hkN' : k ≤ N := by omega
      have hsuccN : k + 1 ≤ N := hkN
      have hmeshEq : (((k + 1 : ℕ) : ℝ) * delta) =
          (k : ℝ) * delta + delta := by
        push_cast
        ring
      by_cases hbefore : t ≤ (k : ℝ) * delta
      · exact ih hkN' hz.1 t ⟨ht.1, hbefore⟩
      · have hafter : (k : ℝ) * delta < t := lt_of_not_ge hbefore
        by_cases hend : t = ((k + 1 : ℕ) : ℝ) * delta
        · subst t
          let q : Fin (N + 1) :=
            ⟨k + 1, by omega⟩
          apply Set.mem_iUnion.mpr
          exact ⟨q, smoothPicardFiniteChart_center_mem hdelta hz⟩
        · have htEnd : t < ((k + 1 : ℕ) : ℝ) * delta :=
            lt_of_le_of_ne ht.2 hend
          let q : Fin (N + 1) := ⟨k, by omega⟩
          apply Set.mem_iUnion.mpr
          refine ⟨q, ?_⟩
          constructor
          · apply smoothPicardStepChartDomain_time_segment_mem z
                (show (k : ℝ) * delta ≤
                  ((k + 1 : ℕ) : ℝ) * delta by nlinarith [hmeshEq])
                (smoothPicardStepChart_center_mem hz.1)
                (smoothPicardStepChart_next_mem hz)
            exact ⟨hafter.le, htEnd.le⟩
          · change t ∈ Set.Ioo
              ((k : ℝ) * delta - delta) ((k : ℝ) * delta + delta)
            rw [← hmeshEq]
            exact ⟨by nlinarith, htEnd⟩

/-- The finite chart union is star-shaped in each time fiber about time zero. -/
theorem smoothPicardFiniteContinuationDomain_zero_segment_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N : ℕ}
    {z : ParameterPhaseSpace} {t : ℝ}
    (hp : (z, t) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N) :
    ∀ s ∈ Set.uIcc (0 : ℝ) t,
      (z, s) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N := by
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  have hz : z ∈ smoothPicardStepAdmissible n lambda S delta k := hpk.1.1
  have hkN : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
  intro s hs
  rcases le_total 0 t with htNonneg | htNonpos
  · have hsIcc : s ∈ Set.Icc (0 : ℝ) t := by
      simpa [Set.uIcc_of_le htNonneg] using hs
    by_cases htMesh : t ≤ (k : ℝ) * delta
    · exact smoothPicardFiniteContinuationDomain_mesh_segment_mem
        hdelta hkN hz s ⟨hsIcc.1, hsIcc.2.trans htMesh⟩
    · have hmeshLt : (k : ℝ) * delta < t := lt_of_not_ge htMesh
      by_cases hsMesh : s ≤ (k : ℝ) * delta
      · exact smoothPicardFiniteContinuationDomain_mesh_segment_mem
          hdelta hkN hz s ⟨hsIcc.1, hsMesh⟩
      · have hmeshS : (k : ℝ) * delta ≤ s := le_of_not_ge hsMesh
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        constructor
        · apply smoothPicardStepChartDomain_time_segment_mem z hmeshLt.le
              (smoothPicardStepChart_center_mem hz) hpk.1
          exact ⟨hmeshS, hsIcc.2⟩
        · exact ⟨by nlinarith, lt_of_le_of_lt hsIcc.2 hpk.2.2⟩
  · have hsIcc : s ∈ Set.Icc t (0 : ℝ) := by
      rw [← Set.uIcc_of_le htNonpos, Set.uIcc_comm]
      exact hs
    have hkzero : (k : ℕ) = 0 := by
      by_contra hk0
      have hkOne : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
      have hkCast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkOne
      have hmul := mul_le_mul_of_nonneg_right hkCast hdelta.le
      nlinarith [hpk.2.1]
    have hkFin : k = (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) :=
      Fin.ext hkzero
    subst k
    apply Set.mem_iUnion.mpr
    let q : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    refine ⟨q, ?_⟩
    constructor
    · apply smoothPicardStepChartDomain_time_segment_mem z htNonpos
          hpk.1 (by
            simpa using smoothPicardStepChart_center_mem
              (show z ∈ smoothPicardStepAdmissible n lambda S delta 0 by simp))
      exact hsIcc
    · have hpkLower : -delta < t := by simpa using hpk.2.1
      simpa [q] using
        (⟨lt_of_lt_of_le hpkLower hsIcc.1,
          lt_of_le_of_lt hsIcc.2 hdelta⟩ : s ∈ Set.Ioo (-delta) delta)

theorem smoothPicardFiniteContinuationDomain_time_segment_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} (hdelta : 0 < delta) {N : ℕ}
    (z : ParameterPhaseSpace) {a b : ℝ} (hab : a ≤ b)
    (ha : (z, a) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N)
    (hb : (z, b) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N) :
    ∀ t ∈ Set.Icc a b,
      (z, t) ∈ smoothPicardFiniteContinuationDomain n lambda S delta N := by
  intro t ht
  rcases le_total t 0 with htNonpos | htNonneg
  · apply smoothPicardFiniteContinuationDomain_zero_segment_mem hdelta ha t
    rw [Set.uIcc_comm, Set.uIcc_of_le (ht.1.trans htNonpos)]
    exact ⟨ht.1, htNonpos⟩
  · apply smoothPicardFiniteContinuationDomain_zero_segment_mem hdelta hb t
    rw [Set.uIcc_of_le (htNonneg.trans ht.2)]
    exact ⟨htNonneg, ht.2⟩

/-- Planar component of the finite, choice-independent continuation. -/
noncomputable def chebyshevFiniteSmoothPlanarFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (N : ℕ) : ParameterPhaseSpace × ℝ → PhaseSpace :=
  fun p => (smoothPicardFiniteLiftedFlow n lambda S delta N p).2

/-- A genuine jointly `C¹` flow obtained by gluing finitely many consecutive
Picard charts.  Its open time fibers contain zero and are intervals. -/
noncomputable def chebyshevPolynomialFiniteC1LocalFlow
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (hdelta : 0 < delta) (N : ℕ) :
    C1LocalFlow (fun mu x => chebyshevPerturbedPhaseVector n lambda
      (mvPolynomialProdEval (chebyshevPPolynomial n S)) mu x) where
  flow := chebyshevFiniteSmoothPlanarFlow n lambda S delta N
  domain := smoothPicardFiniteContinuationDomain n lambda S delta N
  isOpen_domain :=
    isOpen_smoothPicardFiniteContinuationDomain n lambda S delta N
  zero_mem := by
    intro mu x
    exact smoothPicardFiniteContinuationDomain_zero_mem
      n lambda S hdelta N (mu, x)
  time_segment_mem := by
    intro mu x a b hab ha hb t ht
    exact smoothPicardFiniteContinuationDomain_time_segment_mem
      hdelta (mu, x) hab ha hb t ht
  contDiffOn_flow := by
    intro p hp
    have hlift : ContDiffAt ℝ 1
        (smoothPicardFiniteLiftedFlow n lambda S delta N) p :=
      (contDiffOn_smoothPicardFiniteLiftedFlow n lambda S hdelta N p hp).contDiffAt
        ((isOpen_smoothPicardFiniteContinuationDomain n lambda S delta N).mem_nhds hp)
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ PhaseSpace).contDiff.contDiffAt.comp
      p hlift
    change ContDiffWithinAt ℝ 1
      (fun q : ParameterPhaseSpace × ℝ =>
        (smoothPicardFiniteLiftedFlow n lambda S delta N q).2)
      (smoothPicardFiniteContinuationDomain n lambda S delta N) p
    simpa [Function.comp_def] using hsnd.contDiffWithinAt
  initial := by
    intro mu x _
    exact congrArg Prod.snd
      (smoothPicardFiniteLiftedFlow_zero n lambda S hdelta N (mu, x))
  ode := by
    intro mu x t hp
    have hlift := smoothPicardFiniteLiftedFlow_time_hasDerivAt hdelta hp
    have hsnd := (ContinuousLinearMap.snd ℝ ℝ PhaseSpace).hasFDerivAt.comp_hasDerivAt
      t hlift
    have hmu :
        (smoothPicardFiniteLiftedFlow n lambda S delta N ((mu, x), t)).1 = mu :=
      smoothPicardFiniteLiftedFlow_fst hdelta hp
    simpa [chebyshevFiniteSmoothPlanarFlow, chebyshevLiftedField,
      Spikes.parameterLift, Function.comp_def, hmu] using hsnd

/-- For the equal-step chain furnished by compactness, the finite glued flow
contains the entire explicit unperturbed period segment. -/
theorem exists_chebyshevPolynomialFiniteC1LocalFlow_sectionPeriod
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (S : MvPolynomial (Fin 2) ℝ) :
    ∃ (N : ℕ) (delta : ℝ) (hdelta : 0 < delta),
      (N : ℝ) * delta =
        Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h ∧
      ∀ t ∈ Set.Icc (0 : ℝ)
          (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h),
        ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈
          (chebyshevPolynomialFiniteC1LocalFlow
            n lambda S delta hdelta N).domain := by
  obtain ⟨N, delta, hN, hdelta, hmesh, hopen, hadmissible, hC1, hreturn⟩ :=
    exists_smoothPicard_sectionOrbit_period_chain
      hn hi hj hlambda hh hhHalf S
  refine ⟨N, delta, hdelta, hmesh, ?_⟩
  intro t ht
  apply smoothPicardFiniteContinuationDomain_mesh_segment_mem
    hdelta (le_rfl : N ≤ N) hadmissible t
  simpa [hmesh] using ht

end Hilbert16
