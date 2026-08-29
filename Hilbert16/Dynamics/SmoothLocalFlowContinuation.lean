import Hilbert16.Dynamics.SmoothLocalFlowConstruction
import Hilbert16.Dynamics.ChebyshevFlowIdentification
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

namespace Hilbert16

open Filter Set Metric
open scoped Topology

/-- Rightward uniqueness for the product-coordinate Hamiltonian ODE, with
the real inner-product scalar instances used by the explicit clock proofs. -/
theorem chebyshevHamiltonian_integralCurve_unique_on_Icc_right
    {n : ℕ} {lambda a b : ℝ} {f g : ℝ → ℝ × ℝ}
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b, RealInnerProdHasDerivAt f
      (Spikes.chebyshevHamiltonianVector n lambda (f t)) t)
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hg : ∀ t ∈ Set.Icc a b, RealInnerProdHasDerivAt g
      (Spikes.chebyshevHamiltonianVector n lambda (g t)) t)
    (hinitial : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : AddCommGroup (ℝ × ℝ) := inferInstance
  letI : Module ℝ (ℝ × ℝ) := inferInstance
  change ∀ t ∈ Set.Icc a b, HasDerivAt f
    (Spikes.chebyshevHamiltonianVector n lambda (f t)) t at hf
  change ∀ t ∈ Set.Icc a b, HasDerivAt g
    (Spikes.chebyshevHamiltonianVector n lambda (g t)) t at hg
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hfcompact : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hfcont
  have hgcompact : IsCompact (g '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hgcont
  obtain ⟨Rf, hRf⟩ := hfcompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨Rg, hRg⟩ := hgcompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let R := max Rf Rg
  have hfmem : ∀ t ∈ Set.Ico a b,
      f t ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro t ht
    exact le_trans (hRf ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_left Rf Rg)
  have hgmem : ∀ t ∈ Set.Ico a b,
      g t ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro t ht
    exact le_trans (hRg ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_right Rf Rg)
  obtain ⟨K, hK⟩ :=
    (contDiff_chebyshevHamiltonianVector n lambda).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0 : ℝ × ℝ) R)
        (isCompact_closedBall _ _)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => Spikes.chebyshevHamiltonianVector n lambda)
    (s := fun _ => Metric.closedBall (0 : ℝ × ℝ) R)
    (K := K) (fun _ _ => hK) hfcont
      (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hfmem
      hgcont (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      hgmem hinitial

/-- Iterate the glued lifted local endpoint at one fixed physical time step. -/
noncomputable def smoothPicardStepIterate
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) : ℕ → ParameterPhaseSpace → ParameterPhaseSpace
  | 0 => id
  | k + 1 => fun z => smoothPicardLiftedFlow n lambda S
      (delta, smoothPicardStepIterate n lambda S delta k z)

@[simp]
theorem smoothPicardStepIterate_zero
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (z : ParameterPhaseSpace) :
    smoothPicardStepIterate n lambda S delta 0 z = z := rfl

@[simp]
theorem smoothPicardStepIterate_succ
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) (z : ParameterPhaseSpace) :
    smoothPicardStepIterate n lambda S delta (k + 1) z =
      smoothPicardLiftedFlow n lambda S
        (delta, smoothPicardStepIterate n lambda S delta k z) := rfl

/-- Initial states for which the first `k` fixed-size Picard steps are all
defined. -/
def smoothPicardStepAdmissible
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) : ℕ → Set ParameterPhaseSpace
  | 0 => Set.univ
  | k + 1 => smoothPicardStepAdmissible n lambda S delta k ∩
      (fun z => (delta, smoothPicardStepIterate n lambda S delta k z)) ⁻¹'
        smoothPicardDomain n lambda S

@[simp]
theorem smoothPicardStepAdmissible_zero
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) :
    smoothPicardStepAdmissible n lambda S delta 0 = Set.univ := rfl

@[simp]
theorem mem_smoothPicardStepAdmissible_succ
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {z : ParameterPhaseSpace} :
    z ∈ smoothPicardStepAdmissible n lambda S delta (k + 1) ↔
      z ∈ smoothPicardStepAdmissible n lambda S delta k ∧
        (delta, smoothPicardStepIterate n lambda S delta k z) ∈
          smoothPicardDomain n lambda S :=
  Iff.rfl

/-- The fixed-step admissible set is open, and the `k`-step endpoint is jointly
`C¹` in its lifted initial state on this set. -/
theorem isOpen_and_contDiffOn_smoothPicardStep
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    IsOpen (smoothPicardStepAdmissible n lambda S delta k) ∧
      ContDiffOn ℝ 1 (smoothPicardStepIterate n lambda S delta k)
        (smoothPicardStepAdmissible n lambda S delta k) := by
  induction k with
  | zero =>
      exact ⟨isOpen_univ, contDiff_id.contDiffOn⟩
  | succ k ih =>
      let A := smoothPicardStepAdmissible n lambda S delta k
      let e := smoothPicardStepIterate n lambda S delta k
      let input : ParameterPhaseSpace → ℝ × ParameterPhaseSpace :=
        fun z => (delta, e z)
      have hinput : ContDiffOn ℝ 1 input A := by
        exact contDiff_const.contDiffOn.prodMk ih.2
      have hopen : IsOpen
          (A ∩ input ⁻¹' smoothPicardDomain n lambda S) :=
        hinput.continuousOn.isOpen_inter_preimage ih.1
          (isOpen_smoothPicardDomain n lambda S)
      have hcomp : ContDiffOn ℝ 1
          (smoothPicardLiftedFlow n lambda S ∘ input)
          (A ∩ input ⁻¹' smoothPicardDomain n lambda S) :=
        (contDiffOn_smoothPicardLiftedFlow n lambda S).comp_inter hinput
      constructor
      · simpa [smoothPicardStepAdmissible, A, input, e] using hopen
      · simpa [smoothPicardStepAdmissible, smoothPicardStepIterate,
          A, input, e, Function.comp_def] using hcomp

theorem isOpen_smoothPicardStepAdmissible
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    IsOpen (smoothPicardStepAdmissible n lambda S delta k) :=
  (isOpen_and_contDiffOn_smoothPicardStep n lambda S delta k).1

theorem contDiffOn_smoothPicardStepIterate
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    ContDiffOn ℝ 1 (smoothPicardStepIterate n lambda S delta k)
      (smoothPicardStepAdmissible n lambda S delta k) :=
  (isOpen_and_contDiffOn_smoothPicardStep n lambda S delta k).2

/-- The `k`-th continuation chart uses the `k`-step endpoint as its new local
initial state and measures local time from `k * delta`. -/
noncomputable def smoothPicardStepChart
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    (ℝ × ParameterPhaseSpace) → ParameterPhaseSpace :=
  fun p => smoothPicardLiftedFlow n lambda S
    (p.1 - k * delta, smoothPicardStepIterate n lambda S delta k p.2)

def smoothPicardStepChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) : Set (ℝ × ParameterPhaseSpace) :=
  Prod.snd ⁻¹' smoothPicardStepAdmissible n lambda S delta k ∩
    (fun p => (p.1 - k * delta,
      smoothPicardStepIterate n lambda S delta k p.2)) ⁻¹'
        smoothPicardDomain n lambda S

theorem isOpen_smoothPicardStepChartDomain
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    IsOpen (smoothPicardStepChartDomain n lambda S delta k) := by
  let A := smoothPicardStepAdmissible n lambda S delta k
  let input : (ℝ × ParameterPhaseSpace) → ℝ × ParameterPhaseSpace :=
    fun p => (p.1 - k * delta,
      smoothPicardStepIterate n lambda S delta k p.2)
  have hbase : IsOpen (Prod.snd ⁻¹' A) :=
    (isOpen_smoothPicardStepAdmissible n lambda S delta k).preimage
      (continuous_snd : Continuous (fun p : ℝ × ParameterPhaseSpace => p.2))
  have hiterate : ContDiffOn ℝ 1
      (fun p : ℝ × ParameterPhaseSpace =>
        smoothPicardStepIterate n lambda S delta k p.2)
      (Prod.snd ⁻¹' A) := by
    exact (contDiffOn_smoothPicardStepIterate n lambda S delta k).comp
      contDiff_snd.contDiffOn (fun _ hp => hp)
  have hinput : ContDiffOn ℝ 1 input (Prod.snd ⁻¹' A) := by
    exact (contDiff_fst.sub contDiff_const).contDiffOn.prodMk hiterate
  have hopen := hinput.continuousOn.isOpen_inter_preimage hbase
    (isOpen_smoothPicardDomain n lambda S)
  simpa [smoothPicardStepChartDomain, A, input, Set.mem_preimage] using hopen

theorem contDiffOn_smoothPicardStepChart
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) :
    ContDiffOn ℝ 1 (smoothPicardStepChart n lambda S delta k)
      (smoothPicardStepChartDomain n lambda S delta k) := by
  let A := smoothPicardStepAdmissible n lambda S delta k
  let input : (ℝ × ParameterPhaseSpace) → ℝ × ParameterPhaseSpace :=
    fun p => (p.1 - k * delta,
      smoothPicardStepIterate n lambda S delta k p.2)
  have hiterate : ContDiffOn ℝ 1
      (fun p : ℝ × ParameterPhaseSpace =>
        smoothPicardStepIterate n lambda S delta k p.2)
      (Prod.snd ⁻¹' A) := by
    exact (contDiffOn_smoothPicardStepIterate n lambda S delta k).comp
      contDiff_snd.contDiffOn (fun _ hp => hp)
  have hinput : ContDiffOn ℝ 1 input (Prod.snd ⁻¹' A) := by
    exact (contDiff_fst.sub contDiff_const).contDiffOn.prodMk hiterate
  have hcomp := (contDiffOn_smoothPicardLiftedFlow n lambda S).comp_inter hinput
  change ContDiffOn ℝ 1
    (fun p : ℝ × ParameterPhaseSpace => smoothPicardLiftedFlow n lambda S
      (p.1 - k * delta, smoothPicardStepIterate n lambda S delta k p.2))
    (Prod.snd ⁻¹' smoothPicardStepAdmissible n lambda S delta k ∩
      (fun p : ℝ × ParameterPhaseSpace => (p.1 - k * delta,
        smoothPicardStepIterate n lambda S delta k p.2)) ⁻¹'
          smoothPicardDomain n lambda S)
  simpa [A, input, Function.comp_def] using hcomp

/-- Each continuation chart retains the interval property in its physical
time fiber. -/
theorem smoothPicardStepChartDomain_time_segment_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} (z : ParameterPhaseSpace)
    {a b : ℝ} (hab : a ≤ b)
    (ha : (a, z) ∈ smoothPicardStepChartDomain n lambda S delta k)
    (hb : (b, z) ∈ smoothPicardStepChartDomain n lambda S delta k) :
    ∀ t ∈ Set.Icc a b,
      (t, z) ∈ smoothPicardStepChartDomain n lambda S delta k := by
  intro t ht
  refine ⟨ha.1, ?_⟩
  apply smoothPicardDomain_time_segment_mem
    (smoothPicardStepIterate n lambda S delta k z)
    (sub_le_sub_right hab ((k : ℝ) * delta)) ha.2 hb.2
  exact ⟨sub_le_sub_right ht.1 _, sub_le_sub_right ht.2 _⟩

/-- Rightward uniqueness for the lifted polynomial ODE on a compact interval. -/
theorem chebyshevLifted_integralCurve_unique_on_Icc_right
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {a b : ℝ} {f g : ℝ → ParameterPhaseSpace}
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (chebyshevLiftedField n lambda S (f t)) t)
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt g (chebyshevLiftedField n lambda S (g t)) t)
    (hinitial : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hfcompact : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hfcont
  have hgcompact : IsCompact (g '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hgcont
  obtain ⟨Rf, hRf⟩ :=
    hfcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  obtain ⟨Rg, hRg⟩ :=
    hgcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  let R := max Rf Rg
  have hfmem : ∀ t ∈ Set.Ico a b,
      f t ∈ Metric.closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRf ⟨t, Ico_subset_Icc_self ht, rfl⟩)
      (le_max_left Rf Rg)
  have hgmem : ∀ t ∈ Set.Ico a b,
      g t ∈ Metric.closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRg ⟨t, Ico_subset_Icc_self ht, rfl⟩)
      (le_max_right Rf Rg)
  obtain ⟨K, hK⟩ :=
    (contDiff_chebyshevLiftedField n lambda S).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0 : ParameterPhaseSpace) R)
        (isCompact_closedBall _ _)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => chebyshevLiftedField n lambda S)
    (s := fun _ => Metric.closedBall (0 : ParameterPhaseSpace) R)
    (K := K) (fun _ _ => hK) hfcont
      (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hfmem
      hgcont (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      hgmem hinitial

/-- Leftward uniqueness for the lifted polynomial ODE on a compact interval. -/
theorem chebyshevLifted_integralCurve_unique_on_Icc_left
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {a b : ℝ} {f g : ℝ → ParameterPhaseSpace}
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Icc a b,
      HasDerivAt f (chebyshevLiftedField n lambda S (f t)) t)
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt g (chebyshevLiftedField n lambda S (g t)) t)
    (hinitial : f b = g b) :
    Set.EqOn f g (Set.Icc a b) := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hfcompact : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hfcont
  have hgcompact : IsCompact (g '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hgcont
  obtain ⟨Rf, hRf⟩ :=
    hfcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  obtain ⟨Rg, hRg⟩ :=
    hgcompact.isBounded.subset_closedBall (0 : ParameterPhaseSpace)
  let R := max Rf Rg
  have hfmem : ∀ t ∈ Set.Ioc a b,
      f t ∈ Metric.closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRf ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩)
      (le_max_left Rf Rg)
  have hgmem : ∀ t ∈ Set.Ioc a b,
      g t ∈ Metric.closedBall (0 : ParameterPhaseSpace) R := by
    intro t ht
    exact le_trans (hRg ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩)
      (le_max_right Rf Rg)
  obtain ⟨K, hK⟩ :=
    (contDiff_chebyshevLiftedField n lambda S).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall (0 : ParameterPhaseSpace) R)
        (isCompact_closedBall _ _)
  exact ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => chebyshevLiftedField n lambda S)
    (s := fun _ => Metric.closedBall (0 : ParameterPhaseSpace) R)
    (K := K) (fun _ _ => hK) hfcont
      (fun t ht => (hf t ⟨ht.1.le, ht.2⟩).hasDerivWithinAt) hfmem
      hgcont (fun t ht => (hg t ⟨ht.1.le, ht.2⟩).hasDerivWithinAt)
      hgmem hinitial

theorem smoothPicardStepChart_center_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {z : ParameterPhaseSpace}
    (hz : z ∈ smoothPicardStepAdmissible n lambda S delta k) :
    ((k : ℝ) * delta, z) ∈
      smoothPicardStepChartDomain n lambda S delta k := by
  refine ⟨hz, ?_⟩
  simpa using smoothPicardDomain_zero_mem n lambda S
    (smoothPicardStepIterate n lambda S delta k z)

@[simp]
theorem smoothPicardStepChart_center
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) (z : ParameterPhaseSpace) :
    smoothPicardStepChart n lambda S delta k ((k : ℝ) * delta, z) =
      smoothPicardStepIterate n lambda S delta k z := by
  simp [smoothPicardStepChart, smoothPicardLiftedFlow_zero]

theorem smoothPicardStepChart_next_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {z : ParameterPhaseSpace}
    (hz : z ∈ smoothPicardStepAdmissible n lambda S delta (k + 1)) :
    (((k + 1 : ℕ) : ℝ) * delta, z) ∈
      smoothPicardStepChartDomain n lambda S delta k := by
  refine ⟨hz.1, ?_⟩
  change ((((k + 1 : ℕ) : ℝ) * delta - (k : ℝ) * delta),
    smoothPicardStepIterate n lambda S delta k z) ∈
      smoothPicardDomain n lambda S
  have hstep := hz.2
  change (delta, smoothPicardStepIterate n lambda S delta k z) ∈
    smoothPicardDomain n lambda S at hstep
  convert hstep using 1
  push_cast
  ring

theorem smoothPicardStepChart_next
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    (delta : ℝ) (k : ℕ) (z : ParameterPhaseSpace) :
    smoothPicardStepChart n lambda S delta k
        (((k + 1 : ℕ) : ℝ) * delta, z) =
      smoothPicardStepIterate n lambda S delta (k + 1) z := by
  unfold smoothPicardStepChart
  rw [show (((k + 1 : ℕ) : ℝ) * delta - (k : ℝ) * delta) = delta by
    push_cast
    ring]
  rfl

/-- Every continuation chart is an actual solution of the same lifted ODE in
its physical-time coordinate. -/
theorem smoothPicardStepChart_time_hasDerivAt
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {t : ℝ} {z : ParameterPhaseSpace}
    (hp : (t, z) ∈ smoothPicardStepChartDomain n lambda S delta k) :
    HasDerivAt (fun s : ℝ => smoothPicardStepChart n lambda S delta k (s, z))
      (chebyshevLiftedField n lambda S
        (smoothPicardStepChart n lambda S delta k (t, z))) t := by
  have hraw := smoothPicardLiftedFlow_time_hasDerivAt
    (n := n) (lambda := lambda) (S := S) hp.2
  have hinner : HasDerivAt (fun s : ℝ => s - (k : ℝ) * delta) 1 t := by
    simpa using (hasDerivAt_id t).sub_const ((k : ℝ) * delta)
  have hcomp := hraw.hasFDerivAt.comp_hasDerivAt t hinner
  simpa [smoothPicardStepChart, Function.comp_def] using hcomp

/-- Consecutive continuation charts agree wherever both are defined.  Their
common value at the intervening mesh time is the next Picard iterate, and
compact-interval ODE uniqueness propagates that equality to either side. -/
theorem smoothPicardStepChart_eq_next_of_mem
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta t : ℝ} {k : ℕ} {z : ParameterPhaseSpace}
    (hk : (t, z) ∈ smoothPicardStepChartDomain n lambda S delta k)
    (hk1 : (t, z) ∈ smoothPicardStepChartDomain n lambda S delta (k + 1)) :
    smoothPicardStepChart n lambda S delta k (t, z) =
      smoothPicardStepChart n lambda S delta (k + 1) (t, z) := by
  let c : ℝ := ((k + 1 : ℕ) : ℝ) * delta
  let f : ℝ → ParameterPhaseSpace := fun s =>
    smoothPicardStepChart n lambda S delta k (s, z)
  let g : ℝ → ParameterPhaseSpace := fun s =>
    smoothPicardStepChart n lambda S delta (k + 1) (s, z)
  have hz1 : z ∈ smoothPicardStepAdmissible n lambda S delta (k + 1) :=
    hk1.1
  have hfc : (c, z) ∈ smoothPicardStepChartDomain n lambda S delta k := by
    simpa [c] using smoothPicardStepChart_next_mem hz1
  have hgc : (c, z) ∈
      smoothPicardStepChartDomain n lambda S delta (k + 1) := by
    simpa [c] using smoothPicardStepChart_center_mem hz1
  have hcenter : f c = g c := by
    dsimp [f, g, c]
    rw [smoothPicardStepChart_next, smoothPicardStepChart_center]
  rcases le_total t c with htc | hct
  · have hfdom : ∀ s ∈ Set.Icc t c,
        (s, z) ∈ smoothPicardStepChartDomain n lambda S delta k :=
      smoothPicardStepChartDomain_time_segment_mem z htc hk hfc
    have hgdom : ∀ s ∈ Set.Icc t c,
        (s, z) ∈ smoothPicardStepChartDomain n lambda S delta (k + 1) :=
      smoothPicardStepChartDomain_time_segment_mem z htc hk1 hgc
    have hfderiv : ∀ s ∈ Set.Icc t c,
        HasDerivAt f (chebyshevLiftedField n lambda S (f s)) s := by
      intro s hs
      simpa [f] using smoothPicardStepChart_time_hasDerivAt (hfdom s hs)
    have hgderiv : ∀ s ∈ Set.Icc t c,
        HasDerivAt g (chebyshevLiftedField n lambda S (g s)) s := by
      intro s hs
      simpa [g] using smoothPicardStepChart_time_hasDerivAt (hgdom s hs)
    have heq := chebyshevLifted_integralCurve_unique_on_Icc_left
      (HasDerivAt.continuousOn hfderiv) hfderiv
      (HasDerivAt.continuousOn hgderiv) hgderiv hcenter
    exact heq ⟨le_rfl, htc⟩
  · have hfdom : ∀ s ∈ Set.Icc c t,
        (s, z) ∈ smoothPicardStepChartDomain n lambda S delta k :=
      smoothPicardStepChartDomain_time_segment_mem z hct hfc hk
    have hgdom : ∀ s ∈ Set.Icc c t,
        (s, z) ∈ smoothPicardStepChartDomain n lambda S delta (k + 1) :=
      smoothPicardStepChartDomain_time_segment_mem z hct hgc hk1
    have hfderiv : ∀ s ∈ Set.Icc c t,
        HasDerivAt f (chebyshevLiftedField n lambda S (f s)) s := by
      intro s hs
      simpa [f] using smoothPicardStepChart_time_hasDerivAt (hfdom s hs)
    have hgderiv : ∀ s ∈ Set.Icc c t,
        HasDerivAt g (chebyshevLiftedField n lambda S (g s)) s := by
      intro s hs
      simpa [g] using smoothPicardStepChart_time_hasDerivAt (hgdom s hs)
    have heq := chebyshevLifted_integralCurve_unique_on_Icc_right
      (HasDerivAt.continuousOn hfderiv) hfderiv
      (HasDerivAt.continuousOn hgderiv) hgderiv hcenter
    exact heq ⟨hct, le_rfl⟩

theorem smoothPicardStepIterate_fst
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {z : ParameterPhaseSpace}
    (hz : z ∈ smoothPicardStepAdmissible n lambda S delta k) :
    (smoothPicardStepIterate n lambda S delta k z).1 = z.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [smoothPicardStepIterate_succ,
        smoothPicardLiftedFlow_fst hz.2, ih hz.1]

theorem smoothPicardStepChart_fst
    {n : ℕ} {lambda : ℝ} {S : MvPolynomial (Fin 2) ℝ}
    {delta : ℝ} {k : ℕ} {t : ℝ} {z : ParameterPhaseSpace}
    (hp : (t, z) ∈ smoothPicardStepChartDomain n lambda S delta k) :
    (smoothPicardStepChart n lambda S delta k (t, z)).1 = z.1 := by
  rw [smoothPicardStepChart, smoothPicardLiftedFlow_fst hp.2,
    smoothPicardStepIterate_fst hp.1]

/-- Compactness turns pointwise zero-time existence into a uniform time tube
over a compact family of lifted states. -/
theorem exists_uniform_smoothPicard_time
    (n : ℕ) (lambda : ℝ) (S : MvPolynomial (Fin 2) ℝ)
    {K : Set ParameterPhaseSpace} (hK : IsCompact K) :
    ∃ epsilon > (0 : ℝ), ∀ z ∈ K, ∀ t : ℝ, |t| < epsilon →
      (t, z) ∈ smoothPicardDomain n lambda S := by
  let K₀ : Set (ℝ × ParameterPhaseSpace) :=
    (fun z : ParameterPhaseSpace => ((0 : ℝ), z)) '' K
  have hK₀ : IsCompact K₀ :=
    hK.image (continuous_const.prodMk continuous_id)
  have hsubset : K₀ ⊆ smoothPicardDomain n lambda S := by
    rintro p ⟨z, hz, rfl⟩
    exact smoothPicardDomain_zero_mem n lambda S z
  obtain ⟨epsilon, hepsilon, hthick⟩ :=
    hK₀.exists_thickening_subset_open
      (isOpen_smoothPicardDomain n lambda S) hsubset
  refine ⟨epsilon, hepsilon, fun z hz t ht => hthick ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨((0 : ℝ), z), ⟨z, hz, rfl⟩, ?_⟩
  simpa [Prod.dist_eq, Real.dist_eq] using ht

/-- The compact lifted zero-parameter section orbit admits one uniform local
Picard time step all along its full positive period. -/
theorem exists_uniform_smoothPicard_time_along_sectionOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (S : MvPolynomial (Fin 2) ℝ) :
    ∃ epsilon > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ)
          (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h),
        ∀ s : ℝ, |s| < epsilon →
          (s, ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
            hn hi hj hlambda hh hhHalf t)) ∈
            smoothPicardDomain n lambda S := by
  let period := Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h
  let orbit : ℝ → PhaseSpace :=
    chebyshevHamiltonianSectionPhaseOrbit hn hi hj hlambda hh hhHalf
  let K : Set ParameterPhaseSpace :=
    (fun t : ℝ => ((0 : ℝ), orbit t)) '' Set.Icc (0 : ℝ) period
  have horbit : ContinuousOn orbit (Set.Icc (0 : ℝ) period) := by
    exact continuousOn_chebyshevHamiltonianSectionPhaseOrbit
      hn hi hj hlambda hh hhHalf
  have hlifted : ContinuousOn (fun t : ℝ => ((0 : ℝ), orbit t))
      (Set.Icc (0 : ℝ) period) :=
    continuousOn_const.prodMk horbit
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn hlifted
  obtain ⟨epsilon, hepsilon, htube⟩ :=
    exists_uniform_smoothPicard_time n lambda S hK
  refine ⟨epsilon, hepsilon, ?_⟩
  intro t ht s hs
  exact htube _ ⟨t, by simpa [period] using ht, rfl⟩ s hs

/-- Subdivide a positive time into finitely many equal positive steps smaller
than any prescribed positive radius. -/
theorem exists_equal_time_subdivision
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧
      let delta := T / (N : ℝ)
      0 < delta ∧ delta < epsilon ∧ (N : ℝ) * delta = T := by
  obtain ⟨N, hN⟩ := exists_nat_gt (T / epsilon)
  have hratio : 0 < T / epsilon := div_pos hT hepsilon
  have hNposReal : (0 : ℝ) < N := lt_trans hratio hN
  have hNpos : 0 < N := by exact_mod_cast hNposReal
  refine ⟨N, hNpos, div_pos hT hNposReal, ?_, ?_⟩
  · rw [div_lt_iff₀ hNposReal]
    simpa [mul_comm] using (div_lt_iff₀ hepsilon).mp hN
  · exact mul_div_cancel₀ T (ne_of_gt hNposReal)

/-- One admissible Picard step from a point of the explicit zero-parameter
section orbit lands at the corresponding later point of that orbit. -/
theorem smoothPicardLiftedFlow_sectionOrbit_step
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (S : MvPolynomial (Fin 2) ℝ)
    {t₀ delta : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ)
      (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h))
    (hdelta : 0 ≤ delta)
    (hsum : t₀ + delta ≤
      Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h)
    (hdomain : ∀ s ∈ Set.Icc (0 : ℝ) delta,
      (s, ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
        hn hi hj hlambda hh hhHalf t₀)) ∈
          smoothPicardDomain n lambda S) :
    smoothPicardLiftedFlow n lambda S
        (delta, ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf t₀)) =
      ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
        hn hi hj hlambda hh hhHalf (t₀ + delta)) := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : AddCommGroup (ℝ × ℝ) := inferInstance
  letI : Module ℝ (ℝ × ℝ) := inferInstance
  let period := Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h
  let x₀ := chebyshevHamiltonianSectionPhaseOrbit
    hn hi hj hlambda hh hhHalf t₀
  let Phi := chebyshevPolynomialC1LocalFlow n lambda S
  let f : ℝ → ℝ × ℝ := fun s =>
    phaseSpaceProdEquiv (Phi.flow (((0 : ℝ), x₀), s))
  let g : ℝ → ℝ × ℝ := fun s =>
    Spikes.chebyshevHamiltonianSectionTimeOrbit
      hn hi hj hlambda hh hhHalf (t₀ + s)
  have hPhiDomain : ∀ s ∈ Set.Icc (0 : ℝ) delta,
      (((0 : ℝ), x₀), s) ∈ Phi.domain := by
    intro s hs
    change (s, ((0 : ℝ), x₀)) ∈ smoothPicardDomain n lambda S
    exact hdomain s hs
  have hfieldZero : ∀ x : PhaseSpace,
      chebyshevPerturbedPhaseVector n lambda
          (mvPolynomialProdEval (chebyshevPPolynomial n S)) 0 x =
        chebyshevPhaseHamiltonianVector n lambda x := by
    intro x
    apply phaseSpaceProdEquiv.injective
    simp [chebyshevPerturbedPhaseVector, chebyshevPerturbedVector,
      chebyshevPhaseHamiltonianVector, Spikes.chebyshevHamiltonianVector,
      Spikes.chebyshevHamiltonianDx, Spikes.chebyshevHamiltonianDy]
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) delta,
      RealInnerProdHasDerivAt f
        (Spikes.chebyshevHamiltonianVector n lambda (f s)) s := by
    intro s hs
    have hode := Phi.ode 0 x₀ s (hPhiDomain s hs)
    rw [hfieldZero] at hode
    have hout : HasFDerivAt phaseSpaceProdEquiv
        phaseSpaceProdEquiv.toContinuousLinearMap (Phi.flow ((0, x₀), s)) :=
      phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
    have hcomp := hout.comp_hasDerivAt s hode
    simpa [f, chebyshevPhaseHamiltonianVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hcomp
  have htimeMem : ∀ s ∈ Set.Icc (0 : ℝ) delta,
      t₀ + s ∈ Set.Icc (0 : ℝ) period := by
    intro s hs
    constructor
    · exact add_nonneg ht₀.1 hs.1
    · exact le_trans (by simpa [add_comm] using add_le_add_left hs.2 t₀) hsum
  have hg : ∀ s ∈ Set.Icc (0 : ℝ) delta,
      RealInnerProdHasDerivAt g
        (Spikes.chebyshevHamiltonianVector n lambda (g s)) s := by
    intro s hs
    have hmono := Spikes.strictMono_chebyshevHamiltonianSectionAngularTime
      hn hi hj hlambda hh hhHalf
    have hu := htimeMem s hs
    have huPadded : t₀ + s ∈ Set.Ioo
        (Spikes.chebyshevHamiltonianSectionAngularTime n i j lambda h (-1))
        (Spikes.chebyshevHamiltonianSectionAngularTime n i j lambda h
          (2 * Real.pi + 1)) := by
      constructor
      · calc
          Spikes.chebyshevHamiltonianSectionAngularTime n i j lambda h (-1) < 0 := by
            rw [← Spikes.chebyshevHamiltonianSectionAngularTime_zero n i j lambda h]
            exact hmono (by norm_num)
          _ ≤ t₀ + s := hu.1
      · calc
          t₀ + s ≤ period := hu.2
          _ = Spikes.chebyshevHamiltonianSectionAngularTime n i j lambda h
              (2 * Real.pi) := rfl
          _ < Spikes.chebyshevHamiltonianSectionAngularTime n i j lambda h
              (2 * Real.pi + 1) := hmono (by norm_num)
    have houter :=
      (Spikes.chebyshevHamiltonianSectionTimeOrbit_fst_hasDerivAt_of_padded_mem
        hn hi hj hlambda hh hhHalf huPadded).prodMk
      (Spikes.chebyshevHamiltonianSectionTimeOrbit_snd_hasDerivAt_of_padded_mem
        hn hi hj hlambda hh hhHalf huPadded)
    have hinner : HasDerivAt (fun r : ℝ => t₀ + r) 1 s := by
      simpa using (hasDerivAt_id s).const_add t₀
    have hcomp := houter.hasFDerivAt.comp_hasDerivAt s hinner
    simpa [g, Function.comp_def] using hcomp
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) delta) :=
    HasDerivAt.continuousOn hf
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) delta) :=
    HasDerivAt.continuousOn hg
  have hinitial : f 0 = g 0 := by
    have hinit := Phi.initial 0 x₀ (hPhiDomain 0 ⟨le_rfl, hdelta⟩)
    change phaseSpaceProdEquiv (Phi.flow ((0, x₀), 0)) =
      Spikes.chebyshevHamiltonianSectionTimeOrbit
        hn hi hj hlambda hh hhHalf (t₀ + 0)
    rw [hinit]
    simp [x₀, chebyshevHamiltonianSectionPhaseOrbit]
  have heq := chebyshevHamiltonian_integralCurve_unique_on_Icc_right
    (n := n) (lambda := lambda) hfcont hf hgcont hg hinitial
  have hend := heq ⟨hdelta, le_rfl⟩
  apply Prod.ext
  · exact smoothPicardLiftedFlow_fst (hdomain delta ⟨hdelta, le_rfl⟩)
  · apply phaseSpaceProdEquiv.injective
    simpa [f, g, Phi, chebyshevPolynomialC1LocalFlow,
      chebyshevSmoothPlanarFlow, x₀,
      chebyshevHamiltonianSectionPhaseOrbit] using hend

/-- Every admissible fixed-size Picard iterate starting at the explicit
zero-parameter section orbit agrees with the corresponding mesh point of that
orbit, up to the full positive period. -/
theorem smoothPicardStepIterate_sectionOrbit
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (S : MvPolynomial (Fin 2) ℝ)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaSmall : delta < epsilon)
    (htube : ∀ t ∈ Set.Icc (0 : ℝ)
        (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h),
      ∀ s : ℝ, |s| < epsilon →
        (s, ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf t)) ∈
          smoothPicardDomain n lambda S)
    (k : ℕ)
    (hk : (k : ℝ) * delta ≤
      Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h) :
    ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) ∈
        smoothPicardStepAdmissible n lambda S delta k ∧
      smoothPicardStepIterate n lambda S delta k
          ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) =
        ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
          hn hi hj hlambda hh hhHalf ((k : ℝ) * delta)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hmeshNonneg : 0 ≤ (k : ℝ) * delta :=
        mul_nonneg (Nat.cast_nonneg k) hdelta.le
      have hmeshLe : (k : ℝ) * delta ≤
          Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h := by
        calc
          (k : ℝ) * delta ≤ (k : ℝ) * delta + delta :=
            le_add_of_nonneg_right hdelta.le
          _ = ((k + 1 : ℕ) : ℝ) * delta := by push_cast; ring
          _ ≤ Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h := hk
      obtain ⟨hadmissible, hiterate⟩ := ih hmeshLe
      have hmeshMem : (k : ℝ) * delta ∈ Set.Icc (0 : ℝ)
          (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h) :=
        ⟨hmeshNonneg, hmeshLe⟩
      have hlocal : (delta,
          ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
            hn hi hj hlambda hh hhHalf ((k : ℝ) * delta))) ∈
          smoothPicardDomain n lambda S := by
        apply htube ((k : ℝ) * delta) hmeshMem delta
        simpa [abs_of_pos hdelta] using hdeltaSmall
      constructor
      · refine ⟨hadmissible, ?_⟩
        change (delta, smoothPicardStepIterate n lambda S delta k
          ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h)) ∈
            smoothPicardDomain n lambda S
        rw [hiterate]
        exact hlocal
      · rw [smoothPicardStepIterate_succ, hiterate]
        have hstep := smoothPicardLiftedFlow_sectionOrbit_step
          hn hi hj hlambda hh hhHalf S hmeshMem hdelta.le
          (by
            simpa [Nat.cast_add, Nat.cast_one, add_mul] using hk)
          (by
            intro s hs
            apply htube ((k : ℝ) * delta) hmeshMem s
            rw [abs_of_nonneg hs.1]
            exact lt_of_le_of_lt hs.2 hdeltaSmall)
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hstep

/-- The compact explicit section orbit admits a finite equal-step Picard
continuation through one complete period.  The admissible initial-state set is
open, the resulting endpoint is jointly `C¹` there, and the zero-parameter
section point returns to itself after the final step. -/
theorem exists_smoothPicard_sectionOrbit_period_chain
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 ≤ h)
    (hhHalf : h < 1 / 2) (S : MvPolynomial (Fin 2) ℝ) :
    ∃ (N : ℕ) (delta : ℝ),
      0 < N ∧ 0 < delta ∧
      (N : ℝ) * delta =
        Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h ∧
      IsOpen (smoothPicardStepAdmissible n lambda S delta N) ∧
      ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) ∈
        smoothPicardStepAdmissible n lambda S delta N ∧
      ContDiffOn ℝ 1 (smoothPicardStepIterate n lambda S delta N)
        (smoothPicardStepAdmissible n lambda S delta N) ∧
      smoothPicardStepIterate n lambda S delta N
          ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) =
        ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) := by
  obtain ⟨epsilon, hepsilon, htube⟩ :=
    exists_uniform_smoothPicard_time_along_sectionOrbit
      hn hi hj hlambda hh hhHalf S
  have hperiod : 0 <
      Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h :=
    Spikes.chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh hhHalf
  obtain ⟨N, hN, hdelta, hdeltaSmall, hperiodMesh⟩ :=
    exists_equal_time_subdivision hperiod hepsilon
  have htrack := smoothPicardStepIterate_sectionOrbit
    hn hi hj hlambda hh hhHalf S hepsilon hdelta hdeltaSmall htube N
      hperiodMesh.le
  refine ⟨N, _, hN, hdelta, hperiodMesh,
    isOpen_smoothPicardStepAdmissible n lambda S _ N,
    htrack.1,
    contDiffOn_smoothPicardStepIterate n lambda S _ N, ?_⟩
  calc
    smoothPicardStepIterate n lambda S _ N
        ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) =
      ((0 : ℝ), chebyshevHamiltonianSectionPhaseOrbit
        hn hi hj hlambda hh hhHalf ((N : ℝ) *
          (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h /
            (N : ℝ)))) := htrack.2
    _ = ((0 : ℝ), chebyshevPhaseSectionPoint n i j lambda h) := by
      rw [hperiodMesh]
      simp

end Hilbert16
