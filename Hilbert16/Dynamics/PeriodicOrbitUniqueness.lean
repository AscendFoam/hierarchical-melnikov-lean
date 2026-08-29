import Hilbert16.Foundations.PeriodicOrbit
import Hilbert16.Dynamics.ParameterizedFlow
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

namespace Hilbert16

open Set

theorem PeriodicOrbit.isCompact_carrier
    {X : PhaseSpace → PhaseSpace} (O : PeriodicOrbit X) :
    IsCompact O.carrier := by
  rcases O.exists_periodicParametrization with ⟨gamma, hgamma, hrange⟩
  rcases hgamma with ⟨T, hT, hint, hperiod, hnonconst⟩
  have hcont : Continuous gamma :=
    continuous_iff_continuousAt.2 fun t => (hint t).continuousAt
  have hper : Function.Periodic gamma T := hperiod
  rw [← hrange]
  exact hper.compact_of_continuous hT.ne' hcont

/-- Global integral curves of a `C¹` autonomous vector field that agree at
time zero agree for all time.  The proof is local on each compact time
interval and uses a Lipschitz constant on one compact phase-space ball. -/
theorem isIntegralCurve_eq_of_contDiff_of_eq_zero
    {X : PhaseSpace → PhaseSpace} (hX : ContDiff ℝ 1 X)
    {γ η : ℝ → PhaseSpace}
    (hγ : IsIntegralCurve γ (autonomousField X))
    (hη : IsIntegralCurve η (autonomousField X))
    (hzero : γ 0 = η 0) :
    γ = η := by
  funext t
  let a : ℝ := min t 0 - 1
  let b : ℝ := max t 0 + 1
  have hab : a < b := by
    dsimp [a, b]
    have hmin : min t 0 ≤ 0 := min_le_right _ _
    have hmax : 0 ≤ max t 0 := le_max_right _ _
    linarith
  have hzeroMem : (0 : ℝ) ∈ Set.Ioo a b := by
    dsimp [a, b]
    constructor
    · have hmin : min t 0 ≤ 0 := min_le_right _ _
      linarith
    · have hmax : 0 ≤ max t 0 := le_max_right _ _
      linarith
  have htMem : t ∈ Set.Icc a b := by
    dsimp [a, b]
    constructor
    · have hmin : min t 0 ≤ t := min_le_left _ _
      linarith
    · have hmax : t ≤ max t 0 := le_max_left _ _
      linarith
  have hγcont : ContinuousOn γ (Set.Icc a b) :=
    HasDerivAt.continuousOn fun s _ => hγ s
  have hηcont : ContinuousOn η (Set.Icc a b) :=
    HasDerivAt.continuousOn fun s _ => hη s
  have hγcompact : IsCompact (γ '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hγcont
  have hηcompact : IsCompact (η '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hηcont
  obtain ⟨Rγ, hRγ⟩ := hγcompact.isBounded.subset_closedBall (0 : PhaseSpace)
  obtain ⟨Rη, hRη⟩ := hηcompact.isBounded.subset_closedBall (0 : PhaseSpace)
  let R : ℝ := max Rγ Rη
  have hγmem : ∀ s ∈ Set.Icc a b,
      γ s ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro s hs
    exact le_trans (hRγ ⟨s, hs, rfl⟩) (le_max_left Rγ Rη)
  have hηmem : ∀ s ∈ Set.Icc a b,
      η s ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro s hs
    exact le_trans (hRη ⟨s, hs, rfl⟩) (le_max_right Rγ Rη)
  obtain ⟨K, hK⟩ := hX.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : PhaseSpace) R)
      (isCompact_closedBall (0 : PhaseSpace) R)
  have heq : Set.EqOn γ η (Set.Icc a b) :=
    ODE_solution_unique_of_mem_Icc
      (v := autonomousField X)
      (s := fun _ => Metric.closedBall (0 : PhaseSpace) R)
      (K := K)
      (fun _ _ => by
        change LipschitzOnWith K X (Metric.closedBall (0 : PhaseSpace) R)
        exact hK)
      hzeroMem hγcont
      (fun s _ => hγ s)
      (fun s hs => hγmem s ⟨hs.1.le, hs.2.le⟩)
      hηcont
      (fun s _ => hη s)
      (fun s hs => hηmem s ⟨hs.1.le, hs.2.le⟩)
      hzero
  exact heq htMem

/-- Two periodic-orbit carriers of a `C¹` autonomous field are either
disjoint or equal.  A common point synchronizes their parametrizations,
after which ODE uniqueness identifies the whole trajectories. -/
theorem PeriodicOrbit.carrier_eq_of_mem_of_mem
    {X : PhaseSpace → PhaseSpace} (hX : ContDiff ℝ 1 X)
    (O₁ O₂ : PeriodicOrbit X) {z : PhaseSpace}
    (hz₁ : z ∈ O₁.carrier) (hz₂ : z ∈ O₂.carrier) :
    O₁.carrier = O₂.carrier := by
  rcases O₁.exists_periodicParametrization with ⟨γ, hγ, hγrange⟩
  rcases O₂.exists_periodicParametrization with ⟨η, hη, hηrange⟩
  rcases hγ with ⟨Tγ, hTγ, hγint, hγperiodic, hγnonconst⟩
  rcases hη with ⟨Tη, hTη, hηint, hηperiodic, hηnonconst⟩
  rw [← hγrange] at hz₁
  rw [← hηrange] at hz₂
  rcases hz₁ with ⟨tγ, htγ⟩
  rcases hz₂ with ⟨tη, htη⟩
  let γ' : ℝ → PhaseSpace := fun t => γ (t + tγ)
  let η' : ℝ → PhaseSpace := fun t => η (t + tη)
  have hγ'int : IsIntegralCurve γ' (autonomousField X) := by
    intro t
    simpa [γ', autonomousField] using
      (hγint (t + tγ)).comp_add_const t tγ
  have hη'int : IsIntegralCurve η' (autonomousField X) := by
    intro t
    simpa [η', autonomousField] using
      (hηint (t + tη)).comp_add_const t tη
  have hzero : γ' 0 = η' 0 := by
    simpa [γ', η'] using htγ.trans htη.symm
  have hcurves : γ' = η' :=
    isIntegralCurve_eq_of_contDiff_of_eq_zero hX hγ'int hη'int hzero
  rw [← hγrange, ← hηrange]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t - tγ + tη, ?_⟩
    have heq := congrFun hcurves (t - tγ)
    simpa [γ', η'] using heq.symm
  · rintro ⟨t, rfl⟩
    refine ⟨t - tη + tγ, ?_⟩
    have heq := congrFun hcurves (t - tη)
    simpa [γ', η'] using heq

theorem PeriodicOrbit.disjoint_or_carrier_eq
    {X : PhaseSpace → PhaseSpace} (hX : ContDiff ℝ 1 X)
    (O₁ O₂ : PeriodicOrbit X) :
    Disjoint O₁.carrier O₂.carrier ∨ O₁.carrier = O₂.carrier := by
  by_cases hdis : Disjoint O₁.carrier O₂.carrier
  · exact Or.inl hdis
  · rw [Set.not_disjoint_iff] at hdis
    rcases hdis with ⟨z, hz₁, hz₂⟩
    exact Or.inr (O₁.carrier_eq_of_mem_of_mem hX O₂ hz₁ hz₂)

/-- A genuine local-flow segment starting on a periodic carrier stays on
that carrier.  This is a direct interval form of autonomous ODE uniqueness. -/
theorem C1LocalFlow.apply_mem_periodicOrbit_carrier
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {mu T : ℝ} (hT : 0 ≤ T) (hX : ContDiff ℝ 1 (X mu))
    (O : PeriodicOrbit (X mu)) {z : PhaseSpace} (hz : z ∈ O.carrier)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) T, ((mu, z), t) ∈ Phi.domain) :
    Phi.flow ((mu, z), T) ∈ O.carrier := by
  rcases O.exists_periodicParametrization with ⟨gamma, hgamma, hrange⟩
  rcases hgamma with ⟨period, hperiod, hint, hperiodic, hnonconst⟩
  rw [← hrange] at hz
  rcases hz with ⟨t₀, ht₀⟩
  let c : ℝ → PhaseSpace := fun t => Phi.flow ((mu, z), t)
  let eta : ℝ → PhaseSpace := fun t => gamma (t + t₀)
  have hcderiv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt c (X mu (c t)) t := by
    intro t ht
    exact Phi.ode mu z t (hsegment t ht)
  have hetaderiv : ∀ t : ℝ, HasDerivAt eta (X mu (eta t)) t := by
    intro t
    simpa [eta, autonomousField] using
      (hint (t + t₀)).comp_add_const t t₀
  have hccont : ContinuousOn c (Set.Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn fun t ht => hcderiv t ht
  have hetacont : ContinuousOn eta (Set.Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn fun t ht => hetaderiv t
  have hccompact : IsCompact (c '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hccont
  have hetacompact : IsCompact (eta '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hetacont
  obtain ⟨Rc, hRc⟩ := hccompact.isBounded.subset_closedBall (0 : PhaseSpace)
  obtain ⟨Re, hRe⟩ := hetacompact.isBounded.subset_closedBall (0 : PhaseSpace)
  let R : ℝ := max Rc Re
  have hcmem : ∀ t ∈ Set.Icc (0 : ℝ) T,
      c t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    exact le_trans (hRc ⟨t, ht, rfl⟩) (le_max_left Rc Re)
  have hetamem : ∀ t ∈ Set.Icc (0 : ℝ) T,
      eta t ∈ Metric.closedBall (0 : PhaseSpace) R := by
    intro t ht
    exact le_trans (hRe ⟨t, ht, rfl⟩) (le_max_right Rc Re)
  obtain ⟨K, hK⟩ := hX.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : PhaseSpace) R)
      (isCompact_closedBall (0 : PhaseSpace) R)
  have hzero : c 0 = eta 0 := by
    have hc0 := Phi.initial mu z (hsegment 0 ⟨le_rfl, hT⟩)
    simpa [c, eta, ht₀] using hc0
  have heq : Set.EqOn c eta (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := autonomousField (X mu))
      (s := fun _ => Metric.closedBall (0 : PhaseSpace) R)
      (K := K)
      (fun _ _ => by
        change LipschitzOnWith K (X mu) (Metric.closedBall (0 : PhaseSpace) R)
        exact hK)
      hccont
      (fun t ht => (hcderiv t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      (fun t ht => hcmem t ⟨ht.1, ht.2.le⟩)
      hetacont
      (fun t ht => (hetaderiv t).hasDerivWithinAt)
      (fun t ht => hetamem t ⟨ht.1, ht.2.le⟩)
      hzero
  rw [← hrange]
  refine ⟨T + t₀, ?_⟩
  simpa [c, eta] using (heq ⟨hT, le_rfl⟩).symm

end Hilbert16
