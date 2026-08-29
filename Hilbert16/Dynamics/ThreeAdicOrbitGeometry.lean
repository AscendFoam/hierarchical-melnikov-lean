import Hilbert16.Dynamics.ThreeAdicPeriodicOrbit
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Set

/-!
# Geometry of the indexed unperturbed orbit family
-/

/-- Reassociate the exact counting index as a marked tensor cell together
with one root slot. -/
def threeAdicCycleIndexEquiv {r : ℕ} :
    ThreeAdicCycleIndex r ≃
      Σ c : ThreeAdicTensorCell r, Fin (threeAdicBlockRootCount c.1) where
  toFun q := ⟨threeAdicCycleCell q, threeAdicCycleRootSlot q⟩
  invFun q := by
    rcases q with ⟨⟨⟨k, l⟩, i, j⟩, s⟩
    exact ⟨k, ⟨l, (i, j, s)⟩⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

theorem threeAdicCycleCell_rootSlot_injective {r : ℕ} :
    Function.Injective (fun q : ThreeAdicCycleIndex r =>
      (⟨threeAdicCycleCell q, threeAdicCycleRootSlot q⟩ :
        Σ c : ThreeAdicTensorCell r, Fin (threeAdicBlockRootCount c.1))) :=
  threeAdicCycleIndexEquiv.injective

/-- Injective root labels turn the marked cell and its selected energy into
an injective label for the exact counting index. -/
theorem threeAdicCycleCell_energy_injective
    {r : ℕ} {zeta : ℝ}
    (root : ∀ c : ThreeAdicTensorCell r,
      Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ)
    (hinj : ∀ c, Function.Injective (fun s => root c s zeta)) :
    Function.Injective (fun q : ThreeAdicCycleIndex r =>
      (threeAdicCycleCell q,
        root (threeAdicCycleCell q) (threeAdicCycleRootSlot q) zeta)) := by
  have hlabel : Function.Injective (fun q :
      Σ c : ThreeAdicTensorCell r, Fin (threeAdicBlockRootCount c.1) =>
      (q.1, root q.1 q.2 zeta)) := by
    rintro ⟨c, s⟩ ⟨d, t⟩ h
    have hcell : c = d := congrArg Prod.fst h
    subst d
    have hroot : root c s zeta = root c t zeta := congrArg Prod.snd h
    exact Sigma.ext rfl (heq_of_eq (hinj c hroot))
  intro q p hqp
  apply threeAdicCycleIndexEquiv.injective
  apply hlabel
  exact hqp

/-- Row indices from different three-adic layers cannot coincide. -/
theorem threeAdicRowIndex_ne_of_lt
    {r : ℕ} {p k : Fin r} (hpk : p < k)
    (i : ThreeAdicRow r p) (j : ThreeAdicRow r k) :
    threeAdicRowIndex i ≠ threeAdicRowIndex j := by
  intro heq
  have hi : threeAdicRowIndex i ∈ threeAdicRowSet r p := by
    simp [threeAdicRowSet]
  have hj : threeAdicRowIndex j ∈ threeAdicRowSet r k := by
    simp [threeAdicRowSet]
  exact (Finset.disjoint_left.1
    (threeAdicRowSet_disjoint_of_lt hpk k.2)) hi (heq ▸ hj)

/-- The dependent family of all three-adic rows embeds into the physical
Chebyshev row index. -/
theorem threeAdicSigmaRowIndex_injective {r : ℕ} :
    Function.Injective (fun q : Σ k : Fin r, ThreeAdicRow r k =>
      threeAdicRowIndex q.2) := by
  rintro ⟨k, i⟩ ⟨l, j⟩ heq
  by_cases hkl : k = l
  · subst l
    have hij : i = j := threeAdicRowIndex_injective heq
    subst j
    rfl
  · rcases lt_or_gt_of_ne hkl with hkl | hlk
    · exact (threeAdicRowIndex_ne_of_lt hkl i j heq).elim
    · exact (threeAdicRowIndex_ne_of_lt hlk j i heq.symm).elim

/-- A tensor cell is determined by its pair of physical row indices. -/
theorem threeAdicTensorCell_rowIndices_injective {r : ℕ} :
    Function.Injective (fun c : ThreeAdicTensorCell r =>
      (threeAdicRowIndex c.2.1, threeAdicRowIndex c.2.2)) := by
  rintro ⟨⟨k, l⟩, i, j⟩ ⟨⟨k', l'⟩, i', j'⟩ heq
  have hfirst : (⟨k, i⟩ : Σ k : Fin r, ThreeAdicRow r k) = ⟨k', i'⟩ :=
    threeAdicSigmaRowIndex_injective (congrArg Prod.fst heq)
  have hsecond : (⟨l, j⟩ : Σ l : Fin r, ThreeAdicRow r l) = ⟨l', j'⟩ :=
    threeAdicSigmaRowIndex_injective (congrArg Prod.snd heq)
  cases hfirst
  cases hsecond
  rfl

theorem continuous_chebyshevPhaseOrbit
    (n i j : ℕ) (lambda h : ℝ) :
    Continuous (chebyshevPhaseOrbit n i j lambda h) := by
  unfold chebyshevPhaseOrbit Spikes.chebyshevCellOrbit
    Spikes.chebyshevCellInverseMap Spikes.ellipticOrbitUV
    Spikes.chebyshevInverseBranch
  fun_prop

theorem chebyshevPhaseOrbit_periodic
    (n i j : ℕ) (lambda h : ℝ) :
    Function.Periodic (chebyshevPhaseOrbit n i j lambda h)
      (2 * Real.pi) := by
  intro t
  apply phaseSpaceProdEquiv.injective
  simp only [phaseSpaceProdEquiv_chebyshevPhaseOrbit]
  exact Spikes.chebyshevCellOrbit_add_two_pi n i j lambda h t

theorem isCompact_range_chebyshevPhaseOrbit
    (n i j : ℕ) (lambda h : ℝ) :
    IsCompact (Set.range (chebyshevPhaseOrbit n i j lambda h)) := by
  exact (chebyshevPhaseOrbit_periodic n i j lambda h).compact_of_continuous
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (continuous_chebyshevPhaseOrbit n i j lambda h)

/-- Different energy ovals in one cell remain disjoint after transport to
the public phase space. -/
theorem chebyshevPhaseOrbit_range_disjoint_of_energy_ne
    {n i j : ℕ} (hn : n ≠ 0) {lambda h₁ h₂ : ℝ}
    (hlambda : 1 ≤ lambda) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (hh₁Half : h₁ ≤ 1 / 2) (hh₂Half : h₂ ≤ 1 / 2)
    (hne : h₁ ≠ h₂) :
    Disjoint (Set.range (chebyshevPhaseOrbit n i j lambda h₁))
      (Set.range (chebyshevPhaseOrbit n i j lambda h₂)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t₁, rfl⟩ ⟨t₂, heq⟩
  have hprod := congrArg phaseSpaceProdEquiv heq
  exact (Set.disjoint_left.1
    (Spikes.chebyshevCellOrbit_range_disjoint_of_ne
      hn hlambda hh₁ hh₂ hh₁Half hh₂Half hne))
    ⟨t₁, rfl⟩ ⟨t₂, hprod⟩

/-- Ovals in different physical Chebyshev cells are disjoint. -/
theorem chebyshevPhaseOrbit_range_disjoint_of_cell_ne
    {n i j k l : ℕ} (hn : n ≠ 0)
    (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n)
    {lambda h₁ h₂ : ℝ} (hlambda : 1 ≤ lambda)
    (hh₁ : 0 < h₁) (hh₁Upper : h₁ < Spikes.chebyshevCommonEnergyUpper)
    (hh₂ : 0 < h₂) (hh₂Upper : h₂ < Spikes.chebyshevCommonEnergyUpper)
    (hne : (i, j) ≠ (k, l)) :
    Disjoint (Set.range (chebyshevPhaseOrbit n i j lambda h₁))
      (Set.range (chebyshevPhaseOrbit n k l lambda h₂)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t₁, rfl⟩ ⟨t₂, heq⟩
  have hmem₁ := Spikes.chebyshevCellOrbit_mem_cellRectangle
    hn hi hj hlambda hh₁ hh₁Upper (t := t₁)
  have hmem₂ := Spikes.chebyshevCellOrbit_mem_cellRectangle
    hn hk hl hlambda hh₂ hh₂Upper (t := t₂)
  have hprod := congrArg phaseSpaceProdEquiv heq
  rw [phaseSpaceProdEquiv_chebyshevPhaseOrbit,
    phaseSpaceProdEquiv_chebyshevPhaseOrbit] at hprod
  exact (Set.disjoint_left.1
    (Spikes.chebyshevCellRectangle_disjoint hn hi hj hk hl hne))
      hmem₁ (hprod ▸ hmem₂)

/-- The unperturbed oval associated with one exact counting index. -/
noncomputable def threeAdicUnperturbedCarrier
    {r : ℕ} (lambda zeta : ℝ)
    (root : ∀ c : ThreeAdicTensorCell r,
      Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ)
    (q : ThreeAdicCycleIndex r) : Set PhaseSpace :=
  Set.range (chebyshevPhaseOrbit (3 ^ r)
    (threeAdicRowIndex (threeAdicCycleCell q).2.1)
    (threeAdicRowIndex (threeAdicCycleCell q).2.2)
    lambda (root (threeAdicCycleCell q) (threeAdicCycleRootSlot q) zeta))

theorem isCompact_threeAdicUnperturbedCarrier
    {r : ℕ} (lambda zeta : ℝ)
    (root : ∀ c : ThreeAdicTensorCell r,
      Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ)
    (q : ThreeAdicCycleIndex r) :
    IsCompact (threeAdicUnperturbedCarrier lambda zeta root q) :=
  isCompact_range_chebyshevPhaseOrbit _ _ _ _ _

/-- The unperturbed ovals indexed by the exact three-adic lower-bound type
are pairwise disjoint.  Same-cell indices are separated by root-slot
injectivity; different-cell indices are separated by the physical row
rectangles. -/
theorem threeAdicUnperturbedCarrier_pairwise_disjoint
    {r : ℕ} (_hr : 1 ≤ r) {lambda zeta : ℝ}
    (hlambda : 1 ≤ lambda)
    (root : ∀ c : ThreeAdicTensorCell r,
      Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ)
    (hinj : ∀ c, Function.Injective (fun s => root c s zeta))
    (hpos : ∀ c s, 0 < root c s zeta)
    (hupper : ∀ c s,
      root c s zeta < Spikes.chebyshevCommonEnergyUpper) :
    Pairwise (fun q p => Disjoint
      (threeAdicUnperturbedCarrier lambda zeta root q)
      (threeAdicUnperturbedCarrier lambda zeta root p)) := by
  intro q p hqp
  let cq := threeAdicCycleCell q
  let cp := threeAdicCycleCell p
  by_cases hcell : cq = cp
  · have hcell' : threeAdicCycleCell q = threeAdicCycleCell p := by
      simpa [cq, cp] using hcell
    have hrow₁ :
        threeAdicRowIndex (threeAdicCycleCell p).2.1 =
          threeAdicRowIndex (threeAdicCycleCell q).2.1 :=
      congrArg (fun c : ThreeAdicTensorCell r => threeAdicRowIndex c.2.1)
        hcell'.symm
    have hrow₂ :
        threeAdicRowIndex (threeAdicCycleCell p).2.2 =
          threeAdicRowIndex (threeAdicCycleCell q).2.2 :=
      congrArg (fun c : ThreeAdicTensorCell r => threeAdicRowIndex c.2.2)
        hcell'.symm
    have henergy :
        root cq (threeAdicCycleRootSlot q) zeta ≠
          root cp (threeAdicCycleRootSlot p) zeta := by
      intro he
      apply hqp
      apply threeAdicCycleCell_energy_injective root hinj
      exact Prod.ext hcell he
    have hsame := chebyshevPhaseOrbit_range_disjoint_of_energy_ne
      (n := 3 ^ r)
      (i := threeAdicRowIndex cq.2.1)
      (j := threeAdicRowIndex cq.2.2)
      (h₁ := root cq (threeAdicCycleRootSlot q) zeta)
      (h₂ := root cp (threeAdicCycleRootSlot p) zeta)
      (pow_ne_zero _ (by decide)) hlambda
      (hpos cq (threeAdicCycleRootSlot q)).le
      (hpos cp (threeAdicCycleRootSlot p)).le
      ((hupper cq (threeAdicCycleRootSlot q)).le.trans
        Spikes.chebyshevCommonEnergyUpper_lt_half.le)
      ((hupper cp (threeAdicCycleRootSlot p)).le.trans
        Spikes.chebyshevCommonEnergyUpper_lt_half.le)
      henergy
    dsimp [cq, cp] at hsame
    simpa only [threeAdicUnperturbedCarrier, hrow₁, hrow₂] using hsame
  · have hdiff := chebyshevPhaseOrbit_range_disjoint_of_cell_ne
      (n := 3 ^ r)
      (i := threeAdicRowIndex cq.2.1)
      (j := threeAdicRowIndex cq.2.2)
      (k := threeAdicRowIndex cp.2.1)
      (l := threeAdicRowIndex cp.2.2)
      (h₁ := root cq (threeAdicCycleRootSlot q) zeta)
      (h₂ := root cp (threeAdicCycleRootSlot p) zeta)
      (pow_ne_zero _ (by decide))
      (threeAdicRowIndex_lt_pow cq.1.1.2 cq.2.1)
      (threeAdicRowIndex_lt_pow cq.1.2.2 cq.2.2)
      (threeAdicRowIndex_lt_pow cp.1.1.2 cp.2.1)
      (threeAdicRowIndex_lt_pow cp.1.2.2 cp.2.2)
      hlambda
      (hpos cq (threeAdicCycleRootSlot q))
      (hupper cq (threeAdicCycleRootSlot q))
      (hpos cp (threeAdicCycleRootSlot p))
      (hupper cp (threeAdicCycleRootSlot p))
      (by
        intro hrows
        exact hcell (threeAdicTensorCell_rowIndices_injective hrows))
    simpa [threeAdicUnperturbedCarrier, cq, cp] using hdiff

end Hilbert16
