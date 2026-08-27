import Lean.Elab.Tactic.Omega

namespace Hilbert16

/-- Coordinatewise visibility for the two-dimensional layer indices. -/
def VisibleFrom (α β : Nat × Nat) : Prop := α.1 ≤ β.1 ∧ α.2 ≤ β.2

/-- The exponent used to separate the tensor blocks. -/
def hierarchyWeight (α : Nat × Nat) : Nat := α.1 + α.2

/-- Visibility can only increase the hierarchical exponent. -/
theorem visible_weight_mono {α β : Nat × Nat} (h : VisibleFrom α β) :
    hierarchyWeight α ≤ hierarchyWeight β := by
  rcases α with ⟨k, l⟩
  rcases β with ⟨p, q⟩
  simp only [VisibleFrom, hierarchyWeight] at h ⊢
  omega

/-- In a visible quadrant, the base layer is the unique layer of equal weight. -/
theorem visible_equal_weight_iff {α β : Nat × Nat} (h : VisibleFrom α β) :
    hierarchyWeight β = hierarchyWeight α ↔ β = α := by
  rcases α with ⟨k, l⟩
  rcases β with ⟨p, q⟩
  simp only [VisibleFrom, hierarchyWeight, Prod.mk.injEq] at h ⊢
  constructor
  · intro hw
    constructor <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every other visible block carries at least one extra power of `ζ`. -/
theorem visible_weight_gap {α β : Nat × Nat}
    (hvis : VisibleFrom α β) (hne : β ≠ α) :
    hierarchyWeight α + 1 ≤ hierarchyWeight β := by
  have hle := visible_weight_mono hvis
  have hweight : hierarchyWeight β ≠ hierarchyWeight α := by
    intro heq
    exact hne ((visible_equal_weight_iff hvis).mp heq)
  omega

end Hilbert16
