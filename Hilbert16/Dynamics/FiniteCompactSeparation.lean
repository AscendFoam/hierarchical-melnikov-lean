import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

namespace Hilbert16

open Set

/-!
# Simultaneous separation of a finite compact family
-/

/-- A finite pairwise-disjoint family of compact sets in a normal Hausdorff
space admits pairwise-disjoint open supersets. -/
theorem exists_pairwiseDisjoint_open_supersets
    {alpha X : Type*} [Fintype alpha] [TopologicalSpace X]
    [T2Space X] [NormalSpace X]
    (K : alpha → Set X) (hcompact : ∀ a, IsCompact (K a))
    (hpair : Pairwise (fun a b => Disjoint (K a) (K b))) :
    ∃ U : alpha → Set X,
      (∀ a, IsOpen (U a) ∧ K a ⊆ U a) ∧
      Pairwise (fun a b => Disjoint (U a) (U b)) := by
  classical
  have hsep : ∀ a b, ∃ A B : Set X,
      IsOpen A ∧ IsOpen B ∧ K a ⊆ A ∧ K b ⊆ B ∧
        (a ≠ b → Disjoint A B) := by
    intro a b
    by_cases hab : a = b
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ,
        Set.subset_univ _, Set.subset_univ _, fun hne => (hne hab).elim⟩
    · rcases normal_separation (hcompact a).isClosed (hcompact b).isClosed
        (hpair hab) with ⟨A, B, hAopen, hBopen, hKA, hKB, hAB⟩
      exact ⟨A, B, hAopen, hBopen, hKA, hKB, fun _ => hAB⟩
  choose A B hAopen hBopen hKA hKB hAB using hsep
  let U : alpha → Set X := fun a => ⋂ b, A a b ∩ B b a
  refine ⟨U, ?_, ?_⟩
  · intro a
    constructor
    · exact isOpen_iInter_of_finite fun b => (hAopen a b).inter (hBopen b a)
    · intro x hx
      change x ∈ ⋂ b, A a b ∩ B b a
      exact Set.mem_iInter.2 fun b => ⟨hKA a b hx, hKB b a hx⟩
  · intro a b hab
    apply (hAB a b hab).mono
    · intro x hx
      change x ∈ ⋂ c, A a c ∩ B c a at hx
      exact (Set.mem_iInter.mp hx b).1
    · intro x hx
      change x ∈ ⋂ c, A b c ∩ B c b at hx
      exact (Set.mem_iInter.mp hx a).2

end Hilbert16
