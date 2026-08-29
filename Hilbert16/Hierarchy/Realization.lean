import Hilbert16.Analytic.RankToRoots

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace Hilbert16

/-!
# Finite hierarchical realization of simple roots

This file formalizes the finite simultaneous-stability core of Paper Theorem
2.2.  A triangular family is normalized by the weight of its cell layer.  At
`ζ = 0` only the diagonal response remains; all strictly higher visible blocks
carry a positive power of `ζ`.  The scalar implicit-function theorem then
continues every diagonal simple root, and finiteness produces one common
positive parameter neighborhood for all layers, cells, and roots.
-/

/-- The single weighted response obtained by adding all chosen block vectors. -/
noncomputable def hierarchicalWeightedResponse
    {A C : Type*} [Fintype A] (weight : A → ℕ)
    (response : C → A → ℝ → ℝ) (c : C) (zeta h : ℝ) : ℝ :=
  ∑ beta, zeta ^ weight beta * response c beta h

/-- The response at a cell after division by the weight of its own layer.
Only visible blocks are retained; triangular visibility later identifies this
with the exact weighted response. -/
noncomputable def hierarchicalNormalizedResponse
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ) (c : C) (u : ℝ × ℝ) : ℝ :=
  ∑ beta, @ite ℝ (layer c ≤ beta) (Classical.propDecidable _)
    (u.1 ^ (weight beta - weight (layer c)) * response c beta u.2) 0

/-- The normalized response at `ζ=0` is exactly its diagonal block. -/
theorem hierarchicalNormalizedResponse_zero
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ)
    (hweight : ∀ {alpha beta : A}, alpha < beta → weight alpha < weight beta)
    (c : C) (h : ℝ) :
    hierarchicalNormalizedResponse layer weight response c (0, h) =
      response c (layer c) h := by
  classical
  unfold hierarchicalNormalizedResponse
  change (∑ beta, if layer c ≤ beta then
      0 ^ (weight beta - weight (layer c)) * response c beta h else 0) = _
  calc
    _ = if layer c ≤ layer c then
        0 ^ (weight (layer c) - weight (layer c)) * response c (layer c) h else 0 := by
      apply Finset.sum_eq_single (layer c)
      · intro beta _ hne
        by_cases hvis : layer c ≤ beta
        · have hlt : layer c < beta := lt_of_le_of_ne hvis hne.symm
          have hwt := hweight hlt
          have hexp : weight beta - weight (layer c) ≠ 0 := by
            omega
          simp [hvis, hexp]
        · simp [hvis]
      · simp
    _ = response c (layer c) h := by simp

/-- Under triangular visibility, multiplying the normalized response by the
cell-layer weight gives the exact single weighted response. -/
theorem hierarchyWeight_mul_normalized_eq_weighted
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ)
    (hvisible : ∀ c beta, ¬ layer c ≤ beta → response c beta = 0)
    (hweightMono : ∀ {alpha beta : A}, alpha ≤ beta → weight alpha ≤ weight beta)
    (c : C) (zeta h : ℝ) :
    zeta ^ weight (layer c) *
        hierarchicalNormalizedResponse layer weight response c (zeta, h) =
      hierarchicalWeightedResponse weight response c zeta h := by
  classical
  rw [hierarchicalNormalizedResponse, hierarchicalWeightedResponse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro beta _
  by_cases hvis : layer c ≤ beta
  · simp only [if_pos hvis]
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (hweightMono hvis)]
  · rw [if_neg hvis, mul_zero, hvisible c beta hvis]
    simp

/-- Joint `C¹` regularity of the finite normalized hierarchy at a diagonal
root follows termwise from `C¹` regularity of the one-variable responses. -/
theorem hierarchicalNormalizedResponse_contDiffAt
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ)
    (c : C) (rho : ℝ)
    (hresponse : ∀ beta, ContDiffAt ℝ 1 (response c beta) rho) :
    ContDiffAt ℝ 1 (hierarchicalNormalizedResponse layer weight response c) (0, rho) := by
  classical
  unfold hierarchicalNormalizedResponse
  apply ContDiffAt.sum
  intro beta _
  by_cases hvis : layer c ≤ beta
  · simp only [if_pos hvis]
    have hcomp : ContDiffAt ℝ 1 (fun u : ℝ × ℝ => response c beta u.2) (0, rho) := by
      apply (hresponse beta).comp (0, rho)
      fun_prop
    exact (contDiffAt_fst.pow (weight beta - weight (layer c))).mul hcomp
  · simp only [if_neg hvis]
    exact contDiffAt_const

/-- Root branches for all cells and all roots assigned to their layers. -/
structure HierarchicalSimpleRootFamily
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (rootCount : A → ℕ)
    (rho : ∀ alpha, Fin (rootCount alpha) → ℝ)
    (F : C → ℝ × ℝ → ℝ) where
  root : ∀ c, Fin (rootCount (layer c)) → ℝ → ℝ
  root_at : ∀ c s, root c s 0 = rho (layer c) s
  contDiffAt_root : ∀ c s, ContDiffAt ℝ 1 (root c s) 0
  eventually_zero : ∀ c s, ∀ᶠ zeta in 𝓝 0, F c (zeta, root c s zeta) = 0
  eventually_positive : ∀ c s, ∀ᶠ zeta in 𝓝 0, 0 < root c s zeta
  eventually_simple : ∀ c s, ∀ᶠ zeta in 𝓝 0, ∃ dzeta : ℝ, dzeta ≠ 0 ∧
    HasDerivAt (fun h : ℝ => F c (zeta, h)) dzeta (root c s zeta)

/-- Injective indexing of the diagonal roots persists simultaneously in
every finite cell. -/
theorem HierarchicalSimpleRootFamily.eventually_root_injective
    {A C : Type*} [Fintype A] [PartialOrder A] [Fintype C]
    {layer : C → A} {rootCount : A → ℕ}
    {rho : ∀ alpha, Fin (rootCount alpha) → ℝ}
    {F : C → ℝ × ℝ → ℝ}
    (H : HierarchicalSimpleRootFamily layer rootCount rho F)
    (hrho : ∀ alpha, Function.Injective (rho alpha)) :
    ∀ᶠ zeta in nhds (0 : ℝ), ∀ c,
      Function.Injective (fun s => H.root c s zeta) := by
  have hpairs : ∀ᶠ zeta in nhds (0 : ℝ), ∀ c s t, s ≠ t →
      H.root c s zeta ≠ H.root c t zeta := by
    rw [Filter.eventually_all]
    intro c
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro t
    by_cases hst : s = t
    · exact Eventually.of_forall fun _ hne => (hne hst).elim
    · have hs : Tendsto (H.root c s) (nhds (0 : ℝ))
          (nhds (rho (layer c) s)) := by
        have hs₀ := (H.contDiffAt_root c s).continuousAt
        change Tendsto (H.root c s) (nhds (0 : ℝ))
          (nhds (H.root c s 0)) at hs₀
        rw [H.root_at c s] at hs₀
        exact hs₀
      have ht : Tendsto (H.root c t) (nhds (0 : ℝ))
          (nhds (rho (layer c) t)) := by
        have ht₀ := (H.contDiffAt_root c t).continuousAt
        change Tendsto (H.root c t) (nhds (0 : ℝ))
          (nhds (H.root c t 0)) at ht₀
        rw [H.root_at c t] at ht₀
        exact ht₀
      have hlimit : rho (layer c) s - rho (layer c) t ≠ 0 := by
        rw [sub_ne_zero]
        exact fun heq => hst (hrho (layer c) heq)
      have hne : ∀ᶠ zeta in nhds (0 : ℝ),
          H.root c s zeta - H.root c t zeta ≠ 0 :=
        (hs.sub ht).eventually (eventually_ne_nhds hlimit)
      filter_upwards [hne] with zeta hneZeta
      exact fun _ heq => hneZeta (sub_eq_zero.mpr heq)
  filter_upwards [hpairs] with zeta hpairsZeta
  intro c s t heq
  by_contra hst
  exact hpairsZeta c s t hst heq

/-- Construct all normalized root branches from diagonal replicated simple
roots. -/
noncomputable def hierarchicalSimpleRootFamily_of_diagonal
    {A C : Type*} [Fintype A] [PartialOrder A]
    (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ)
    (hweight : ∀ {alpha beta : A}, alpha < beta → weight alpha < weight beta)
    (base : A → ℝ → ℝ) (gamma : C → ℝ)
    (hgamma : ∀ c, gamma c ≠ 0)
    (hdiag : ∀ c h, response c (layer c) h = gamma c * base (layer c) h)
    (rootCount : A → ℕ) (rho : ∀ alpha, Fin (rootCount alpha) → ℝ)
    (hrhoPos : ∀ alpha s, 0 < rho alpha s)
    (deriv : ∀ alpha, Fin (rootCount alpha) → ℝ)
    (hbaseZero : ∀ alpha s, base alpha (rho alpha s) = 0)
    (hbaseDeriv : ∀ alpha s,
      HasDerivAt (base alpha) (deriv alpha s) (rho alpha s))
    (hbaseDerivNe : ∀ alpha s, deriv alpha s ≠ 0)
    (hresponseC1 : ∀ c beta s,
      ContDiffAt ℝ 1 (response c beta) (rho (layer c) s)) :
    HierarchicalSimpleRootFamily layer rootCount rho
      (fun c => hierarchicalNormalizedResponse layer weight response c) := by
  let F : C → ℝ × ℝ → ℝ := fun c =>
    hierarchicalNormalizedResponse layer weight response c
  let Z : (c : C) → (s : Fin (rootCount (layer c))) →
      LocalZeroContinuation (F c) (0, rho (layer c) s) := fun c s => by
    have hF : ContDiffAt ℝ 1 (F c) (0, rho (layer c) s) :=
      hierarchicalNormalizedResponse_contDiffAt layer weight response c
        (rho (layer c) s) (fun beta => hresponseC1 c beta s)
    have hzero : F c (0, rho (layer c) s) = 0 := by
      change hierarchicalNormalizedResponse layer weight response c
        (0, rho (layer c) s) = 0
      rw [hierarchicalNormalizedResponse_zero layer weight response hweight]
      rw [hdiag, hbaseZero]
      simp
    have hslice : (fun h : ℝ => F c (0, h)) =
        fun h => gamma c * base (layer c) h := by
      funext h
      change hierarchicalNormalizedResponse layer weight response c (0, h) = _
      rw [hierarchicalNormalizedResponse_zero layer weight response hweight]
      exact hdiag c h
    have hd : HasDerivAt (fun h : ℝ => F c (0, h))
        (gamma c * deriv (layer c) s) (rho (layer c) s) := by
      rw [hslice]
      exact (hbaseDeriv (layer c) s).const_mul (gamma c)
    exact ContDiffAt.localZeroContinuation_of_hasDerivAt hF hzero hd
      (mul_ne_zero (hgamma c) (hbaseDerivNe (layer c) s))
  refine
    { root := fun c s => (Z c s).root
      root_at := fun c s => (Z c s).root_at
      contDiffAt_root := fun c s => (Z c s).contDiffAt_root
      eventually_zero := fun c s => (Z c s).eventually_zero
      eventually_positive := ?_
      eventually_simple := ?_ }
  · intro c s
    have ht := (Z c s).contDiffAt_root.continuousAt
    change Tendsto (Z c s).root (𝓝 0) (𝓝 ((Z c s).root 0)) at ht
    rw [(Z c s).root_at] at ht
    exact ht.eventually (Ioi_mem_nhds (hrhoPos (layer c) s))
  · intro c s
    have hF : ContDiffAt ℝ 1 (F c) (0, rho (layer c) s) :=
      hierarchicalNormalizedResponse_contDiffAt layer weight response c
        (rho (layer c) s) (fun beta => hresponseC1 c beta s)
    have hslice : (fun h : ℝ => F c (0, h)) =
        fun h => gamma c * base (layer c) h := by
      funext h
      change hierarchicalNormalizedResponse layer weight response c (0, h) = _
      rw [hierarchicalNormalizedResponse_zero layer weight response hweight]
      exact hdiag c h
    have hd : HasDerivAt (fun h : ℝ => F c (0, h))
        (gamma c * deriv (layer c) s) (rho (layer c) s) := by
      rw [hslice]
      exact (hbaseDeriv (layer c) s).const_mul (gamma c)
    exact (Z c s).eventually_hasDerivAt_slice_ne_zero hF hd
      (mul_ne_zero (hgamma c) (hbaseDerivNe (layer c) s))

/-- One sufficiently small positive `ζ` works simultaneously for every cell
and every root, and the roots are simple zeros of the exact weighted response,
not only of its normalization. -/
theorem HierarchicalSimpleRootFamily.eventually_weighted_positive_simpleZeros
    {A C : Type*} [Fintype A] [DecidableEq A] [PartialOrder A]
    [Fintype C] (layer : C → A) (weight : A → ℕ)
    (response : C → A → ℝ → ℝ)
    (rootCount : A → ℕ) (rho : ∀ alpha, Fin (rootCount alpha) → ℝ)
    (H : HierarchicalSimpleRootFamily layer rootCount rho
      (fun c => hierarchicalNormalizedResponse layer weight response c))
    (hvisible : ∀ c beta, ¬ layer c ≤ beta → response c beta = 0)
    (hweightMono : ∀ {alpha beta : A}, alpha ≤ beta → weight alpha ≤ weight beta) :
    ∀ᶠ zeta in 𝓝[>] 0, ∀ c, ∀ s : Fin (rootCount (layer c)),
      hierarchicalWeightedResponse weight response c zeta (H.root c s zeta) = 0 ∧
      0 < H.root c s zeta ∧
      ∃ dzeta : ℝ, dzeta ≠ 0 ∧
        HasDerivAt (hierarchicalWeightedResponse weight response c zeta) dzeta
          (H.root c s zeta) := by
  have hzero : ∀ᶠ zeta in 𝓝 0, ∀ c, ∀ s : Fin (rootCount (layer c)),
      hierarchicalNormalizedResponse layer weight response c (zeta, H.root c s zeta) = 0 :=
    (Filter.eventually_all).2 (fun c =>
      (Filter.eventually_all).2 (fun s => H.eventually_zero c s))
  have hpos : ∀ᶠ zeta in 𝓝 0, ∀ c, ∀ s : Fin (rootCount (layer c)),
      0 < H.root c s zeta :=
    (Filter.eventually_all).2 (fun c =>
      (Filter.eventually_all).2 (fun s => H.eventually_positive c s))
  have hsimple : ∀ᶠ zeta in 𝓝 0, ∀ c, ∀ s : Fin (rootCount (layer c)),
      ∃ dzeta : ℝ, dzeta ≠ 0 ∧
        HasDerivAt (fun h : ℝ => hierarchicalNormalizedResponse layer weight response c (zeta, h))
          dzeta (H.root c s zeta) :=
    (Filter.eventually_all).2 (fun c =>
      (Filter.eventually_all).2 (fun s => H.eventually_simple c s))
  filter_upwards [hzero.filter_mono inf_le_left, hpos.filter_mono inf_le_left,
    hsimple.filter_mono inf_le_left, self_mem_nhdsWithin] with zeta hz hp hs hzeta
  intro c s
  rcases hs c s with ⟨d, hd, hderiv⟩
  have heq : (fun h : ℝ => hierarchicalWeightedResponse weight response c zeta h) =
      fun h => zeta ^ weight (layer c) *
        hierarchicalNormalizedResponse layer weight response c (zeta, h) := by
    funext h
    exact (hierarchyWeight_mul_normalized_eq_weighted
      layer weight response hvisible hweightMono c zeta h).symm
  have hderivWeighted : HasDerivAt
      (hierarchicalWeightedResponse weight response c zeta)
      (zeta ^ weight (layer c) * d) (H.root c s zeta) := by
    change HasDerivAt
      (fun h : ℝ => hierarchicalWeightedResponse weight response c zeta h)
      (zeta ^ weight (layer c) * d) (H.root c s zeta)
    rw [heq]
    exact hderiv.const_mul (zeta ^ weight (layer c))
  refine ⟨?_, hp c s, zeta ^ weight (layer c) * d, ?_, hderivWeighted⟩
  · rw [← hierarchyWeight_mul_normalized_eq_weighted
      layer weight response hvisible hweightMono]
    simp [hz c s]
  · exact mul_ne_zero (pow_ne_zero _ hzeta.ne') hd

/-!
## Selecting the diagonal block vectors from analytic rank
-/

/-- One fixed member of an analytic family together with all of its selected
positive simple roots. -/
structure SimpleRootCombination (d : ℕ) (f : Fin (d + 1) → ℝ → ℝ) where
  coeff : Fin (d + 1) → ℝ
  root : Fin d → ℝ
  deriv : Fin d → ℝ
  root_pos : ∀ s, 0 < root s
  root_injective : Function.Injective root
  zero : ∀ s, (∑ i, coeff i * f i (root s)) = 0
  deriv_ne : ∀ s, deriv s ≠ 0
  hasDerivAt : ∀ s,
    HasDerivAt (fun h => ∑ i, coeff i * f i h) (deriv s) (root s)

/-- Paper Lemma 2.1 supplies one fixed block combination after choosing one
sufficiently small positive concentration parameter. -/
theorem exists_simpleRootCombination_of_rank (d : ℕ)
    (f : Fin (d + 1) → ℝ → ℝ)
    (p : Fin (d + 1) → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0)
    (hlin : LinearIndependent ℝ p) :
    Nonempty (SimpleRootCombination d f) := by
  let rho : Fin d → ℝ := fun s => (s : ℝ) + 1
  have hrho : Function.Injective rho := by
    intro s t h
    simp only [rho, add_left_inj] at h
    exact Fin.ext (Nat.cast_injective h)
  have hrhoPos : ∀ s, 0 < rho s := by
    intro s
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  rcases rankToSimplePositiveRoots d f p hp hlin rho hrho hrhoPos with
    ⟨A, root, hroot0, hlocation, hevent⟩
  rcases hevent.exists with ⟨tau, hinj, htau⟩
  let droot : Fin d → ℝ := fun s => Classical.choose (htau s).2.2
  refine ⟨
    { coeff := A tau
      root := fun s => tau * root s tau
      deriv := droot
      root_pos := fun s => (htau s).2.1
      root_injective := hinj
      zero := fun s => (htau s).1
      deriv_ne := ?_
      hasDerivAt := ?_ }⟩
  · intro s
    exact (Classical.choose_spec (htau s).2.2).1
  · intro s
    exact (Classical.choose_spec (htau s).2.2).2

/-- Finitely many analytic ranks can be converted simultaneously into one
fixed simple-root combination per layer. -/
theorem exists_layerwiseSimpleRootCombinations_of_rank
    {A : Type*} [Fintype A] (rootCount : A → ℕ)
    (f : ∀ alpha, Fin (rootCount alpha + 1) → ℝ → ℝ)
    (p : ∀ alpha, Fin (rootCount alpha + 1) →
      FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ alpha j, HasFPowerSeriesAt (f alpha j) (p alpha j) 0)
    (hlin : ∀ alpha, LinearIndependent ℝ (p alpha)) :
    Nonempty (∀ alpha, SimpleRootCombination (rootCount alpha) (f alpha)) := by
  classical
  exact ⟨fun alpha => Classical.choice
    (exists_simpleRootCombination_of_rank (rootCount alpha) (f alpha) (p alpha)
      (hp alpha) (hlin alpha))⟩

/-- Response after inserting the one fixed coefficient vector selected in each
layer by rank-to-roots. -/
noncomputable def selectedHierarchicalResponse
    {A C : Type*} (rootCount : A → ℕ)
    (f : ∀ alpha, Fin (rootCount alpha + 1) → ℝ → ℝ)
    (choice : ∀ alpha, SimpleRootCombination (rootCount alpha) (f alpha))
    (basisResponse : C → ∀ beta, Fin (rootCount beta + 1) → ℝ → ℝ)
    (c : C) (beta : A) (h : ℝ) : ℝ :=
  ∑ i, (choice beta).coeff i * basisResponse c beta i h

/-- **Paper Theorem 2.2 (hierarchical realization), finite analytic-family
form.**  One coefficient vector is first selected in every diagonal block by
rank-to-roots.  For all sufficiently small positive `ζ`, the single weighted
sum of those vectors has every selected positive simple root simultaneously in
every cell. -/
theorem hierarchicalRealization
    {A C : Type*} [Fintype A] [DecidableEq A] [PartialOrder A] [Fintype C]
    (layer : C → A) (weight : A → ℕ)
    (hweight : ∀ {alpha beta : A}, alpha < beta → weight alpha < weight beta)
    (rootCount : A → ℕ)
    (f : ∀ alpha, Fin (rootCount alpha + 1) → ℝ → ℝ)
    (p : ∀ alpha, Fin (rootCount alpha + 1) →
      FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ alpha j, HasFPowerSeriesAt (f alpha j) (p alpha j) 0)
    (hlin : ∀ alpha, LinearIndependent ℝ (p alpha))
    (basisResponse : C → ∀ beta, Fin (rootCount beta + 1) → ℝ → ℝ)
    (hbasisC1 : ∀ c beta i, ContDiff ℝ 1 (basisResponse c beta i))
    (hvisible : ∀ c beta i, ¬ layer c ≤ beta → basisResponse c beta i = 0)
    (gamma : C → ℝ) (hgamma : ∀ c, gamma c ≠ 0)
    (hdiag : ∀ c (v : Fin (rootCount (layer c) + 1) → ℝ) h,
      ∑ i, v i * basisResponse c (layer c) i h =
        gamma c * ∑ i, v i * f (layer c) i h) :
    ∃ (v : ∀ alpha, Fin (rootCount alpha + 1) → ℝ)
      (root : ∀ c, Fin (rootCount (layer c)) → ℝ → ℝ),
      ∀ᶠ zeta in 𝓝[>] 0,
        (∀ c, Function.Injective (fun s => root c s zeta)) ∧
        ∀ c, ∀ s : Fin (rootCount (layer c)),
          hierarchicalWeightedResponse weight
            (fun c beta h => ∑ i, v beta i * basisResponse c beta i h)
            c zeta (root c s zeta) = 0 ∧
          0 < root c s zeta ∧
          ∃ dzeta : ℝ, dzeta ≠ 0 ∧
            HasDerivAt
              (hierarchicalWeightedResponse weight
                (fun c beta h => ∑ i, v beta i * basisResponse c beta i h) c zeta)
              dzeta (root c s zeta) := by
  classical
  let choice : ∀ alpha, SimpleRootCombination (rootCount alpha) (f alpha) :=
    Classical.choice (exists_layerwiseSimpleRootCombinations_of_rank
      rootCount f p hp hlin)
  let response : C → A → ℝ → ℝ :=
    selectedHierarchicalResponse rootCount f choice basisResponse
  have hresponseEq : response =
      fun c beta h => ∑ i, (choice beta).coeff i * basisResponse c beta i h := by
    rfl
  let base : A → ℝ → ℝ := fun alpha h =>
    ∑ i, (choice alpha).coeff i * f alpha i h
  have hresponseC1 : ∀ c beta s,
      ContDiffAt ℝ 1 (response c beta) ((choice (layer c)).root s) := by
    intro c beta s
    unfold response selectedHierarchicalResponse
    apply ContDiffAt.sum
    intro i _
    exact contDiffAt_const.mul (hbasisC1 c beta i).contDiffAt
  have hdiagSelected : ∀ c h,
      response c (layer c) h = gamma c * base (layer c) h := by
    intro c h
    exact hdiag c (choice (layer c)).coeff h
  have hvisibleSelected : ∀ c beta, ¬ layer c ≤ beta →
      response c beta = 0 := by
    intro c beta hvis
    funext h
    unfold response selectedHierarchicalResponse
    apply Finset.sum_eq_zero
    intro i _
    rw [hvisible c beta i hvis]
    simp
  have hweightMono : ∀ {alpha beta : A}, alpha ≤ beta →
      weight alpha ≤ weight beta := by
    intro alpha beta hab
    rcases hab.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hweight hlt).le
  let H := hierarchicalSimpleRootFamily_of_diagonal
    layer weight response hweight base gamma hgamma hdiagSelected rootCount
    (fun alpha => (choice alpha).root)
    (fun alpha s => (choice alpha).root_pos s)
    (fun alpha => (choice alpha).deriv)
    (fun alpha s => (choice alpha).zero s)
    (fun alpha s => (choice alpha).hasDerivAt s)
    (fun alpha s => (choice alpha).deriv_ne s)
    hresponseC1
  refine ⟨(fun alpha => (choice alpha).coeff), H.root, ?_⟩
  have hcommon := H.eventually_weighted_positive_simpleZeros
    layer weight response rootCount (fun alpha => (choice alpha).root)
    hvisibleSelected hweightMono
  have hinjective := H.eventually_root_injective
    (fun alpha => (choice alpha).root_injective)
  filter_upwards [hinjective.filter_mono inf_le_left, hcommon]
    with zeta hinj hzeta
  refine ⟨hinj, ?_⟩
  intro c s
  rcases hzeta c s with ⟨hzero, hpos, d, hd, hderiv⟩
  let selected : C → A → ℝ → ℝ :=
    fun c beta h => ∑ i, (choice beta).coeff i * basisResponse c beta i h
  have hselected : selected = response := by
    exact hresponseEq.symm
  have heq : hierarchicalWeightedResponse weight selected c zeta =
      hierarchicalWeightedResponse weight response c zeta := by
    rw [hselected]
  refine ⟨?_, hpos, d, hd, ?_⟩
  · rw [heq]
    exact hzero
  · apply hderiv.congr_of_eventuallyEq
    exact Eventually.of_forall (fun h => congrFun heq h)

end Hilbert16
