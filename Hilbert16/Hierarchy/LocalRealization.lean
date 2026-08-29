import Hilbert16.Hierarchy.Realization

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace Hilbert16

/-!
# Local finite hierarchical realization

The analytic kernels used by the concrete Chebyshev construction are certified
only on a fixed neighborhood of the origin.  This file strengthens the
rank-to-roots selection by forcing all selected roots into an arbitrary
positive interval `(0, R)`, and correspondingly weakens the realization
theorem from global `C¹` regularity to `C¹` regularity on that interval.
-/

/-- A simple-root combination whose selected positive roots all lie below a
prescribed radius. -/
structure BoundedSimpleRootCombination (d : ℕ)
    (f : Fin (d + 1) → ℝ → ℝ) (R : ℝ)
    extends SimpleRootCombination d f where
  root_lt : ∀ s, root s < R

/-- Analytic rank supplies a fixed combination with all its simple positive
roots in any prescribed positive interval. -/
theorem exists_boundedSimpleRootCombination_of_rank (d : ℕ)
    (f : Fin (d + 1) → ℝ → ℝ)
    (p : Fin (d + 1) → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0)
    (hlin : LinearIndependent ℝ p) (R : ℝ) (hR : 0 < R) :
    Nonempty (BoundedSimpleRootCombination d f R) := by
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
  have hrootTendsto : ∀ s, Tendsto (fun tau => tau * root s tau) (𝓝 0) (𝓝 0) := by
    intro s
    have herror : Tendsto
        (fun tau => tau * root s tau - tau * rho s) (𝓝 0) (𝓝 0) :=
      (hlocation s).tendsto_zero_of_tendsto tendsto_id
    have hmain : Tendsto (fun tau : ℝ => tau * rho s) (𝓝 0) (𝓝 0) := by
      have hid : Tendsto (fun tau : ℝ => tau) (𝓝 0) (𝓝 0) := tendsto_id
      simpa using hid.mul_const (rho s)
    simpa only [sub_add_cancel, zero_add] using herror.add hmain
  have hbound : ∀ᶠ tau in 𝓝 0, ∀ s, tau * root s tau < R :=
    (Filter.eventually_all).2 fun s =>
      (hrootTendsto s).eventually (Iio_mem_nhds hR)
  have hchosen : ∀ᶠ tau in 𝓝[>] 0,
      Function.Injective (fun s => tau * root s tau) ∧
      ∀ s : Fin d,
        (∑ i, A tau i * f i (tau * root s tau)) = 0 ∧
        0 < tau * root s tau ∧ tau * root s tau < R ∧
        ∃ dtau : ℝ, dtau ≠ 0 ∧
          HasDerivAt (fun h => ∑ i, A tau i * f i h) dtau
            (tau * root s tau) := by
    filter_upwards [hevent, hbound.filter_mono inf_le_left] with tau htau hlt
    refine ⟨htau.1, ?_⟩
    intro s
    rcases htau.2 s with ⟨hz, hp, droot, hdroot, hderiv⟩
    exact ⟨hz, hp, hlt s, droot, hdroot, hderiv⟩
  rcases hchosen.exists with ⟨tau, hinj, htau⟩
  let droot : Fin d → ℝ := fun s => Classical.choose (htau s).2.2.2
  refine ⟨
    { coeff := A tau
      root := fun s => tau * root s tau
      deriv := droot
      root_pos := fun s => (htau s).2.1
      root_injective := hinj
      zero := fun s => (htau s).1
      deriv_ne := ?_
      hasDerivAt := ?_
      root_lt := fun s => (htau s).2.2.1 }⟩
  · intro s
    exact (Classical.choose_spec (htau s).2.2.2).1
  · intro s
    exact (Classical.choose_spec (htau s).2.2.2).2

/-- Finitely many analytic ranks can be selected layerwise while keeping all
chosen roots inside one prescribed positive interval. -/
theorem exists_layerwiseBoundedSimpleRootCombinations_of_rank
    {A : Type*} [Fintype A] (rootCount : A → ℕ)
    (f : ∀ alpha, Fin (rootCount alpha + 1) → ℝ → ℝ)
    (p : ∀ alpha, Fin (rootCount alpha + 1) →
      FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ alpha j, HasFPowerSeriesAt (f alpha j) (p alpha j) 0)
    (hlin : ∀ alpha, LinearIndependent ℝ (p alpha))
    (R : ℝ) (hR : 0 < R) :
    Nonempty (∀ alpha,
      BoundedSimpleRootCombination (rootCount alpha) (f alpha) R) := by
  classical
  exact ⟨fun alpha => Classical.choice
    (exists_boundedSimpleRootCombination_of_rank
      (rootCount alpha) (f alpha) (p alpha) (hp alpha) (hlin alpha) R hR)⟩

/-- **Local form of hierarchical realization.**  It is enough for each basis
response to be `C¹` on `(0, R)`: the rank-to-roots choice is made inside that
same interval before the finite hierarchical perturbation is applied. -/
theorem hierarchicalRealizationOn
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
    (R : ℝ) (hR : 0 < R)
    (hbasisC1 : ∀ c beta i,
      ContDiffOn ℝ 1 (basisResponse c beta i) (Set.Ioo 0 R))
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
          root c s zeta < R ∧
          ∃ dzeta : ℝ, dzeta ≠ 0 ∧
            HasDerivAt
              (hierarchicalWeightedResponse weight
                (fun c beta h => ∑ i, v beta i * basisResponse c beta i h) c zeta)
              dzeta (root c s zeta) := by
  classical
  let choice : ∀ alpha,
      BoundedSimpleRootCombination (rootCount alpha) (f alpha) R :=
    Classical.choice (exists_layerwiseBoundedSimpleRootCombinations_of_rank
      rootCount f p hp hlin R hR)
  let response : C → A → ℝ → ℝ :=
    selectedHierarchicalResponse rootCount f
      (fun alpha => (choice alpha).toSimpleRootCombination) basisResponse
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
    apply contDiffAt_const.mul
    exact (hbasisC1 c beta i).contDiffAt
      (IsOpen.mem_nhds isOpen_Ioo
        ⟨(choice (layer c)).root_pos s, (choice (layer c)).root_lt s⟩)
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
  have hupper : ∀ᶠ zeta in 𝓝 0, ∀ c, ∀ s : Fin (rootCount (layer c)),
      H.root c s zeta < R :=
    (Filter.eventually_all).2 fun c =>
      (Filter.eventually_all).2 fun s => by
        have ht := (H.contDiffAt_root c s).continuousAt
        change Tendsto (H.root c s) (𝓝 0) (𝓝 (H.root c s 0)) at ht
        rw [H.root_at] at ht
        exact ht.eventually (Iio_mem_nhds ((choice (layer c)).root_lt s))
  have hinjective := H.eventually_root_injective
    (fun alpha => (choice alpha).root_injective)
  filter_upwards [hinjective.filter_mono inf_le_left, hcommon,
    hupper.filter_mono inf_le_left] with zeta hinj hzeta hlt
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
  refine ⟨?_, hpos, hlt c s, d, hd, ?_⟩
  · rw [heq]
    exact hzero
  · apply hderiv.congr_of_eventuallyEq
    exact Eventually.of_forall (fun h => congrFun heq h)

end Hilbert16
