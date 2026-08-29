import Hilbert16.Hierarchy.LocalRealization
import Hilbert16.Degree.ThreeAdicDensity
import Hilbert16.Spikes.ChebyshevMelnikov

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter
open scoped BigOperators Topology

namespace Hilbert16

/-!
# Concrete three-adic hierarchical realization

This module instantiates the finite local hierarchy with the actual row and
frequency types of the three-adic Chebyshev construction.
-/

/-- A tensor layer is a pair of one-dimensional three-adic bands. -/
abbrev ThreeAdicTensorLayer (r : ℕ) := Fin r × Fin r

/-- A marked tensor cell carries one row from each band of its layer. -/
def ThreeAdicTensorCell (r : ℕ) :=
  Σ kl : ThreeAdicTensorLayer r,
    ThreeAdicRow r kl.1 × ThreeAdicRow r kl.2

instance (r : ℕ) : Fintype (ThreeAdicTensorCell r) := by
  unfold ThreeAdicTensorCell
  infer_instance

/-- The number of simple roots assigned to one tensor block. -/
def threeAdicBlockRootCount {r : ℕ} (kl : ThreeAdicTensorLayer r) : ℕ :=
  Fintype.card (ThreeAdicFrequency kl.1) *
    Fintype.card (ThreeAdicFrequency kl.2) - 1

theorem threeAdicBlockFrequencyProduct_pos {r : ℕ} (kl : ThreeAdicTensorLayer r) :
    1 ≤ Fintype.card (ThreeAdicFrequency kl.1) *
      Fintype.card (ThreeAdicFrequency kl.2) := by
  rw [card_threeAdicFrequency, card_threeAdicFrequency]
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))

/-- Enumerate a block's full Cartesian frequency family by the `d+1`
indices expected by rank-to-roots. -/
noncomputable def threeAdicBlockIndexEquiv {r : ℕ} (kl : ThreeAdicTensorLayer r) :
    Fin (threeAdicBlockRootCount kl + 1) ≃
      Fin (Fintype.card (ThreeAdicFrequency kl.1)) ×
        Fin (Fintype.card (ThreeAdicFrequency kl.2)) :=
  (finCongr (Nat.sub_add_cancel (threeAdicBlockFrequencyProduct_pos kl))).trans
    finProdFinEquiv.symm

/-- Convert one finite block index into its pair of genuine frequency
parameters. -/
noncomputable def threeAdicBlockFrequency
    {r : ℕ}
    (kl : ThreeAdicTensorLayer r) (a : Fin (threeAdicBlockRootCount kl + 1)) :
    ThreeAdicFrequency kl.1 × ThreeAdicFrequency kl.2 :=
  ((Fintype.equivFin (ThreeAdicFrequency kl.1)).symm
      (threeAdicBlockIndexEquiv kl a).1,
    (Fintype.equivFin (ThreeAdicFrequency kl.2)).symm
      (threeAdicBlockIndexEquiv kl a).2)

/-- The preceding conversion as an equivalence. -/
noncomputable def threeAdicBlockFrequencyEquiv {r : ℕ}
    (kl : ThreeAdicTensorLayer r) :
    Fin (threeAdicBlockRootCount kl + 1) ≃
      ThreeAdicFrequency kl.1 × ThreeAdicFrequency kl.2 :=
  (threeAdicBlockIndexEquiv kl).trans
    (Equiv.prodCongr
      (Fintype.equivFin (ThreeAdicFrequency kl.1)).symm
      (Fintype.equivFin (ThreeAdicFrequency kl.2)).symm)

@[simp]
theorem threeAdicBlockFrequencyEquiv_apply {r : ℕ}
    (kl : ThreeAdicTensorLayer r) (a) :
    threeAdicBlockFrequencyEquiv kl a = threeAdicBlockFrequency kl a := rfl

/-- Reassociate a tensor layer and its genuine frequency pair into the public
`ThreeAdicMode` index. -/
def threeAdicLayerFrequencyModeEquiv (r : ℕ) :
    (Σ kl : ThreeAdicTensorLayer r,
      ThreeAdicFrequency kl.1 × ThreeAdicFrequency kl.2) ≃ ThreeAdicMode r where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun m := ⟨(m.1, m.2.1), m.2.2⟩
  left_inv x := by cases x with | mk kl ab => cases kl; rfl
  right_inv m := by rcases m with ⟨k, l, ab⟩; rfl

/-- The exact equivalence between the blockwise `d+1` indices and all public
three-adic modes. -/
noncomputable def threeAdicBlockModeEquiv (r : ℕ) :
    (Σ kl : ThreeAdicTensorLayer r, Fin (threeAdicBlockRootCount kl + 1)) ≃
      ThreeAdicMode r :=
  (Equiv.sigmaCongrRight fun kl => threeAdicBlockFrequencyEquiv kl).trans
    (threeAdicLayerFrequencyModeEquiv r)

@[simp]
theorem threeAdicBlockModeEquiv_apply_layer {r : ℕ}
    (x : Σ kl : ThreeAdicTensorLayer r, Fin (threeAdicBlockRootCount kl + 1)) :
    (threeAdicBlockModeEquiv r x).1 = x.1.1 := rfl

@[simp]
theorem threeAdicBlockModeEquiv_apply_secondLayer {r : ℕ}
    (x : Σ kl : ThreeAdicTensorLayer r, Fin (threeAdicBlockRootCount kl + 1)) :
    (threeAdicBlockModeEquiv r x).2.1 = x.1.2 := rfl

@[simp]
theorem threeAdicBlockModeEquiv_apply_frequencies {r : ℕ}
    (x : Σ kl : ThreeAdicTensorLayer r, Fin (threeAdicBlockRootCount kl + 1)) :
    (threeAdicBlockModeEquiv r x).2.2 = threeAdicBlockFrequency x.1 x.2 := rfl

/-- The normalized first frequency coordinate of a tensor block. -/
noncomputable def threeAdicBlockAlpha (r : ℕ) (kl : ThreeAdicTensorLayer r)
    (a : Fin (Fintype.card (ThreeAdicFrequency kl.1))) : ℝ :=
  (threeAdicFrequencyValue (r := r)
      ((Fintype.equivFin (ThreeAdicFrequency kl.1)).symm a) : ℝ) / (3 ^ r : ℝ)

/-- The normalized second frequency coordinate of a tensor block. -/
noncomputable def threeAdicBlockBeta (r : ℕ) (kl : ThreeAdicTensorLayer r)
    (b : Fin (Fintype.card (ThreeAdicFrequency kl.2))) : ℝ :=
  (threeAdicFrequencyValue (r := r)
      ((Fintype.equivFin (ThreeAdicFrequency kl.2)).symm b) : ℝ) / (3 ^ r : ℝ)

theorem threeAdicBlockAlpha_pos {r : ℕ} (kl : ThreeAdicTensorLayer r) (a) :
    0 < threeAdicBlockAlpha r kl a := by
  unfold threeAdicBlockAlpha
  apply div_pos
  · exact_mod_cast Nat.mul_pos (threeAdicFrequencyNumerator_pos _)
      (pow_pos (by decide) _)
  · positivity

theorem threeAdicBlockBeta_pos {r : ℕ} (kl : ThreeAdicTensorLayer r) (b) :
    0 < threeAdicBlockBeta r kl b := by
  unfold threeAdicBlockBeta
  apply div_pos
  · exact_mod_cast Nat.mul_pos (threeAdicFrequencyNumerator_pos _)
      (pow_pos (by decide) _)
  · positivity

theorem threeAdicBlockAlpha_lt_one {r : ℕ} (kl : ThreeAdicTensorLayer r) (a) :
    threeAdicBlockAlpha r kl a < 1 := by
  unfold threeAdicBlockAlpha
  rw [div_lt_one (by positivity : (0 : ℝ) < 3 ^ r)]
  exact_mod_cast threeAdicFrequencyValue_lt_pow kl.1.2
    ((Fintype.equivFin (ThreeAdicFrequency kl.1)).symm a)

theorem threeAdicBlockBeta_lt_one {r : ℕ} (kl : ThreeAdicTensorLayer r) (b) :
    threeAdicBlockBeta r kl b < 1 := by
  unfold threeAdicBlockBeta
  rw [div_lt_one (by positivity : (0 : ℝ) < 3 ^ r)]
  exact_mod_cast threeAdicFrequencyValue_lt_pow kl.2.2
    ((Fintype.equivFin (ThreeAdicFrequency kl.2)).symm b)

theorem threeAdicBlockAlpha_injective {r : ℕ} (kl : ThreeAdicTensorLayer r) :
    Function.Injective (threeAdicBlockAlpha r kl) := by
  intro a b hab
  apply (Fintype.equivFin (ThreeAdicFrequency kl.1)).symm.injective
  apply threeAdicFrequencyValue_injective
  have hcast :
      (threeAdicFrequencyValue (r := r)
          ((Fintype.equivFin (ThreeAdicFrequency kl.1)).symm a) : ℝ) =
        threeAdicFrequencyValue (r := r)
          ((Fintype.equivFin (ThreeAdicFrequency kl.1)).symm b) := by
    exact (div_left_inj' (by positivity : (3 ^ r : ℝ) ≠ 0)).mp hab
  exact_mod_cast hcast

theorem threeAdicBlockBeta_injective {r : ℕ} (kl : ThreeAdicTensorLayer r) :
    Function.Injective (threeAdicBlockBeta r kl) := by
  intro a b hab
  apply (Fintype.equivFin (ThreeAdicFrequency kl.2)).symm.injective
  apply threeAdicFrequencyValue_injective
  have hcast :
      (threeAdicFrequencyValue (r := r)
          ((Fintype.equivFin (ThreeAdicFrequency kl.2)).symm a) : ℝ) =
        threeAdicFrequencyValue (r := r)
          ((Fintype.equivFin (ThreeAdicFrequency kl.2)).symm b) := by
    exact (div_left_inj' (by positivity : (3 ^ r : ℝ) ≠ 0)).mp hab
  exact_mod_cast hcast

/-- One-based tensor weight from Paper Eq. (6.6). -/
def threeAdicTensorWeight {r : ℕ} (kl : ThreeAdicTensorLayer r) : ℕ :=
  kl.1.1 + 1 + (kl.2.1 + 1)

theorem threeAdicTensorWeight_strictMono
    {r : ℕ}
    {alpha beta : ThreeAdicTensorLayer r} (h : alpha < beta) :
    threeAdicTensorWeight alpha < threeAdicTensorWeight beta := by
  rcases h with ⟨hle, hne⟩
  have hfst : alpha.1.1 ≤ beta.1.1 := hle.1
  have hsnd : alpha.2.1 ≤ beta.2.1 := hle.2
  have hone : alpha.1.1 < beta.1.1 ∨ alpha.2.1 < beta.2.1 := by
    by_contra hn
    push Not at hn
    apply hne
    exact ⟨hn.1, hn.2⟩
  unfold threeAdicTensorWeight
  omega

/-- The nonzero frequency character multiplying the analytic kernel in one
diagonal block. -/
noncomputable def threeAdicBlockFrequencyCharacter
    {r : ℕ}
    (kl : ThreeAdicTensorLayer r) (a : Fin (threeAdicBlockRootCount kl + 1)) : ℝ :=
  modTwelveCharacter (threeAdicFrequencyNumerator (threeAdicBlockFrequency kl a).1) *
    modTwelveCharacter (threeAdicFrequencyNumerator (threeAdicBlockFrequency kl a).2)

theorem threeAdicBlockFrequencyCharacter_ne_zero
    {r : ℕ}
    (kl : ThreeAdicTensorLayer r) (a) :
    threeAdicBlockFrequencyCharacter kl a ≠ 0 := by
  unfold threeAdicBlockFrequencyCharacter
  exact mul_ne_zero (modTwelveCharacter_ne_zero _) (modTwelveCharacter_ne_zero _)

/-- The diagonal analytic family, including its nonzero frequency sign. -/
noncomputable def threeAdicDiagonalKernel (r : ℕ) (lambda : ℝ)
    (kl : ThreeAdicTensorLayer r) (a : Fin (threeAdicBlockRootCount kl + 1))
    (h : ℝ) : ℝ :=
  (threeAdicBlockFrequencyCharacter kl a •
    analyticKernel
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).1 : ℝ) /
        (3 ^ r : ℝ))
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).2 : ℝ) /
        (3 ^ r : ℝ)) lambda) h

/-- Formal series of the signed diagonal kernel. -/
noncomputable def threeAdicDiagonalKernelSeries (r : ℕ) (lambda : ℝ)
    (kl : ThreeAdicTensorLayer r) (a : Fin (threeAdicBlockRootCount kl + 1)) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  threeAdicBlockFrequencyCharacter kl a •
    analyticKernelSeries
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).1 : ℝ) /
        (3 ^ r : ℝ))
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).2 : ℝ) /
        (3 ^ r : ℝ)) lambda

/-- Coefficientwise linear independence lifts to formal power series. -/
theorem linearIndependent_formalMultilinearSeries_of_coeff
    {ι : Type*} [Fintype ι]
    (p : ι → FormalMultilinearSeries ℝ ℝ ℝ)
    (hcoeff : LinearIndependent ℝ (fun i => fun m => (p i).coeff m)) :
    LinearIndependent ℝ p := by
  classical
  rw [Fintype.linearIndependent_iff] at hcoeff ⊢
  intro c hzero
  apply hcoeff c
  funext m
  have hm := congrArg
    (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q.coeff m) hzero
  rw [show (∑ i, c i • p i) =
      ∑ i ∈ (Finset.univ : Finset ι), c i • p i by simp,
    coeff_finset_sum_smul] at hm
  have hz : (0 : FormalMultilinearSeries ℝ ℝ ℝ).coeff m = 0 := rfl
  rw [hz] at hm
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hm

/-- One common anisotropy threshold gives full formal-series rank in every
actual three-adic tensor block, including the diagonal frequency signs. -/
theorem finiteThreeAdicCommonDiagonalKernelSeriesRank (r : ℕ) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda, ∀ kl : ThreeAdicTensorLayer r,
      LinearIndependent ℝ (threeAdicDiagonalKernelSeries r lambda kl) := by
  let d : ThreeAdicTensorLayer r → ℕ := fun kl =>
    Fintype.card (ThreeAdicFrequency kl.1)
  let e : ThreeAdicTensorLayer r → ℕ := fun kl =>
    Fintype.card (ThreeAdicFrequency kl.2)
  let alpha : ∀ kl, Fin (d kl) → ℝ := fun kl => threeAdicBlockAlpha r kl
  let beta : ∀ kl, Fin (e kl) → ℝ := fun kl => threeAdicBlockBeta r kl
  rcases finiteBlockCommonAnisotropicTaylorRank d e alpha beta
    (fun kl => threeAdicBlockAlpha_pos kl)
    (fun kl => threeAdicBlockAlpha_lt_one kl)
    (fun kl => threeAdicBlockAlpha_injective kl)
    (fun kl => threeAdicBlockBeta_pos kl)
    (fun kl => threeAdicBlockBeta_lt_one kl)
    (fun kl => threeAdicBlockBeta_injective kl) with
    ⟨Lambda, hLambda, hRank⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda kl
  have hcoeffPair := hRank lambda hlambda kl
  have hcoeff : LinearIndependent ℝ
      (fun a : Fin (threeAdicBlockRootCount kl + 1) => fun m : ℕ =>
        analyticKernelTaylorCoefficient
          ((threeAdicFrequencyValue (r := r)
              (threeAdicBlockFrequency kl a).1 : ℝ) / (3 ^ r : ℝ))
          ((threeAdicFrequencyValue (r := r)
              (threeAdicBlockFrequency kl a).2 : ℝ) / (3 ^ r : ℝ))
          lambda m) := by
    have hreindex := hcoeffPair.comp (threeAdicBlockIndexEquiv kl)
      (threeAdicBlockIndexEquiv kl).injective
    convert hreindex using 1
    funext a m
    rfl
  let p : Fin (threeAdicBlockRootCount kl + 1) →
      FormalMultilinearSeries ℝ ℝ ℝ := fun a =>
    analyticKernelSeries
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).1 : ℝ) /
        (3 ^ r : ℝ))
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).2 : ℝ) /
        (3 ^ r : ℝ)) lambda
  have hp : LinearIndependent ℝ p := by
    apply linearIndependent_formalMultilinearSeries_of_coeff
    simpa only [p, analyticKernelSeries_coeff] using hcoeff
  let unitScale : Fin (threeAdicBlockRootCount kl + 1) → ℝˣ := fun a =>
    Units.mk0 (threeAdicBlockFrequencyCharacter kl a)
      (threeAdicBlockFrequencyCharacter_ne_zero kl a)
  have hscaled := hp.units_smul unitScale
  have hfamily : unitScale • p = threeAdicDiagonalKernelSeries r lambda kl := by
    funext a
    change (threeAdicBlockFrequencyCharacter kl a : ℝ) •
        analyticKernelSeries
          ((threeAdicFrequencyValue (r := r)
              (threeAdicBlockFrequency kl a).1 : ℝ) / (3 ^ r : ℝ))
          ((threeAdicFrequencyValue (r := r)
              (threeAdicBlockFrequency kl a).2 : ℝ) / (3 ^ r : ℝ)) lambda = _
    rfl
  rw [← hfamily]
  exact hscaled

/-- The physical response of one source block on one marked target cell. -/
noncomputable def threeAdicHierarchicalBasisResponse (r : ℕ) (lambda : ℝ)
    (c : ThreeAdicTensorCell r) (beta : ThreeAdicTensorLayer r)
    (a : Fin (threeAdicBlockRootCount beta + 1)) (h : ℝ) : ℝ :=
  threeAdicTensorCellWeight c.2.1 c.2.2
      (threeAdicBlockFrequency beta a).1 (threeAdicBlockFrequency beta a).2 *
    analyticKernel
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).1 : ℝ) /
        (3 ^ r : ℝ))
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).2 : ℝ) /
        (3 ^ r : ℝ)) lambda h

/-- The row-only nonzero diagonal factor. -/
noncomputable def threeAdicCellDiagonalFactor {r : ℕ}
    (c : ThreeAdicTensorCell r) : ℝ :=
  (3 / 4 : ℝ) *
    (modTwelveCharacter (threeAdicRowUnit c.2.1) *
      modTwelveCharacter (threeAdicRowUnit c.2.2))

theorem threeAdicCellDiagonalFactor_ne_zero {r : ℕ}
    (c : ThreeAdicTensorCell r) : threeAdicCellDiagonalFactor c ≠ 0 := by
  unfold threeAdicCellDiagonalFactor
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero (modTwelveCharacter_ne_zero _) (modTwelveCharacter_ne_zero _))

theorem threeAdicDiagonalKernel_hasFPowerSeriesAt {r : ℕ} {lambda : ℝ}
    (hlambda : 1 ≤ lambda) (kl : ThreeAdicTensorLayer r)
    (a : Fin (threeAdicBlockRootCount kl + 1)) :
    HasFPowerSeriesAt (threeAdicDiagonalKernel r lambda kl a)
      (threeAdicDiagonalKernelSeries r lambda kl a) 0 := by
  have haPos : 0 <
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).1 : ℝ) /
        (3 ^ r : ℝ)) := by
    change 0 < threeAdicBlockAlpha r kl (threeAdicBlockIndexEquiv kl a).1
    exact threeAdicBlockAlpha_pos kl _
  have haOne :
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).1 : ℝ) /
        (3 ^ r : ℝ)) < 1 := by
    change threeAdicBlockAlpha r kl (threeAdicBlockIndexEquiv kl a).1 < 1
    exact threeAdicBlockAlpha_lt_one kl _
  have hbPos : 0 <
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).2 : ℝ) /
        (3 ^ r : ℝ)) := by
    change 0 < threeAdicBlockBeta r kl (threeAdicBlockIndexEquiv kl a).2
    exact threeAdicBlockBeta_pos kl _
  have hbOne :
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency kl a).2 : ℝ) /
        (3 ^ r : ℝ)) < 1 := by
    change threeAdicBlockBeta r kl (threeAdicBlockIndexEquiv kl a).2 < 1
    exact threeAdicBlockBeta_lt_one kl _
  have hfps := (analyticKernel_hasFPowerSeriesAt
    haPos haOne hbPos hbOne hlambda).const_smul
      (c := threeAdicBlockFrequencyCharacter kl a)
  change HasFPowerSeriesAt (threeAdicDiagonalKernel r lambda kl a)
    (threeAdicBlockFrequencyCharacter kl a •
      analyticKernelSeries
        ((threeAdicFrequencyValue (r := r)
            (threeAdicBlockFrequency kl a).1 : ℝ) / (3 ^ r : ℝ))
        ((threeAdicFrequencyValue (r := r)
            (threeAdicBlockFrequency kl a).2 : ℝ) / (3 ^ r : ℝ)) lambda) 0
  apply hfps.congr
  exact Eventually.of_forall fun h => by
    simp only [threeAdicDiagonalKernel, Pi.smul_apply, smul_eq_mul]

theorem threeAdicHierarchicalBasisResponse_contDiffOn {r : ℕ} {lambda : ℝ}
    (hlambda : 1 ≤ lambda) (c : ThreeAdicTensorCell r)
    (beta : ThreeAdicTensorLayer r)
    (a : Fin (threeAdicBlockRootCount beta + 1)) :
    ContDiffOn ℝ 1 (threeAdicHierarchicalBasisResponse r lambda c beta a)
      (Set.Ioo 0 (1 / 4)) := by
  have haPos : 0 <
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).1 : ℝ) /
        (3 ^ r : ℝ)) := by
    change 0 < threeAdicBlockAlpha r beta (threeAdicBlockIndexEquiv beta a).1
    exact threeAdicBlockAlpha_pos beta _
  have haOne :
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).1 : ℝ) /
        (3 ^ r : ℝ)) < 1 := by
    change threeAdicBlockAlpha r beta (threeAdicBlockIndexEquiv beta a).1 < 1
    exact threeAdicBlockAlpha_lt_one beta _
  have hbPos : 0 <
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).2 : ℝ) /
        (3 ^ r : ℝ)) := by
    change 0 < threeAdicBlockBeta r beta (threeAdicBlockIndexEquiv beta a).2
    exact threeAdicBlockBeta_pos beta _
  have hbOne :
      ((threeAdicFrequencyValue (r := r) (threeAdicBlockFrequency beta a).2 : ℝ) /
        (3 ^ r : ℝ)) < 1 := by
    change threeAdicBlockBeta r beta (threeAdicBlockIndexEquiv beta a).2 < 1
    exact threeAdicBlockBeta_lt_one beta _
  unfold threeAdicHierarchicalBasisResponse
  exact contDiffOn_const.mul
    (analyticKernel_contDiffOn_Ioo_quarter haPos haOne hbPos hbOne hlambda)

theorem threeAdicHierarchicalBasisResponse_invisible {r : ℕ} (lambda : ℝ)
    (c : ThreeAdicTensorCell r) (beta : ThreeAdicTensorLayer r)
    (a : Fin (threeAdicBlockRootCount beta + 1))
    (hbelow : ¬ c.1 ≤ beta) :
    threeAdicHierarchicalBasisResponse r lambda c beta a = 0 := by
  have hcoord : beta.1.1 < c.1.1.1 ∨ beta.2.1 < c.1.2.1 := by
    change ¬ (c.1.1 ≤ beta.1 ∧ c.1.2 ≤ beta.2) at hbelow
    rcases not_and_or.mp hbelow with h | h
    · exact Or.inl (show beta.1 < c.1.1 from lt_of_not_ge h)
    · exact Or.inr (show beta.2 < c.1.2 from lt_of_not_ge h)
  funext h
  unfold threeAdicHierarchicalBasisResponse
  rw [threeAdic_tensor_invisible c.1.1.2 c.1.2.2
    c.2.1 c.2.2 (threeAdicBlockFrequency beta a).1
    (threeAdicBlockFrequency beta a).2 hcoord]
  simp

theorem threeAdicHierarchicalBasisResponse_diagonal {r : ℕ} (lambda : ℝ)
    (c : ThreeAdicTensorCell r)
    (v : Fin (threeAdicBlockRootCount c.1 + 1) → ℝ) (h : ℝ) :
    ∑ a, v a * threeAdicHierarchicalBasisResponse r lambda c c.1 a h =
      threeAdicCellDiagonalFactor c *
        ∑ a, v a * threeAdicDiagonalKernel r lambda c.1 a h := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold threeAdicHierarchicalBasisResponse threeAdicCellDiagonalFactor
    threeAdicDiagonalKernel threeAdicBlockFrequencyCharacter
  rw [threeAdic_tensor_diagonal_factor c.1.1.2 c.1.2.2]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Repackage the block coefficient vectors as coefficients on the public
`ThreeAdicMode` type. -/
noncomputable def threeAdicModeCoefficientOfBlocks {r : ℕ}
    (v : ∀ kl : ThreeAdicTensorLayer r,
      Fin (threeAdicBlockRootCount kl + 1) → ℝ)
    (m : ThreeAdicMode r) : ℝ :=
  v ((threeAdicBlockModeEquiv r).symm m).1
    ((threeAdicBlockModeEquiv r).symm m).2

/-- The genuine mode-indexed analytic response on one marked cell. -/
noncomputable def threeAdicModeKernelResponse (r : ℕ) (lambda zeta : ℝ)
    (blockCoeff : ThreeAdicMode r → ℝ) (c : ThreeAdicTensorCell r)
    (h : ℝ) : ℝ :=
  ∑ m : ThreeAdicMode r,
    zeta ^ threeAdicTensorWeight (m.1, m.2.1) * blockCoeff m *
      threeAdicTensorCellWeight c.2.1 c.2.2 m.2.2.1 m.2.2.2 *
      analyticKernel
        ((threeAdicFrequencyValue (r := r) m.2.2.1 : ℝ) / (3 ^ r : ℝ))
        ((threeAdicFrequencyValue (r := r) m.2.2.2 : ℝ) / (3 ^ r : ℝ))
        lambda h

/-- The abstract weighted response used by the hierarchy is definitionally
the same finite sum as the public mode-indexed response. -/
theorem hierarchicalWeightedResponse_threeAdic_eq_modeKernelResponse {r : ℕ}
    (lambda zeta : ℝ)
    (v : ∀ kl : ThreeAdicTensorLayer r,
      Fin (threeAdicBlockRootCount kl + 1) → ℝ)
    (c : ThreeAdicTensorCell r) (h : ℝ) :
    hierarchicalWeightedResponse threeAdicTensorWeight
        (fun c beta h => ∑ a, v beta a *
          threeAdicHierarchicalBasisResponse r lambda c beta a h)
        c zeta h =
      threeAdicModeKernelResponse r lambda zeta
        (threeAdicModeCoefficientOfBlocks v) c h := by
  classical
  unfold hierarchicalWeightedResponse
  simp_rw [Finset.mul_sum]
  change (∑ beta, ∑ a,
      (fun x : Σ kl : ThreeAdicTensorLayer r,
          Fin (threeAdicBlockRootCount kl + 1) =>
        zeta ^ threeAdicTensorWeight x.1 *
          (v x.1 x.2 *
            threeAdicHierarchicalBasisResponse r lambda c x.1 x.2 h))
        ⟨beta, a⟩) = _
  rw [← Fintype.sum_sigma (f := fun x : Σ kl : ThreeAdicTensorLayer r,
    Fin (threeAdicBlockRootCount kl + 1) =>
      zeta ^ threeAdicTensorWeight x.1 *
        (v x.1 x.2 *
          threeAdicHierarchicalBasisResponse r lambda c x.1 x.2 h))]
  unfold threeAdicModeKernelResponse
  apply Fintype.sum_equiv (threeAdicBlockModeEquiv r)
  intro x
  unfold threeAdicModeCoefficientOfBlocks
  rw [Equiv.symm_apply_apply]
  simp only [threeAdicBlockModeEquiv_apply_layer,
    threeAdicBlockModeEquiv_apply_secondLayer,
    threeAdicBlockModeEquiv_apply_frequencies]
  unfold threeAdicHierarchicalBasisResponse
  ring

/-- **Concrete three-adic local hierarchy.**  One common anisotropy threshold
works for all genuine tensor blocks.  Beyond it, one fixed coefficient vector
per block yields every prescribed positive simple root simultaneously on all
marked cells for all sufficiently small positive hierarchy parameters. -/
theorem threeAdicHierarchicalKernelRealization (r : ℕ) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (v : ∀ kl : ThreeAdicTensorLayer r,
          Fin (threeAdicBlockRootCount kl + 1) → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ),
        ∀ᶠ zeta in 𝓝[>] 0,
          (∀ c, Function.Injective (fun s => root c s zeta)) ∧
          ∀ c, ∀ s : Fin (threeAdicBlockRootCount c.1),
            hierarchicalWeightedResponse threeAdicTensorWeight
              (fun c beta h => ∑ a, v beta a *
                threeAdicHierarchicalBasisResponse r lambda c beta a h)
              c zeta (root c s zeta) = 0 ∧
            0 < root c s zeta ∧
            root c s zeta < 1 / 4 ∧
            ∃ dzeta : ℝ, dzeta ≠ 0 ∧
              HasDerivAt
                (hierarchicalWeightedResponse threeAdicTensorWeight
                  (fun c beta h => ∑ a, v beta a *
                    threeAdicHierarchicalBasisResponse r lambda c beta a h)
                  c zeta) dzeta (root c s zeta) := by
  rcases finiteThreeAdicCommonDiagonalKernelSeriesRank r with
    ⟨Lambda, hLambda, hRank⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  exact hierarchicalRealizationOn
    (fun c : ThreeAdicTensorCell r => c.1) threeAdicTensorWeight
    threeAdicTensorWeight_strictMono threeAdicBlockRootCount
    (threeAdicDiagonalKernel r lambda)
    (threeAdicDiagonalKernelSeries r lambda)
    (fun kl => threeAdicDiagonalKernel_hasFPowerSeriesAt
      (hLambda.trans (le_of_lt hlambda)) kl)
    (hRank lambda hlambda)
    (threeAdicHierarchicalBasisResponse r lambda)
    (1 / 4) (by norm_num)
    (fun c beta => threeAdicHierarchicalBasisResponse_contDiffOn
      (hLambda.trans (le_of_lt hlambda)) c beta)
    (fun c beta => threeAdicHierarchicalBasisResponse_invisible lambda c beta)
    threeAdicCellDiagonalFactor threeAdicCellDiagonalFactor_ne_zero
    (threeAdicHierarchicalBasisResponse_diagonal lambda)

/-- Public mode-indexed form of the concrete hierarchy theorem. -/
theorem threeAdicModeKernelRealization (r : ℕ) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      ∃ (blockCoeff : ThreeAdicMode r → ℝ)
        (root : ∀ c : ThreeAdicTensorCell r,
          Fin (threeAdicBlockRootCount c.1) → ℝ → ℝ),
        ∀ᶠ zeta in 𝓝[>] 0,
          (∀ c, Function.Injective (fun s => root c s zeta)) ∧
          ∀ c, ∀ s : Fin (threeAdicBlockRootCount c.1),
            threeAdicModeKernelResponse r lambda zeta blockCoeff c
                (root c s zeta) = 0 ∧
            0 < root c s zeta ∧ root c s zeta < 1 / 4 ∧
            ∃ dzeta : ℝ, dzeta ≠ 0 ∧
              HasDerivAt (threeAdicModeKernelResponse r lambda zeta blockCoeff c)
                dzeta (root c s zeta) := by
  rcases threeAdicHierarchicalKernelRealization r with
    ⟨Lambda, hLambda, hrealize⟩
  refine ⟨Lambda, hLambda, ?_⟩
  intro lambda hlambda
  rcases hrealize lambda hlambda with ⟨v, root, hevent⟩
  refine ⟨threeAdicModeCoefficientOfBlocks v, root, ?_⟩
  filter_upwards [hevent] with zeta hzeta
  refine ⟨hzeta.1, ?_⟩
  intro c s
  rcases hzeta.2 c s with ⟨hzero, hpos, hquarter, d, hd, hderiv⟩
  have heq :
      hierarchicalWeightedResponse threeAdicTensorWeight
        (fun c beta h => ∑ a, v beta a *
          threeAdicHierarchicalBasisResponse r lambda c beta a h)
        c zeta =
      threeAdicModeKernelResponse r lambda zeta
        (threeAdicModeCoefficientOfBlocks v) c := by
    funext h
    exact hierarchicalWeightedResponse_threeAdic_eq_modeKernelResponse
      lambda zeta v c h
  refine ⟨?_, hpos, hquarter, d, hd, ?_⟩
  · rw [← heq]
    exact hzero
  · rw [← heq]
    exact hderiv

end Hilbert16
