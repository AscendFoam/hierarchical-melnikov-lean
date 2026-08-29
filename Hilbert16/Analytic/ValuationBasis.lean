import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

namespace Hilbert16

/-!
# A valuation basis from separating coefficient functionals

This is the finite-dimensional Gaussian-elimination step behind Paper
Lemma 2.1.  It is deliberately stated for an arbitrary sequence of linear
coefficient functionals.  If those functionals separate points, a finite
dimensional space has a basis whose first nonzero coefficient indices are
strictly increasing.
-/

open Module

/-- A finite-dimensional vector space equipped with a separating sequence of
linear coefficient functionals admits a basis with strictly increasing leading
indices. -/
theorem exists_valuationBasis_of_separating_coefficients
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (coeff : ℕ → M →ₗ[ℝ] ℝ)
    (hdim : finrank ℝ M = n)
    (hsep : ∀ x : M, (∀ k, coeff k x = 0) → x = 0) :
    ∃ (q : Fin n → ℕ) (b : Basis (Fin n) ℝ M),
      StrictMono q ∧ ∀ j, coeff (q j) (b j) ≠ 0 ∧
        ∀ k < q j, coeff k (b j) = 0 := by
  classical
  induction n generalizing M with
  | zero =>
      have hzero : ∀ x : M, x = 0 :=
        finrank_zero_iff_forall_zero.mp hdim
      letI : Subsingleton M := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
      refine ⟨Fin.elim0, Basis.empty M, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro j
        exact Fin.elim0 j
  | succ n ih =>
      have hpos : 0 < finrank ℝ M := by rw [hdim]; omega
      rcases Module.finrank_pos_iff_exists_ne_zero.mp hpos with ⟨x, hx⟩
      have hxcoeff : ∃ k, coeff k x ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hx (hsep x hall)
      have hexists : ∃ k, ∃ y : M, coeff k y ≠ 0 := by
        rcases hxcoeff with ⟨k, hk⟩
        exact ⟨k, x, hk⟩
      let q0 := Nat.find hexists
      rcases Nat.find_spec hexists with ⟨y, hy⟩
      let L : M →ₗ[ℝ] ℝ := coeff q0
      have hyL : L y ≠ 0 := by simpa [L, q0] using hy
      have hL : L ≠ 0 := by
        intro hzero
        apply hy
        exact LinearMap.congr_fun hzero y
      let N : Submodule ℝ M := LinearMap.ker L
      have hdimN : finrank ℝ N = n := by
        have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hL
        rw [hdim] at hker
        have hker' : finrank ℝ (LinearMap.ker L) = n := by omega
        simpa [N] using hker'
      let coeffN : ℕ → N →ₗ[ℝ] ℝ := fun k => (coeff k).comp N.subtype
      have hsepN : ∀ z : N, (∀ k, coeffN k z = 0) → z = 0 := by
        intro z hz
        apply Subtype.ext
        exact hsep z.1 (fun k => hz k)
      rcases ih (M := N) coeffN hdimN hsepN with ⟨qN, bN, hqN, hbN⟩
      have hminimal {k : ℕ} (hk : k < q0) (z : M) : coeff k z = 0 := by
        by_contra hz
        have hle : q0 ≤ k := Nat.find_min' hexists ⟨z, hz⟩
        omega
      have hq0lt : ∀ j, q0 < qN j := by
        intro j
        by_contra hnot
        have hle : qN j ≤ q0 := Nat.not_lt.mp hnot
        rcases hle.eq_or_lt with heq | hlt
        · have hker : L (bN j).1 = 0 := (bN j).2
          exact (hbN j).1 (by simpa [coeffN, L, heq] using hker)
        · exact (hbN j).1 (by simpa [coeffN] using hminimal hlt (bN j).1)
      have hli : ∀ (c : ℝ), ∀ z ∈ N, c • y + z = 0 → c = 0 := by
        intro c z hzN hcz
        have happ := congrArg L hcz
        have hz : L z = 0 := hzN
        simp only [map_add, map_smul, map_zero, hz, add_zero] at happ
        exact (mul_eq_zero.mp happ).resolve_right hy
      have hsp : ∀ z : M, ∃ c : ℝ, z + c • y ∈ N := by
        intro z
        refine ⟨-(L z / L y), ?_⟩
        change L (z + (-(L z / L y)) • y) = 0
        simp only [map_add, map_smul]
        simp only [smul_eq_mul]
        field_simp [hyL]
        ring
      let b : Basis (Fin (n + 1)) ℝ M := Basis.mkFinCons y bN hli hsp
      let q : Fin (n + 1) → ℕ := Fin.cons q0 qN
      refine ⟨q, b, ?_, ?_⟩
      · change StrictMono (Fin.cons q0 qN)
        rw [Fin.strictMono_cons]
        exact ⟨hq0lt, hqN⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · have hlead : coeff q0 y ≠ 0 := hy
          refine ⟨?_, ?_⟩
          · simpa [q, b] using hlead
          · intro k hk
            simpa [q, b] using hminimal hk y
        · have hi := hbN i
          simpa [q, b, coeffN] using hi

/-!
## Application to convergent one-variable power series
-/

open scoped BigOperators

/-- A finite linear combination of formal multilinear series. -/
noncomputable def formalSeriesCombination {m : ℕ}
    (p : Fin m → FormalMultilinearSeries ℝ ℝ ℝ)
    (a : Fin m → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  Fintype.linearCombination ℝ p a

/-- Evaluation of one scalar Taylor coefficient is a linear functional on
formal multilinear series. -/
noncomputable def formalSeriesCoeffFunctional (k : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ →ₗ[ℝ] ℝ where
  toFun p := p.coeff k
  map_add' p r := by
    change ((p + r) k) 1 = (p k) 1 + (r k) 1
    rfl
  map_smul' c p := by
    change ((c • p) k) 1 = c * (p k) 1
    rfl

/-- The `k`th scalar Taylor coefficient of a finite formal-series combination. -/
noncomputable def formalSeriesCoefficientLinear {m : ℕ}
    (p : Fin m → FormalMultilinearSeries ℝ ℝ ℝ) (k : ℕ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ :=
  (formalSeriesCoeffFunctional k).comp (Fintype.linearCombination ℝ p)

theorem formalSeriesCombination_coeff {m : ℕ}
    (p : Fin m → FormalMultilinearSeries ℝ ℝ ℝ)
    (a : Fin m → ℝ) (k : ℕ) :
    (formalSeriesCombination p a).coeff k = formalSeriesCoefficientLinear p k a := by
  rfl

/-- A finite linear combination of functions and the same combination of their
power series have matching power-series expansions. -/
theorem hasFPowerSeriesAt_formalSeriesCombination {m : ℕ}
    (f : Fin m → ℝ → ℝ)
    (p : Fin m → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0) (a : Fin m → ℝ) :
    HasFPowerSeriesAt (fun h => ∑ j, a j * f j h)
      (formalSeriesCombination p a) 0 := by
  classical
  rw [formalSeriesCombination, Fintype.linearCombination_apply]
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty =>
      simpa using (hasFPowerSeriesAt_const (c := (0 : ℝ)) (e := (0 : ℝ)))
  | @insert j s hj ih =>
      have hterm := (hp j).const_smul (c := a j)
      have hadd := hterm.add ih
      convert hadd using 1 <;> ext h <;>
        simp [Finset.sum_insert, hj, Pi.smul_apply, smul_eq_mul]

/-- Linearly independent convergent one-variable power series yield an actual
analytic valuation basis.  The change-of-basis vectors form a basis of the
original coefficient space, the valuations are strictly increasing, and every
new basis function is factored globally as `h^q * g(h)` with `g(0) ≠ 0`. -/
theorem exists_factored_valuationBasis_of_linearlyIndependent_series {m : ℕ}
    (f : Fin m → ℝ → ℝ)
    (p : Fin m → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0)
    (hlin : LinearIndependent ℝ p) :
    ∃ (q : Fin m → ℕ) (b : Basis (Fin m) ℝ (Fin m → ℝ))
      (g : Fin m → ℝ → ℝ),
      StrictMono q ∧ (∀ j, AnalyticAt ℝ (g j) 0) ∧
      (∀ j, g j 0 ≠ 0) ∧
      ∀ j h, ∑ i, b j i * f i h = h ^ q j * g j h := by
  classical
  let coeff : ℕ → (Fin m → ℝ) →ₗ[ℝ] ℝ := formalSeriesCoefficientLinear p
  have hsep : ∀ a : Fin m → ℝ, (∀ k, coeff k a = 0) → a = 0 := by
    intro a ha
    have hcomb : formalSeriesCombination p a = 0 := by
      apply FormalMultilinearSeries.ext
      intro k
      apply FormalMultilinearSeries.coeff_eq_zero.mp
      simpa [formalSeriesCombination_coeff, coeff] using ha k
    have hinj : Function.Injective (Fintype.linearCombination ℝ p) :=
      hlin.fintypeLinearCombination_injective
    apply hinj
    simpa [Fintype.linearCombination_apply, formalSeriesCombination] using hcomb
  have hdim : finrank ℝ (Fin m → ℝ) = m := by simp
  rcases exists_valuationBasis_of_separating_coefficients m coeff hdim hsep with
    ⟨q, b, hq, hb⟩
  let fB : Fin m → ℝ → ℝ := fun j h => ∑ i, b j i * f i h
  let pB : Fin m → FormalMultilinearSeries ℝ ℝ ℝ := fun j =>
    formalSeriesCombination p (b j)
  have hpB : ∀ j, HasFPowerSeriesAt (fB j) (pB j) 0 := by
    intro j
    exact hasFPowerSeriesAt_formalSeriesCombination f p hp (b j)
  have hcoeffB : ∀ j, (pB j).coeff (q j) ≠ 0 ∧
      ∀ k < q j, (pB j).coeff k = 0 := by
    intro j
    simpa [pB, formalSeriesCombination_coeff, coeff] using hb j
  have hpBne : ∀ j, pB j ≠ 0 := by
    intro j hzero
    apply (hcoeffB j).1
    rw [hzero]
    rfl
  have horder : ∀ j, (pB j).order = q j := by
    intro j
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : q j < (pB j).order := Nat.lt_of_not_ge hnot
      exact (hcoeffB j).1 (FormalMultilinearSeries.coeff_eq_zero.mpr
        ((pB j).apply_eq_zero_of_lt_order hlt))
    · by_contra hnot
      have hlt : (pB j).order < q j := Nat.lt_of_not_ge hnot
      have hnonzero := (pB j).apply_order_ne_zero (hpBne j)
      exact hnonzero (FormalMultilinearSeries.coeff_eq_zero.mp
        ((hcoeffB j).2 _ hlt))
  let g : Fin m → ℝ → ℝ := fun j =>
    (Function.swap dslope 0)^[q j] (fB j)
  refine ⟨q, b, g, hq, ?_, ?_, ?_⟩
  · intro j
    exact ((hpB j).has_fpower_series_iterate_dslope_fslope (q j)).analyticAt
  · intro j
    have hne := (hpB j).iterate_dslope_fslope_ne_zero (hpBne j)
    simpa [g, horder j] using hne
  · intro j h
    have hfactor := (hpB j).eq_pow_order_mul_iterate_dslope h
    simpa [fB, g, horder j, smul_eq_mul] using hfactor

end Hilbert16
