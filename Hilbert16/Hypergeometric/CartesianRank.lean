import Hilbert16.Hypergeometric.ShiftIndependence
import Hilbert16.Spikes.ExactMelnikovKernel
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace Hilbert16

open Finset Polynomial
open Spikes

/-! ### The `beta ^ 2` polynomial Vandermonde in Paper Proposition 5.2 -/

/-- The monic degree-`m` polynomial in `X = beta ^ 2` underlying `U_m(beta)`. -/
noncomputable def formalTwoFZeroMonicPolynomial (m : ℕ) : ℝ[X] :=
  ∏ k ∈ Finset.range m, (X - C (4 * (k : ℝ) ^ 2))

/-- The nonzero leading scalar relating `U_m(beta)` to the monic polynomial in `beta ^ 2`. -/
noncomputable def formalTwoFZeroSquareLeading (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m / ((4 : ℝ) ^ m * (m.factorial : ℝ))

theorem formalTwoFZeroMonicPolynomial_monic (m : ℕ) :
    (formalTwoFZeroMonicPolynomial m).Monic := by
  unfold formalTwoFZeroMonicPolynomial
  exact Polynomial.monic_prod_X_sub_C (fun k : ℕ => 4 * (k : ℝ) ^ 2) (Finset.range m)

theorem formalTwoFZeroMonicPolynomial_natDegree (m : ℕ) :
    (formalTwoFZeroMonicPolynomial m).natDegree = m := by
  unfold formalTwoFZeroMonicPolynomial
  rw [Polynomial.natDegree_prod_of_monic]
  · simp only [Polynomial.natDegree_X_sub_C]
    simp
  · intro k _
    exact Polynomial.monic_X_sub_C _

theorem formalTwoFZeroSquareLeading_ne_zero (m : ℕ) :
    formalTwoFZeroSquareLeading m ≠ 0 := by
  unfold formalTwoFZeroSquareLeading
  positivity

/-- Paper Eq. (5.9): `U_m(beta)` is an exact degree-`m` polynomial in `beta ^ 2`, with the
explicit nonzero leading coefficient `(-1)^m / (4^m m!)`. -/
theorem formalTwoFZeroCoefficient_eq_squarePolynomial (beta : ℝ) (m : ℕ) :
    formalTwoFZeroCoefficient beta m =
      formalTwoFZeroSquareLeading m *
        (formalTwoFZeroMonicPolynomial m).eval (beta ^ 2) := by
  induction m with
  | zero =>
      simp [formalTwoFZeroSquareLeading, formalTwoFZeroMonicPolynomial]
  | succ m ih =>
      rw [formalTwoFZeroCoefficient, ascPochhammer_succ_right]
      simp only [eval_mul, eval_add, eval_X, eval_natCast]
      rw [formalTwoFZeroCoefficient] at ih
      rw [show (m + 1).factorial = (m + 1) * m.factorial by
        simpa [Nat.mul_comm] using Nat.factorial_succ m]
      rw [show formalTwoFZeroMonicPolynomial (m + 1) =
          formalTwoFZeroMonicPolynomial m * (X - C (4 * (m : ℝ) ^ 2)) by
        simp [formalTwoFZeroMonicPolynomial, Finset.prod_range_succ]]
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      calc
        (ascPochhammer ℝ m).eval (-beta / 2) * (-beta / 2 + (m : ℝ)) *
              ((ascPochhammer ℝ m).eval (beta / 2) * (beta / 2 + (m : ℝ))) /
            (((m + 1) * m.factorial : ℕ) : ℝ) =
          ((ascPochhammer ℝ m).eval (-beta / 2) *
              (ascPochhammer ℝ m).eval (beta / 2) / (m.factorial : ℝ)) *
            ((-beta / 2 + (m : ℝ)) * (beta / 2 + (m : ℝ)) / (m + 1 : ℝ)) := by
              push_cast
              field_simp
        _ = formalTwoFZeroSquareLeading (m + 1) *
              ((formalTwoFZeroMonicPolynomial m).eval (beta ^ 2) *
                (beta ^ 2 - 4 * (m : ℝ) ^ 2)) := by
              rw [ih]
              unfold formalTwoFZeroSquareLeading
              rw [Nat.factorial_succ]
              push_cast
              field_simp
              ring

/-- The square nodes used by the coefficient Vandermonde remain injective for positive,
pairwise-distinct parameters. -/
theorem sq_injective_of_pos {e : ℕ} {beta : Fin e → ℝ}
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta) :
    Function.Injective (fun j => (beta j) ^ 2) := by
  intro i j hij
  apply hbeta_injective
  nlinarith [hbeta_pos i, hbeta_pos j]

/-- The coefficient matrix `U_m(beta_j)`, oriented with parameter rows and Taylor-order columns. -/
noncomputable def borelCoefficientMatrix {e : ℕ} (beta : Fin e → ℝ) :
    Matrix (Fin e) (Fin e) ℝ :=
  fun j m => formalTwoFZeroCoefficient (beta j) m.val

/-- The `beta ^ 2` polynomial Vandermonde of Paper Proposition 5.2 is nonsingular. -/
theorem borelCoefficientMatrix_det_ne_zero {e : ℕ} (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta) :
    (borelCoefficientMatrix beta).det ≠ 0 := by
  let P : Fin e → ℝ[X] := fun m => formalTwoFZeroMonicPolynomial m.val
  let E : Matrix (Fin e) (Fin e) ℝ :=
    Matrix.of fun j m => (P m).eval ((beta j) ^ 2)
  let D : Matrix (Fin e) (Fin e) ℝ :=
    Matrix.diagonal fun m => formalTwoFZeroSquareLeading m.val
  have hdegree : ∀ m, (P m).natDegree = m.val := by
    intro m
    exact formalTwoFZeroMonicPolynomial_natDegree m.val
  have hmonic : ∀ m, (P m).Monic := by
    intro m
    exact formalTwoFZeroMonicPolynomial_monic m.val
  have hdetE : E.det ≠ 0 := by
    have hdet := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun j => (beta j) ^ 2) P hdegree hmonic
    rw [← hdet]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sq_injective_of_pos hbeta_pos hbeta_injective)
  have hdetD : D.det ≠ 0 := by
    simp only [D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun m _ =>
      formalTwoFZeroSquareLeading_ne_zero m.val
  have hmatrix : borelCoefficientMatrix beta = E * D := by
    ext j m
    simp only [borelCoefficientMatrix, Matrix.mul_apply, D, Matrix.diagonal_apply,
      E, P, Matrix.of_apply]
    rw [Finset.sum_eq_single m]
    · simp only [if_pos]
      simpa only [mul_comm] using
        formalTwoFZeroCoefficient_eq_squarePolynomial (beta j) m.val
    · intro k _ hkm
      simp [hkm]
    · simp
  rw [hmatrix, Matrix.det_mul]
  exact mul_ne_zero hdetE hdetD

/-! ### Extracting a finite Taylor minor -/

/-- A finite linearly independent family of scalar-valued functions admits a square nonzero
evaluation minor.  Applied with `alpha = ℕ`, this is the finite Taylor minor used in Paper
Proposition 5.2. -/
theorem exists_evaluation_minor_of_linearIndependent
    {ι alpha : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → alpha → ℝ) (hf : LinearIndependent ℝ f) :
    ∃ row : ι → alpha,
      (Matrix.of fun i j => f j (row i)).det ≠ 0 := by
  classical
  let S : Set (ι → ℝ) := Set.range (flip f)
  have hspan : Submodule.span ℝ S = ⊤ := by
    exact (span_flip_eq_top_iff_linearIndependent (f := f)).mpr hf
  letI : Module.Finite ℝ (Submodule.span ℝ S) := by
    rw [hspan]
    infer_instance
  obtain ⟨g, hg_mem, _, hg_independent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ℝ) S
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ S) = Fintype.card ι := by
    rw [hspan, finrank_top]
    exact Module.finrank_pi ℝ
  let indexEquiv : ι ≃ Fin (Module.finrank ℝ (Submodule.span ℝ S)) :=
    (Fintype.equivFin ι).trans (finCongr hfinrank.symm)
  have hgreindexed : LinearIndependent ℝ (fun i : ι => g (indexEquiv i)) :=
    hg_independent.comp indexEquiv indexEquiv.injective
  have hg_range : ∀ i : ι, ∃ x : alpha, g (indexEquiv i) = flip f x := by
    intro i
    have hmem := hg_mem (indexEquiv i)
    change g (indexEquiv i) ∈ Set.range (flip f) at hmem
    rcases hmem with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  let row : ι → alpha := fun i => Classical.choose (hg_range i)
  have hrow : ∀ i, g (indexEquiv i) = flip f (row i) := by
    intro i
    exact Classical.choose_spec (hg_range i)
  let A : Matrix ι ι ℝ := Matrix.of fun i j => f j (row i)
  have hA_rows : LinearIndependent ℝ A.row := by
    have heq : (fun i : ι => g (indexEquiv i)) = A.row := by
      funext i j
      rw [hrow i]
      rfl
    rwa [← heq]
  have hA_unit : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hA_rows
  have hdet_unit : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA_unit
  exact ⟨row, hdet_unit.ne_zero⟩

/-- The Borel--Gauss shifted family has a finite square Taylor minor with nonzero determinant. -/
theorem exists_borelGaussShiftTaylorMinor
    {d e : ℕ} (alpha : Fin d → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha) :
    ∃ row : (Fin d × Fin e) → ℕ,
      (Matrix.of fun iq jq =>
        formalTwoFZeroShift (alpha jq.1) jq.2.val (row iq)).det ≠ 0 := by
  have hbase := formalTwoFZeroShift_linearIndependent (e := e) alpha
    halpha_pos halpha_one halpha_injective
  have hreindexed : LinearIndependent ℝ
      (fun iq : Fin d × Fin e =>
        formalTwoFZeroShift (alpha iq.1) iq.2.val) :=
    hbase.comp (fun iq : Fin d × Fin e => (iq.2, iq.1)) (by
      intro iq jq h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  exact exists_evaluation_minor_of_linearIndependent _ hreindexed

/-! ### Column transformation and coefficientwise anisotropic limit -/

/-- The product coefficient with the second (`beta`) Taylor order as summation index. -/
theorem formalProductRow_eq_sum_betaOrder (alpha beta lambda : ℝ) (n : ℕ) :
    formalProductRow alpha beta lambda n =
      ∑ m ∈ Finset.range (n + 1),
        formalTwoFZeroCoefficient alpha (n - m) *
          formalTwoFZeroCoefficient beta m * (lambda⁻¹) ^ m := by
  unfold formalProductRow
  rw [← Finset.sum_range_reflect
    (fun p => formalTwoFZeroCoefficient alpha p *
      formalTwoFZeroCoefficient beta (n - p) * (lambda⁻¹) ^ (n - p)) (n + 1)]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (by simpa only [Nat.add_comm] using hm)
  rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn]

/-- Entrywise form of `V⁻¹ V = 1` for the `U_m(beta_j)` coefficient matrix. -/
theorem borelCoefficientMatrix_inv_mul_apply {e : ℕ} (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta) (q m : Fin e) :
    ∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
        formalTwoFZeroCoefficient (beta j) m.val = if q = m then 1 else 0 := by
  have hdet := borelCoefficientMatrix_det_ne_zero beta hbeta_pos hbeta_injective
  have hunit : IsUnit (borelCoefficientMatrix beta).det :=
    (isUnit_iff_ne_zero.mpr hdet)
  have hmatrix := Matrix.nonsing_inv_mul (borelCoefficientMatrix beta) hunit
  have hentry := congrFun (congrFun hmatrix q) m
  simpa only [Matrix.mul_apply, borelCoefficientMatrix, Matrix.one_apply] using hentry

/-- The column transform from Paper Eq. (5.10), at a fixed Taylor coefficient. -/
noncomputable def transformedProductCoefficient {e : ℕ} (beta : Fin e → ℝ)
    (alpha lambda : ℝ) (q : Fin e) (n : ℕ) : ℝ :=
  lambda ^ q.val *
    ∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
      formalProductRow alpha (beta j) lambda n

theorem transformedProductCoefficient_eq_sum {e : ℕ} (beta : Fin e → ℝ)
    (alpha lambda : ℝ) (q : Fin e) (n : ℕ) :
    transformedProductCoefficient beta alpha lambda q n =
      ∑ m ∈ Finset.range (n + 1),
        formalTwoFZeroCoefficient alpha (n - m) *
          (∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
            formalTwoFZeroCoefficient (beta j) m) *
          (lambda ^ q.val * (lambda⁻¹) ^ m) := by
  unfold transformedProductCoefficient
  simp_rw [formalProductRow_eq_sum_betaOrder]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tendsto_pow_mul_inv_pow_same (q : ℕ) :
    Filter.Tendsto (fun x : ℝ => x ^ q * (x⁻¹) ^ q)
      Filter.atTop (nhds 1) := by
  apply (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
    Filter.atTop (nhds 1)).congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [inv_pow] using (mul_inv_cancel₀ (pow_ne_zero q hx.ne')).symm

theorem tendsto_pow_mul_inv_pow_of_lt {q m : ℕ} (hqm : q < m) :
    Filter.Tendsto (fun x : ℝ => x ^ q * (x⁻¹) ^ m)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun x : ℝ => (x⁻¹) ^ (m - q))
      Filter.atTop (nhds ((0 : ℝ) ^ (m - q))) :=
    tendsto_inv_atTop_zero.pow (m - q)
  have hpow' : Filter.Tendsto (fun x : ℝ => (x⁻¹) ^ (m - q))
      Filter.atTop (nhds 0) := by
    simpa [zero_pow (Nat.sub_pos_of_lt hqm).ne'] using hpow
  apply hpow'.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hm : m = q + (m - q) := by omega
  have hcancel : x ^ q * (x⁻¹) ^ q = 1 := by
    simpa only [inv_pow] using mul_inv_cancel₀ (pow_ne_zero q hx.ne')
  calc
    (x⁻¹) ^ (m - q) = 1 * (x⁻¹) ^ (m - q) := by rw [one_mul]
    _ = (x ^ q * (x⁻¹) ^ q) * (x⁻¹) ^ (m - q) := by rw [hcancel]
    _ = x ^ q * ((x⁻¹) ^ q * (x⁻¹) ^ (m - q)) := by ring
    _ = x ^ q * (x⁻¹) ^ (q + (m - q)) := by rw [pow_add]
    _ = x ^ q * (x⁻¹) ^ m := by rw [← hm]

/-- Paper Eq. (5.11): every fixed Taylor coefficient of a transformed product column converges to
the corresponding shifted `₂F₀` coefficient as `lambda → +∞`. -/
theorem transformedProductCoefficient_tendsto {e : ℕ} (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta)
    (alpha : ℝ) (q : Fin e) (n : ℕ) :
    Filter.Tendsto
      (fun lambda : ℝ => transformedProductCoefficient beta alpha lambda q n)
      Filter.atTop
      (nhds (formalTwoFZeroShift alpha q.val n)) := by
  have hterm : ∀ m ∈ Finset.range (n + 1),
      Filter.Tendsto
        (fun lambda : ℝ =>
          formalTwoFZeroCoefficient alpha (n - m) *
            (∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
              formalTwoFZeroCoefficient (beta j) m) *
            (lambda ^ q.val * (lambda⁻¹) ^ m))
        Filter.atTop
        (nhds (if m = q.val then
          formalTwoFZeroCoefficient alpha (n - m) else 0)) := by
    intro m hm
    by_cases hme : m < e
    · let mf : Fin e := ⟨m, hme⟩
      rw [show (∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
            formalTwoFZeroCoefficient (beta j) m) =
          if q = mf then 1 else 0 by
        simpa only [mf] using
          borelCoefficientMatrix_inv_mul_apply beta hbeta_pos hbeta_injective q mf]
      by_cases hq : q = mf
      · rw [if_pos hq]
        have hmq : m = q.val := by simpa [mf] using congrArg Fin.val hq.symm
        subst m
        rw [if_pos rfl]
        simpa only [mul_one] using
          (tendsto_pow_mul_inv_pow_same q.val).const_mul
            (formalTwoFZeroCoefficient alpha (n - q.val))
      · have hmq : m ≠ q.val := by
          intro h
          apply hq
          apply Fin.ext
          simpa [mf] using h.symm
        rw [if_neg hq]
        simpa only [mul_zero, zero_mul, if_neg hmq] using
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
            Filter.atTop (nhds 0))
    · have he_le : e ≤ m := Nat.le_of_not_gt hme
      have hqm : q.val < m := lt_of_lt_of_le q.isLt he_le
      have hdecay := tendsto_pow_mul_inv_pow_of_lt hqm
      have hscaled := hdecay.const_mul
        (formalTwoFZeroCoefficient alpha (n - m) *
          (∑ j, (borelCoefficientMatrix beta)⁻¹ q j *
            formalTwoFZeroCoefficient (beta j) m))
      simpa [if_neg hqm.ne'] using hscaled
  have hsum := tendsto_finsetSum (Finset.range (n + 1)) hterm
  have hsum' : Filter.Tendsto
      (fun lambda : ℝ => transformedProductCoefficient beta alpha lambda q n)
      Filter.atTop
      (nhds (∑ m ∈ Finset.range (n + 1),
        if m = q.val then formalTwoFZeroCoefficient alpha (n - m) else 0)) :=
    hsum.congr' (Filter.Eventually.of_forall fun lambda =>
      (transformedProductCoefficient_eq_sum beta alpha lambda q n).symm)
  simpa [formalTwoFZeroShift] using hsum'

/-- A finite Taylor minor of the transformed product columns. -/
noncomputable def transformedProductMinor {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (row : (Fin d × Fin e) → ℕ) (lambda : ℝ) :
    Matrix (Fin d × Fin e) (Fin d × Fin e) ℝ :=
  fun r iq => transformedProductCoefficient beta (alpha iq.1) lambda iq.2 (row r)

/-- The limiting Taylor minor formed from the shifted `₂F₀` family. -/
noncomputable def borelGaussShiftMinor {d e : ℕ}
    (alpha : Fin d → ℝ) (row : (Fin d × Fin e) → ℕ) :
    Matrix (Fin d × Fin e) (Fin d × Fin e) ℝ :=
  fun r iq => formalTwoFZeroShift (alpha iq.1) iq.2.val (row r)

theorem transformedProductMinor_tendsto {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta)
    (row : (Fin d × Fin e) → ℕ) :
    Filter.Tendsto
      (fun lambda : ℝ => transformedProductMinor alpha beta row lambda)
      Filter.atTop
      (nhds (borelGaussShiftMinor alpha row)) := by
  change Filter.Tendsto
    (fun lambda (r : Fin d × Fin e) (iq : Fin d × Fin e) =>
      transformedProductCoefficient beta (alpha iq.1)
      lambda iq.2 (row r)) Filter.atTop
    (nhds (fun (r : Fin d × Fin e) (iq : Fin d × Fin e) =>
      formalTwoFZeroShift (alpha iq.1) iq.2.val (row r)))
  rw [tendsto_pi_nhds]
  intro r
  rw [tendsto_pi_nhds]
  intro iq
  exact transformedProductCoefficient_tendsto beta hbeta_pos hbeta_injective
    (alpha iq.1) iq.2 (row r)

theorem transformedProductMinor_det_tendsto {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta)
    (row : (Fin d × Fin e) → ℕ) :
    Filter.Tendsto
      (fun lambda : ℝ => (transformedProductMinor alpha beta row lambda).det)
      Filter.atTop
      (nhds (borelGaussShiftMinor alpha row).det) := by
  exact Filter.Tendsto.comp continuous_id.matrix_det.continuousAt
    (transformedProductMinor_tendsto alpha beta hbeta_pos hbeta_injective row)

theorem transformedProductMinor_eventually_det_ne_zero {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_injective : Function.Injective beta)
    (row : (Fin d × Fin e) → ℕ)
    (hrow : (borelGaussShiftMinor alpha row).det ≠ 0) :
    ∃ Lambda : ℝ, ∀ lambda > Lambda,
      (transformedProductMinor alpha beta row lambda).det ≠ 0 := by
  have heventually :=
    (transformedProductMinor_det_tendsto alpha beta hbeta_pos hbeta_injective row).eventually_ne hrow
  rcases (Filter.eventually_atTop.1 heventually) with ⟨Lambda, hLambda⟩
  exact ⟨Lambda, fun lambda hlambda => hLambda lambda hlambda.le⟩

/-! ### Returning from transformed columns to the original product family -/

/-- A Taylor minor of the original anisotropic product columns. -/
noncomputable def anisotropicProductMinor {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (row : (Fin d × Fin e) → ℕ) (lambda : ℝ) :
    Matrix (Fin d × Fin e) (Fin d × Fin e) ℝ :=
  fun r ij => formalProductRow (alpha ij.1) (beta ij.2) lambda (row r)

/-- The block-diagonal column operation used in Paper Eq. (5.10). -/
noncomputable def anisotropicColumnTransform {d e : ℕ}
    (beta : Fin e → ℝ) (lambda : ℝ) :
    Matrix (Fin d × Fin e) (Fin d × Fin e) ℝ :=
  fun ij iq => if ij.1 = iq.1 then
    lambda ^ iq.2.val * (borelCoefficientMatrix beta)⁻¹ iq.2 ij.2
  else 0

theorem transformedProductMinor_eq_mul {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (row : (Fin d × Fin e) → ℕ) (lambda : ℝ) :
    transformedProductMinor alpha beta row lambda =
      anisotropicProductMinor alpha beta row lambda *
        anisotropicColumnTransform beta lambda := by
  ext r iq
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [transformedProductMinor, anisotropicProductMinor,
    anisotropicColumnTransform]
  rw [Finset.sum_eq_single iq.1]
  · simp only [if_pos, transformedProductCoefficient]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro i hi hne
    simp [hne]
  · simp

theorem anisotropicProductMinor_det_ne_zero_of_transformed {d e : ℕ}
    (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (row : (Fin d × Fin e) → ℕ) (lambda : ℝ)
    (htransformed : (transformedProductMinor alpha beta row lambda).det ≠ 0) :
    (anisotropicProductMinor alpha beta row lambda).det ≠ 0 := by
  rw [transformedProductMinor_eq_mul, Matrix.det_mul] at htransformed
  exact fun hzero => htransformed (by rw [hzero, zero_mul])

/-- A nonzero square evaluation minor certifies linear independence of the full functions. -/
theorem linearIndependent_of_evaluation_minor
    {ι alpha : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → alpha → ℝ) (row : ι → alpha)
    (hdet : (Matrix.of fun i j => f j (row i)).det ≠ 0) :
    LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro c hrelation
  let A : Matrix ι ι ℝ := Matrix.of fun i j => f j (row i)
  have hmul : A.mulVec c = 0 := by
    funext i
    have hpoint := congrFun hrelation (row i)
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpoint
    simpa only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply,
      mul_comm] using hpoint
  have hc : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact fun i => congrFun hc i

/-- **Paper Proposition 5.2, formal-series part.**  For finite positive pairwise-distinct parameter
families in `(0,1)`, the anisotropic Cartesian product family has full rank for every sufficiently
large `lambda`. -/
theorem anisotropicCartesianRank
    {d e : ℕ} (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha)
    (hbeta_pos : ∀ j, 0 < beta j)
    (_hbeta_one : ∀ j, beta j < 1)
    (hbeta_injective : Function.Injective beta) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      LinearIndependent ℝ
        (fun ij : Fin d × Fin e => fun n : ℕ =>
          formalProductRow (alpha ij.1) (beta ij.2) lambda n) := by
  obtain ⟨row, hrow⟩ := exists_borelGaussShiftTaylorMinor alpha
    halpha_pos halpha_one halpha_injective
  have hrow' : (borelGaussShiftMinor alpha row).det ≠ 0 := by
    exact hrow
  obtain ⟨threshold, hthreshold⟩ :=
    transformedProductMinor_eventually_det_ne_zero alpha beta hbeta_pos
      hbeta_injective row hrow'
  refine ⟨max 1 threshold, le_max_left _ _, ?_⟩
  intro lambda hlambda
  have htransformed := hthreshold lambda (lt_of_le_of_lt (le_max_right 1 threshold) hlambda)
  have horiginal := anisotropicProductMinor_det_ne_zero_of_transformed
    alpha beta row lambda htransformed
  apply linearIndependent_of_evaluation_minor
    (fun ij : Fin d × Fin e => fun n : ℕ =>
      formalProductRow (alpha ij.1) (beta ij.2) lambda n) row
  exact horiginal

/-- The actual Taylor coefficient in Paper Eq. (3.12), including its nonzero row factor. -/
noncomputable def analyticKernelTaylorCoefficient
    (alpha beta lambda : ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m / ((m + 1).factorial : ℝ) *
    formalProductRow alpha beta lambda m

theorem analyticKernelTaylorRowFactor_ne_zero (m : ℕ) :
    (2 : ℝ) ^ m / ((m + 1).factorial : ℝ) ≠ 0 := by
  positivity

theorem linearIndependent_mul_coordinate_of_ne_zero
    {ι alpha : Type*} [Fintype ι]
    (f : ι → alpha → ℝ) (scale : alpha → ℝ)
    (hscale : ∀ x, scale x ≠ 0) (hf : LinearIndependent ℝ f) :
    LinearIndependent ℝ (fun i x => scale x * f i x) := by
  classical
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hrelation
  apply hf c
  funext x
  have hpoint := congrFun hrelation x
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpoint ⊢
  have hfactored : scale x * (∑ j, c j * f j x) = 0 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc, mul_left_comm] using hpoint
  exact (mul_eq_zero.mp hfactored).resolve_left (hscale x)

/-- The Taylor coefficient sequences of the convergent kernels have the same eventual full rank as
the formal product rows; their analytic realization is discharged by the exact-kernel module. -/
theorem anisotropicAnalyticKernelTaylorRank
    {d e : ℕ} (alpha : Fin d → ℝ) (beta : Fin e → ℝ)
    (halpha_pos : ∀ i, 0 < alpha i)
    (halpha_one : ∀ i, alpha i < 1)
    (halpha_injective : Function.Injective alpha)
    (hbeta_pos : ∀ j, 0 < beta j)
    (hbeta_one : ∀ j, beta j < 1)
    (hbeta_injective : Function.Injective beta) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda,
      LinearIndependent ℝ
        (fun ij : Fin d × Fin e => fun m : ℕ =>
          analyticKernelTaylorCoefficient
            (alpha ij.1) (beta ij.2) lambda m) := by
  obtain ⟨Lambda, hLambda1, hLambda⟩ := anisotropicCartesianRank alpha beta
    halpha_pos halpha_one halpha_injective hbeta_pos hbeta_one hbeta_injective
  refine ⟨Lambda, hLambda1, fun lambda hlambda => ?_⟩
  exact linearIndependent_mul_coordinate_of_ne_zero
    (fun ij : Fin d × Fin e => fun m : ℕ =>
      formalProductRow (alpha ij.1) (beta ij.2) lambda m)
    (fun m => (2 : ℝ) ^ m / ((m + 1).factorial : ℝ))
    analyticKernelTaylorRowFactor_ne_zero (hLambda lambda hlambda)

/-- Paper lines following Proposition 5.2: finitely many blocks, even with block-dependent
dimensions and parameter families, admit one common anisotropy threshold. -/
theorem finiteBlockCommonAnisotropicTaylorRank
    {κ : Type*} [Fintype κ] (d e : κ → ℕ)
    (alpha : ∀ k, Fin (d k) → ℝ) (beta : ∀ k, Fin (e k) → ℝ)
    (halpha_pos : ∀ k i, 0 < alpha k i)
    (halpha_one : ∀ k i, alpha k i < 1)
    (halpha_injective : ∀ k, Function.Injective (alpha k))
    (hbeta_pos : ∀ k j, 0 < beta k j)
    (hbeta_one : ∀ k j, beta k j < 1)
    (hbeta_injective : ∀ k, Function.Injective (beta k)) :
    ∃ Lambda : ℝ, 1 ≤ Lambda ∧ ∀ lambda > Lambda, ∀ k,
      LinearIndependent ℝ
        (fun ij : Fin (d k) × Fin (e k) => fun m : ℕ =>
          analyticKernelTaylorCoefficient
            (alpha k ij.1) (beta k ij.2) lambda m) := by
  classical
  let threshold : κ → ℝ := fun k =>
    Classical.choose (anisotropicAnalyticKernelTaylorRank (alpha k) (beta k)
      (halpha_pos k) (halpha_one k) (halpha_injective k)
      (hbeta_pos k) (hbeta_one k) (hbeta_injective k))
  have hthreshold (k : κ) :
      1 ≤ threshold k ∧ ∀ lambda > threshold k,
        LinearIndependent ℝ
          (fun ij : Fin (d k) × Fin (e k) => fun m : ℕ =>
            analyticKernelTaylorCoefficient
              (alpha k ij.1) (beta k ij.2) lambda m) := by
    exact Classical.choose_spec (anisotropicAnalyticKernelTaylorRank (alpha k) (beta k)
      (halpha_pos k) (halpha_one k) (halpha_injective k)
      (hbeta_pos k) (hbeta_one k) (hbeta_injective k))
  let Lambda : ℝ := max 1 (∑ k, |threshold k|)
  refine ⟨Lambda, le_max_left _ _, ?_⟩
  intro lambda hlambda k
  apply (hthreshold k).2 lambda
  have hterm : |threshold k| ≤ ∑ j, |threshold j| := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (threshold j))
      (Finset.mem_univ k)
  exact lt_of_le_of_lt
    ((le_abs_self (threshold k)).trans
      (hterm.trans (le_max_right (1 : ℝ) (∑ j, |threshold j|))))
    hlambda

end Hilbert16
