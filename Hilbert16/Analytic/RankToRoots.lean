import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.Asymptotics.Lemmas
import Hilbert16.Dynamics.SimpleRoot
import Hilbert16.Analytic.ValuationBasis

set_option autoImplicit false

open scoped BigOperators Polynomial
open Filter
open Module
open scoped Topology

namespace Hilbert16

/-!
# Sparse generalized polynomials with prescribed positive simple roots

This is the finite-dimensional algebraic core of Paper Lemma 2.1.  A nonzero
combination of `d+1` distinct nonnegative integer powers has at most `d`
positive roots counted with multiplicity, by Descartes' rule of signs.  A
homogeneous evaluation system at `d` prescribed points always has a nonzero
coefficient vector.  The root bound then forces all prescribed roots to be
simple.
-/

/-- A nonzero real polynomial has fewer sign variations than nonzero coefficients. -/
theorem Polynomial.signVariations_lt_card_support {P : ℝ[X]} (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  generalize hn : P.support.card = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases he : P.eraseLead = 0
      · have hmono : Polynomial.monomial P.natDegree P.leadingCoeff = P := by
          simpa [he] using P.eraseLead_add_monomial_natDegree_leadingCoeff
        rw [← hmono, Polynomial.signVariations_monomial]
        have hc : P.support.card ≠ 0 := by
          intro hc
          exact hP (Polynomial.card_support_eq_zero.mp hc)
        omega
      · have hcard := P.eraseLead_support_card_lt hP
        have hcardn : P.eraseLead.support.card < n := by omega
        have hrec := ih P.eraseLead.support.card hcardn he rfl
        calc
          P.signVariations ≤ P.eraseLead.signVariations + 1 :=
            Polynomial.signVariations_le_eraseLead_succ P
          _ < P.eraseLead.support.card + 1 := Nat.add_lt_add_right hrec 1
          _ = P.support.card := P.card_support_eraseLead_add_one hP
          _ = n := hn

/-- The polynomial with coefficient vector `a` supported at exponents `q`. -/
noncomputable def sparsePolynomial {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℝ) : ℝ[X] :=
  ∑ j, Polynomial.monomial (q j) (a j)

theorem sparsePolynomial_eval {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℝ)
    (x : ℝ) :
    (sparsePolynomial q a).eval x = ∑ j, a j * x ^ q j := by
  rw [sparsePolynomial, Polynomial.eval_finsetSum]
  simp

theorem sparsePolynomial_coeff_of_injective {m : ℕ} {q : Fin m → ℕ}
    (hq : Function.Injective q) (a : Fin m → ℝ) (j : Fin m) :
    (sparsePolynomial q a).coeff (q j) = a j := by
  classical
  simp [sparsePolynomial, Polynomial.coeff_monomial, hq.eq_iff]

theorem sparsePolynomial_ne_zero {m : ℕ} {q : Fin m → ℕ}
    (hq : Function.Injective q) {a : Fin m → ℝ} (ha : a ≠ 0) :
    sparsePolynomial q a ≠ 0 := by
  intro hzero
  apply ha
  funext j
  have hcoeff := sparsePolynomial_coeff_of_injective hq a j
  rw [hzero] at hcoeff
  simpa using hcoeff.symm

theorem sparsePolynomial_card_support_le {m : ℕ} (q : Fin m → ℕ)
    (a : Fin m → ℝ) :
    (sparsePolynomial q a).support.card ≤ m := by
  classical
  have hsubset : (sparsePolynomial q a).support ⊆ Finset.univ.image q := by
    intro e he
    by_contra hnot
    have hne : ∀ j : Fin m, q j ≠ e := by
      intro j hj
      apply hnot
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    have hcoeff : (sparsePolynomial q a).coeff e = 0 := by
      simp [sparsePolynomial, Polynomial.coeff_monomial, hne]
    exact (Polynomial.mem_support_iff.mp he) hcoeff
  calc
    (sparsePolynomial q a).support.card ≤ (Finset.univ.image q).card :=
      Finset.card_le_card hsubset
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = m := Fintype.card_fin m

/-- Descartes' rule specialized to a polynomial with at most `m` nonzero monomials. -/
theorem sparsePolynomial_positiveRoots_lt {m : ℕ} {q : Fin m → ℕ}
    (hq : Function.Injective q) {a : Fin m → ℝ} (ha : a ≠ 0) :
    (sparsePolynomial q a).roots.countP (0 < ·) < m := by
  let P := sparsePolynomial q a
  have hP : P ≠ 0 := sparsePolynomial_ne_zero hq ha
  calc
    P.roots.countP (0 < ·) ≤ P.signVariations :=
      Polynomial.roots_countP_pos_le_signVariations P
    _ < P.support.card := Polynomial.signVariations_lt_card_support hP
    _ ≤ m := sparsePolynomial_card_support_le q a

/-- The homogeneous evaluation map at `d` points for `d+1` sparse monomials. -/
noncomputable def sparseEvaluationLinear (d : ℕ) (q : Fin (d + 1) → ℕ)
    (rho : Fin d → ℝ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun a s := ∑ j, a j * rho s ^ q j
  map_add' a b := by
    funext s
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply, mul_assoc]

/-- A system of `d` homogeneous evaluations in `d+1` coefficients has a nonzero solution. -/
theorem exists_sparse_coefficients_vanishing (d : ℕ) (q : Fin (d + 1) → ℕ)
    (rho : Fin d → ℝ) :
    ∃ a : Fin (d + 1) → ℝ, a ≠ 0 ∧
      ∀ s, ∑ j, a j * rho s ^ q j = 0 := by
  let L := sparseEvaluationLinear d q rho
  have hnot : ¬Function.Injective L := by
    intro hinj
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi ℝ, Module.finrank_pi ℝ] at hdim
    simp only [Fintype.card_fin] at hdim
    omega
  rcases Function.not_injective_iff.mp hnot with ⟨a, b, hab, hne⟩
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  have hz : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  intro s
  exact congrFun hz s

/--
Given `d` distinct positive points and `d+1` distinct exponents, one sparse
polynomial vanishes simply at every prescribed point.
-/
theorem exists_sparsePolynomial_simpleRoots (d : ℕ) (q : Fin (d + 1) → ℕ)
    (rho : Fin d → ℝ) (hq : Function.Injective q)
    (hrho : Function.Injective rho) (hrhoPos : ∀ s, 0 < rho s) :
    ∃ a : Fin (d + 1) → ℝ, a ≠ 0 ∧
      ∀ s, (sparsePolynomial q a).eval (rho s) = 0 ∧
        (sparsePolynomial q a).derivative.eval (rho s) ≠ 0 := by
  classical
  rcases exists_sparse_coefficients_vanishing d q rho with ⟨a, ha, hazero⟩
  let P := sparsePolynomial q a
  have hP : P ≠ 0 := sparsePolynomial_ne_zero hq ha
  have hroot (s : Fin d) : P.eval (rho s) = 0 := by
    rw [sparsePolynomial_eval]
    exact hazero s
  let positiveRoots := P.roots.filter (0 < ·)
  have hsubset : Finset.univ.image rho ⊆ positiveRoots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨s, rfl⟩
    simp [positiveRoots, hrhoPos s, Polynomial.mem_roots hP, hroot s]
  have himageCard : (Finset.univ.image rho).card = d := by
    rw [Finset.card_image_of_injective _ hrho]
    simp
  have hlower : d ≤ positiveRoots.toFinset.card := by
    rw [← himageCard]
    exact Finset.card_le_card hsubset
  have hrootBound : P.roots.countP (0 < ·) ≤ d := by
    exact Nat.lt_succ_iff.mp (sparsePolynomial_positiveRoots_lt hq ha)
  have hpositiveCard : positiveRoots.card ≤ d := by
    simpa [positiveRoots, Multiset.countP_eq_card_filter] using hrootBound
  have hcardEq : positiveRoots.toFinset.card = positiveRoots.card := by
    apply Nat.le_antisymm (Multiset.toFinset_card_le positiveRoots)
    exact hpositiveCard.trans hlower
  have hnodup : positiveRoots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp hcardEq
  refine ⟨a, ha, ?_⟩
  intro s
  refine ⟨hroot s, ?_⟩
  have hmem : rho s ∈ positiveRoots := by
    simp [positiveRoots, hrhoPos s, Polynomial.mem_roots hP, hroot s]
  have hcountPositive : positiveRoots.count (rho s) = 1 :=
    Multiset.count_eq_one_of_mem hnodup hmem
  have hcountRoot : P.roots.count (rho s) = 1 := by
    simpa [positiveRoots, Multiset.count_filter_of_pos (hrhoPos s)] using hcountPositive
  intro hderiv
  have hmultiple : 1 < P.rootMultiplicity (rho s) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hroot s, hderiv⟩
  rw [← Polynomial.count_roots] at hmultiple
  omega

/-!
## Stability of the prescribed roots under a scaled `C¹` perturbation

In the application, the original small energy is written as `h = τ · ρ`.  After
dividing the Melnikov combination by its lowest common power of `τ`, one obtains
a `C¹` equation `F (τ, ρ) = 0`.  The next structure records exactly the output
needed later: local root branches through the simple roots of `F (0, ·)`, their
positivity and simplicity, and the unscaled location formula
`h_s(τ) = τ ρ_s + o(τ)`.
-/

/-- Simultaneous pointwise continuations of finitely many positive simple roots of a
scaled scalar equation.  Every eventual statement is allowed its own neighborhood;
finiteness permits taking their intersection when a common parameter range is needed. -/
structure ScaledSimpleRootFamily {d : ℕ} (F : ℝ × ℝ → ℝ)
    (rho : Fin d → ℝ) where
  root : Fin d → ℝ → ℝ
  root_at : ∀ s, root s 0 = rho s
  contDiffAt_root : ∀ s, ContDiffAt ℝ 1 (root s) 0
  eventually_zero : ∀ s, ∀ᶠ tau in 𝓝 0, F (tau, root s tau) = 0
  eventually_positive : ∀ s, ∀ᶠ tau in 𝓝 0, 0 < root s tau
  eventually_simple : ∀ s, ∀ᶠ tau in 𝓝 0, ∃ dtau : ℝ, dtau ≠ 0 ∧
    HasDerivAt (fun r : ℝ => F (tau, r)) dtau (root s tau)
  scaled_location : ∀ s,
    (fun tau => tau * root s tau - tau * rho s) =o[𝓝 0] (fun tau : ℝ => tau)

/-- Distinct prescribed roots remain distinct on one common parameter
neighborhood. -/
theorem ScaledSimpleRootFamily.eventually_root_injective
    {d : ℕ} {F : ℝ × ℝ → ℝ} {rho : Fin d → ℝ}
    (H : ScaledSimpleRootFamily F rho) (hrho : Function.Injective rho) :
    ∀ᶠ tau in nhds (0 : ℝ), Function.Injective (fun s => H.root s tau) := by
  have hpairs : ∀ᶠ tau in nhds (0 : ℝ), ∀ s t, s ≠ t →
      H.root s tau ≠ H.root t tau := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro t
    by_cases hst : s = t
    · exact Eventually.of_forall fun _ hne => (hne hst).elim
    · have hs : Tendsto (H.root s) (nhds (0 : ℝ)) (nhds (rho s)) := by
        have hs₀ := (H.contDiffAt_root s).continuousAt
        change Tendsto (H.root s) (nhds (0 : ℝ))
          (nhds (H.root s 0)) at hs₀
        rw [H.root_at s] at hs₀
        exact hs₀
      have ht : Tendsto (H.root t) (nhds (0 : ℝ)) (nhds (rho t)) := by
        have ht₀ := (H.contDiffAt_root t).continuousAt
        change Tendsto (H.root t) (nhds (0 : ℝ))
          (nhds (H.root t 0)) at ht₀
        rw [H.root_at t] at ht₀
        exact ht₀
      have hlimit : rho s - rho t ≠ 0 := by
        rw [sub_ne_zero]
        exact fun heq => hst (hrho heq)
      have hne : ∀ᶠ tau in nhds (0 : ℝ),
          H.root s tau - H.root t tau ≠ 0 :=
        (hs.sub ht).eventually (eventually_ne_nhds hlimit)
      filter_upwards [hne] with tau hneTau
      exact fun _ heq => hneTau (sub_eq_zero.mpr heq)
  filter_upwards [hpairs] with tau hpairsTau
  intro s t heq
  by_contra hst
  exact hpairsTau s t hst heq

/-- Multiplying all continued roots by one positive common scale preserves
their injective indexing. -/
theorem ScaledSimpleRootFamily.eventually_scaledRoot_injective
    {d : ℕ} {F : ℝ × ℝ → ℝ} {rho : Fin d → ℝ}
    (H : ScaledSimpleRootFamily F rho) (hrho : Function.Injective rho) :
    ∀ᶠ tau in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Function.Injective (fun s => tau * H.root s tau) := by
  filter_upwards [H.eventually_root_injective hrho |>.filter_mono inf_le_left,
    self_mem_nhdsWithin] with tau hinj htau
  intro s t heq
  apply hinj
  exact mul_left_cancel₀ htau.ne' heq

/-- The scalar implicit-function theorem, applied at every prescribed positive simple
root, produces a `ScaledSimpleRootFamily`. -/
noncomputable def scaledSimpleRootFamily_of_simpleRoots {d : ℕ}
    (F : ℝ × ℝ → ℝ) (rho : Fin d → ℝ)
    (hF : ∀ s, ContDiffAt ℝ 1 F (0, rho s))
    (hzero : ∀ s, F (0, rho s) = 0)
    (deriv : Fin d → ℝ)
    (hderiv : ∀ s, HasDerivAt (fun r : ℝ => F (0, r)) (deriv s) (rho s))
    (hderiv_ne : ∀ s, deriv s ≠ 0)
    (hrhoPos : ∀ s, 0 < rho s) :
    ScaledSimpleRootFamily F rho := by
  let C : ∀ s, LocalZeroContinuation F (0, rho s) := fun s =>
    ContDiffAt.localZeroContinuation_of_hasDerivAt
      (hF s) (hzero s) (hderiv s) (hderiv_ne s)
  refine
    { root := fun s => (C s).root
      root_at := fun s => (C s).root_at
      contDiffAt_root := fun s => (C s).contDiffAt_root
      eventually_zero := fun s => (C s).eventually_zero
      eventually_positive := ?_
      eventually_simple := ?_
      scaled_location := ?_ }
  · intro s
    have ht0 := (C s).contDiffAt_root.continuousAt
    change Tendsto (C s).root (𝓝 0) (𝓝 ((C s).root 0)) at ht0
    rw [(C s).root_at] at ht0
    have ht : Tendsto (C s).root (𝓝 0) (𝓝 (rho s)) := ht0
    exact ht.eventually (Ioi_mem_nhds (hrhoPos s))
  · intro s
    exact (C s).eventually_hasDerivAt_slice_ne_zero
      (hF s) (hderiv s) (hderiv_ne s)
  · intro s
    have ht0 := (C s).contDiffAt_root.continuousAt
    change Tendsto (C s).root (𝓝 0) (𝓝 ((C s).root 0)) at ht0
    rw [(C s).root_at] at ht0
    have ht : Tendsto (C s).root (𝓝 0) (𝓝 (rho s)) := ht0
    have hsmall :
        (fun tau => (C s).root tau - rho s) =o[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).2
        (tendsto_sub_nhds_zero_iff.2 ht)
    have hmul :=
      (Asymptotics.isBigO_refl (fun tau : ℝ => tau) (𝓝 0)).mul_isLittleO hsmall
    simpa [mul_sub] using hmul

/-!
## The scaled equation attached to a valuation basis

The following definitions encode the exact factorization
`f_j(h) = h ^ q_j * g_j(h)`, with `g_j(0) ≠ 0`.  This form is supplied
canonically by the order-of-vanishing theorem for analytic functions and
removes every apparent division by the small parameter.
-/

/-- The normalized two-variable equation obtained from a factored valuation basis. -/
noncomputable def valuationScaledEquation {m : ℕ} (q : Fin m → ℕ)
    (g : Fin m → ℝ → ℝ) (a : Fin m → ℝ) (u : ℝ × ℝ) : ℝ :=
  ∑ j, (a j / g j 0) * u.2 ^ q j * g j (u.1 * u.2)

/-- The corresponding member of the original finite-dimensional function space. -/
noncomputable def valuationOriginalCombination {m : ℕ} (Q : ℕ)
    (q : Fin m → ℕ) (g : Fin m → ℝ → ℝ)
    (a : Fin m → ℝ) (tau h : ℝ) : ℝ :=
  ∑ j, (a j / g j 0) * tau ^ (Q - q j) * (h ^ q j * g j h)

/-- At the singular parameter, the normalized equation is exactly the sparse
generalized polynomial determined by the leading coefficients. -/
theorem valuationScaledEquation_zero {m : ℕ} (q : Fin m → ℕ)
    (g : Fin m → ℝ → ℝ) (a : Fin m → ℝ)
    (hg0 : ∀ j, g j 0 ≠ 0) (t : ℝ) :
    valuationScaledEquation q g a (0, t) = (sparsePolynomial q a).eval t := by
  rw [valuationScaledEquation, sparsePolynomial_eval]
  apply Finset.sum_congr rfl
  intro j _
  simp only [zero_mul]
  field_simp [hg0 j]

/-- The normalized equation is jointly `C¹` at every point `(0,ρ)` as soon as
the nonvanishing factors are `C¹` at the origin. -/
theorem valuationScaledEquation_contDiffAt {m : ℕ} (q : Fin m → ℕ)
    (g : Fin m → ℝ → ℝ) (a : Fin m → ℝ)
    (hg : ∀ j, ContDiffAt ℝ 1 (g j) 0) (rho : ℝ) :
    ContDiffAt ℝ 1 (valuationScaledEquation q g a) (0, rho) := by
  unfold valuationScaledEquation
  apply ContDiffAt.sum
  intro j _
  have hgcomp : ContDiffAt ℝ 1 (fun u : ℝ × ℝ => g j (u.1 * u.2)) (0, rho) := by
    have hgj : ContDiffAt ℝ 1 (g j) ((0 : ℝ) * rho) := by simpa using hg j
    apply hgj.comp (0, rho)
    fun_prop
  exact ((contDiffAt_const.mul (contDiffAt_snd.pow (q j))).mul hgcomp)

/-- Exact scaling identity.  No removable singularity is present because the
valuation powers have been factored before introducing `τ`. -/
theorem valuationOriginalCombination_scaled {m : ℕ} (Q : ℕ)
    (q : Fin m → ℕ) (g : Fin m → ℝ → ℝ)
    (a : Fin m → ℝ) (hqQ : ∀ j, q j ≤ Q) (tau t : ℝ) :
    valuationOriginalCombination Q q g a tau (tau * t) =
      tau ^ Q * valuationScaledEquation q g a (tau, t) := by
  rw [valuationOriginalCombination, valuationScaledEquation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change a j / g j 0 * tau ^ (Q - q j) * ((tau * t) ^ q j * g j (tau * t)) =
    tau ^ Q * (a j / g j 0 * t ^ q j * g j (tau * t))
  rw [mul_pow]
  calc
    a j / g j 0 * tau ^ (Q - q j) *
          (tau ^ q j * t ^ q j * g j (tau * t)) =
        (a j / g j 0) * (tau ^ (Q - q j) * tau ^ q j) *
          (t ^ q j * g j (tau * t)) := by ring
    _ = (a j / g j 0) * tau ^ Q * (t ^ q j * g j (tau * t)) := by
      rw [← pow_add, Nat.sub_add_cancel (hqQ j)]
    _ = tau ^ Q * (a j / g j 0 * t ^ q j * g j (tau * t)) := by ring

/-- **Rank-to-roots for a supplied valuation basis.**  Distinct positive target
locations and distinct valuation exponents determine one nonzero coefficient
vector.  The associated normalized equation has `d` positive simple `C¹` root
branches with the required unscaled `o(τ)` location formula. -/
theorem exists_scaledSimpleRootFamily_of_valuationBasis (d : ℕ)
    (q : Fin (d + 1) → ℕ) (rho : Fin d → ℝ)
    (hq : Function.Injective q) (hrho : Function.Injective rho)
    (hrhoPos : ∀ s, 0 < rho s)
    (g : Fin (d + 1) → ℝ → ℝ)
    (hg : ∀ j, ContDiffAt ℝ 1 (g j) 0) (hg0 : ∀ j, g j 0 ≠ 0) :
    ∃ a : Fin (d + 1) → ℝ, a ≠ 0 ∧
      Nonempty (ScaledSimpleRootFamily (valuationScaledEquation q g a) rho) := by
  rcases exists_sparsePolynomial_simpleRoots d q rho hq hrho hrhoPos with
    ⟨a, ha, hroots⟩
  let P := sparsePolynomial q a
  let F := valuationScaledEquation q g a
  have hslice : (fun t : ℝ => F (0, t)) = fun t => P.eval t := by
    funext t
    exact valuationScaledEquation_zero q g a hg0 t
  refine ⟨a, ha, ⟨scaledSimpleRootFamily_of_simpleRoots F rho
    (fun s => valuationScaledEquation_contDiffAt q g a hg (rho s))
    (fun s => ?_) (fun s => P.derivative.eval (rho s))
    (fun s => ?_) (fun s => (hroots s).2) hrhoPos⟩⟩
  · rw [congrFun hslice (rho s)]
    exact (hroots s).1
  · rw [hslice]
    exact P.hasDerivAt (rho s)

/-- Every scaled root supplied by the preceding construction is an exact zero
of the corresponding member of the original function space. -/
theorem ScaledSimpleRootFamily.eventually_valuationOriginalCombination_zero
    {d : ℕ} {q : Fin (d + 1) → ℕ} {rho : Fin d → ℝ}
    {g : Fin (d + 1) → ℝ → ℝ} {a : Fin (d + 1) → ℝ}
    (H : ScaledSimpleRootFamily (valuationScaledEquation q g a) rho)
    (Q : ℕ) (hqQ : ∀ j, q j ≤ Q) (s : Fin d) :
    ∀ᶠ tau in 𝓝 0,
      valuationOriginalCombination Q q g a tau (tau * H.root s tau) = 0 := by
  filter_upwards [H.eventually_zero s] with tau hzero
  rw [valuationOriginalCombination_scaled Q q g a hqQ]
  simp [hzero]

/-- Simplicity in the normalized root coordinate transfers back to the original
energy coordinate for every nonzero scale. -/
theorem ScaledSimpleRootFamily.eventually_valuationOriginalCombination_simple
    {d : ℕ} {q : Fin (d + 1) → ℕ} {rho : Fin d → ℝ}
    {g : Fin (d + 1) → ℝ → ℝ} {a : Fin (d + 1) → ℝ}
    (H : ScaledSimpleRootFamily (valuationScaledEquation q g a) rho)
    (Q : ℕ) (hqQ : ∀ j, q j ≤ Q) (s : Fin d) :
    ∀ᶠ tau in 𝓝 0, tau ≠ 0 → ∃ dtau : ℝ, dtau ≠ 0 ∧
      HasDerivAt (valuationOriginalCombination Q q g a tau) dtau
        (tau * H.root s tau) := by
  filter_upwards [H.eventually_simple s] with tau hsimple htau
  rcases hsimple with ⟨dscaled, hdscaled, hderivScaled⟩
  have harg : H.root s tau = (tau * H.root s tau) / tau := by
    field_simp
  have hdiv : HasDerivAt (fun h : ℝ => h / tau) (1 / tau)
      (tau * H.root s tau) :=
    (hasDerivAt_id' (tau * H.root s tau)).div_const tau
  have hcomp := hderivScaled.comp_of_eq
    (tau * H.root s tau) hdiv harg
  have hscaled := hcomp.const_mul (tau ^ Q)
  have heq : (fun h : ℝ => valuationOriginalCombination Q q g a tau h) =
      fun h : ℝ => tau ^ Q * valuationScaledEquation q g a (tau, h / tau) := by
    funext h
    have hs := valuationOriginalCombination_scaled Q q g a hqQ tau (h / tau)
    have hmul : tau * (h / tau) = h := by field_simp
    simpa only [hmul] using hs
  have horiginal : HasDerivAt (valuationOriginalCombination Q q g a tau)
      (tau ^ Q * (dscaled * (1 / tau))) (tau * H.root s tau) := by
    change HasDerivAt (fun h => valuationOriginalCombination Q q g a tau h)
      (tau ^ Q * (dscaled * (1 / tau))) (tau * H.root s tau)
    rw [heq]
    simpa only [Function.comp_apply] using hscaled
  refine ⟨tau ^ Q * (dscaled * (1 / tau)), ?_, horiginal⟩
  exact mul_ne_zero (pow_ne_zero Q htau)
    (mul_ne_zero hdscaled (one_div_ne_zero htau))

/-- For all sufficiently small positive scales, the original combination has
the prescribed positive simple zeros. -/
theorem ScaledSimpleRootFamily.eventually_valuationOriginalCombination_positive_simpleZeros
    {d : ℕ} {q : Fin (d + 1) → ℕ} {rho : Fin d → ℝ}
    {g : Fin (d + 1) → ℝ → ℝ} {a : Fin (d + 1) → ℝ}
    (H : ScaledSimpleRootFamily (valuationScaledEquation q g a) rho)
    (Q : ℕ) (hqQ : ∀ j, q j ≤ Q) :
    ∀ᶠ tau in 𝓝[>] 0, ∀ s : Fin d,
      valuationOriginalCombination Q q g a tau (tau * H.root s tau) = 0 ∧
      0 < tau * H.root s tau ∧
      ∃ dtau : ℝ, dtau ≠ 0 ∧
        HasDerivAt (valuationOriginalCombination Q q g a tau) dtau
          (tau * H.root s tau) := by
  have hzero : ∀ᶠ tau in 𝓝 0, ∀ s : Fin d,
      valuationOriginalCombination Q q g a tau (tau * H.root s tau) = 0 :=
    (Filter.eventually_all).2 (fun s =>
      H.eventually_valuationOriginalCombination_zero Q hqQ s)
  have hpos : ∀ᶠ tau in 𝓝 0, ∀ s : Fin d, 0 < H.root s tau :=
    (Filter.eventually_all).2 H.eventually_positive
  have hsimple : ∀ᶠ tau in 𝓝 0, ∀ s : Fin d, tau ≠ 0 →
      ∃ dtau : ℝ, dtau ≠ 0 ∧
        HasDerivAt (valuationOriginalCombination Q q g a tau) dtau
          (tau * H.root s tau) :=
    (Filter.eventually_all).2 (fun s =>
      H.eventually_valuationOriginalCombination_simple Q hqQ s)
  filter_upwards [hzero.filter_mono inf_le_left, hpos.filter_mono inf_le_left,
    hsimple.filter_mono inf_le_left, self_mem_nhdsWithin] with tau hz hp hs htau
  intro s
  refine ⟨hz s, mul_pos htau (hp s), ?_⟩
  exact hs s htau.ne'

/-!
## End-to-end rank-to-roots theorem
-/

/-- Coefficients of the original analytic family after expanding the
valuation-basis combination back through its change-of-basis matrix. -/
noncomputable def rankToRootsCoefficients {m : ℕ}
    (b : Basis (Fin m) ℝ (Fin m → ℝ)) (Q : ℕ) (q : Fin m → ℕ)
    (g : Fin m → ℝ → ℝ) (a : Fin m → ℝ) (tau : ℝ) : Fin m → ℝ :=
  fun i => ∑ j, ((a j / g j 0) * tau ^ (Q - q j)) * b j i

/-- Expanding the valuation basis gives exactly the same member of the
original finite-dimensional analytic family. -/
theorem rankToRootsCombination_eq_valuationOriginalCombination {m : ℕ}
    (f : Fin m → ℝ → ℝ) (b : Basis (Fin m) ℝ (Fin m → ℝ))
    (Q : ℕ) (q : Fin m → ℕ) (g : Fin m → ℝ → ℝ)
    (a : Fin m → ℝ)
    (hfactor : ∀ j h, ∑ i, b j i * f i h = h ^ q j * g j h)
    (tau h : ℝ) :
    ∑ i, rankToRootsCoefficients b Q q g a tau i * f i h =
      valuationOriginalCombination Q q g a tau h := by
  unfold rankToRootsCoefficients valuationOriginalCombination
  calc
    ∑ i, (∑ j, (a j / g j 0 * tau ^ (Q - q j)) * b j i) * f i h =
        ∑ i, ∑ j, (a j / g j 0 * tau ^ (Q - q j)) * (b j i * f i h) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j, ∑ i, (a j / g j 0 * tau ^ (Q - q j)) * (b j i * f i h) :=
      Finset.sum_comm
    _ = ∑ j, (a j / g j 0 * tau ^ (Q - q j)) *
          (∑ i, b j i * f i h) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, (a j / g j 0) * tau ^ (Q - q j) * (h ^ q j * g j h) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hfactor j h]

/-- **Paper Lemma 2.1 (rank-to-roots), convergent-series form.**

For `d+1` linearly independent analytic germs and any `d` distinct positive
target locations, a parameter-dependent member of their span has `d` positive
simple roots.  Their energy locations are `τ ρ_s + o(τ)`.  The statement also
covers `d = 0`, i.e. the paper's one-dimensional edge case. -/
theorem rankToSimplePositiveRoots (d : ℕ)
    (f : Fin (d + 1) → ℝ → ℝ)
    (p : Fin (d + 1) → FormalMultilinearSeries ℝ ℝ ℝ)
    (hp : ∀ j, HasFPowerSeriesAt (f j) (p j) 0)
    (hlin : LinearIndependent ℝ p)
    (rho : Fin d → ℝ) (hrho : Function.Injective rho)
    (hrhoPos : ∀ s, 0 < rho s) :
    ∃ (A : ℝ → Fin (d + 1) → ℝ) (root : Fin d → ℝ → ℝ),
      (∀ s, root s 0 = rho s) ∧
      (∀ s, (fun tau => tau * root s tau - tau * rho s) =o[𝓝 0]
        (fun tau : ℝ => tau)) ∧
      ∀ᶠ tau in 𝓝[>] 0,
        Function.Injective (fun s => tau * root s tau) ∧
        ∀ s : Fin d,
          (∑ i, A tau i * f i (tau * root s tau)) = 0 ∧
          0 < tau * root s tau ∧
          ∃ dtau : ℝ, dtau ≠ 0 ∧
            HasDerivAt (fun h => ∑ i, A tau i * f i h) dtau
              (tau * root s tau) := by
  rcases exists_factored_valuationBasis_of_linearlyIndependent_series f p hp hlin with
    ⟨q, b, g, hq, hgAnalytic, hg0, hfactor⟩
  have hqInj : Function.Injective q := hq.injective
  have hgC1 : ∀ j, ContDiffAt ℝ 1 (g j) 0 := by
    intro j
    exact (hgAnalytic j).contDiffAt
  rcases exists_scaledSimpleRootFamily_of_valuationBasis d q rho hqInj hrho
      hrhoPos g hgC1 hg0 with ⟨a, ha, ⟨H⟩⟩
  let Q : ℕ := q (Fin.last d)
  have hqQ : ∀ j, q j ≤ Q := by
    intro j
    exact hq.monotone (Fin.le_last j)
  let A : ℝ → Fin (d + 1) → ℝ := fun tau =>
    rankToRootsCoefficients b Q q g a tau
  have hspan (tau h : ℝ) : ∑ i, A tau i * f i h =
      valuationOriginalCombination Q q g a tau h := by
    exact rankToRootsCombination_eq_valuationOriginalCombination
      f b Q q g a hfactor tau h
  refine ⟨A, H.root, H.root_at, H.scaled_location, ?_⟩
  filter_upwards [H.eventually_scaledRoot_injective hrho,
    H.eventually_valuationOriginalCombination_positive_simpleZeros Q hqQ]
    with tau hinj htau
  refine ⟨hinj, ?_⟩
  intro s
  rcases htau s with ⟨hzero, hpos, dtau, hdtau, hderiv⟩
  refine ⟨?_, hpos, dtau, hdtau, ?_⟩
  · rw [hspan]
    exact hzero
  · apply hderiv.congr_of_eventuallyEq
    exact Eventually.of_forall (fun h => hspan tau h)

end Hilbert16
