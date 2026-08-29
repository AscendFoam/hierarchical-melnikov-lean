import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Iterate
import Hilbert16.Dynamics.NormalizedDisplacement

set_option autoImplicit false

namespace Hilbert16

open Filter Set
open scoped Topology

/-- If all iterates of a continuous order-preserving scalar map stay in a
compact interval, they converge to a fixed point.  This replaces an
unnecessary assumption that a nearby periodic carrier returns to its first
section point after exactly one chosen return-time branch. -/
theorem exists_fixedPoint_limit_of_iterates_mem_Icc
    {f : ℝ → ℝ} {a b x : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hmono : MonotoneOn f (Set.Icc a b))
    (hiter : ∀ k : ℕ, (f^[k]) x ∈ Set.Icc a b) :
    ∃ l ∈ Set.Icc a b, f l = l ∧
      Tendsto (fun k : ℕ => (f^[k]) x) atTop (𝓝 l) := by
  let s : ℕ → ℝ := fun k => (f^[k]) x
  have hs (k : ℕ) : s k ∈ Set.Icc a b := hiter k
  have hstep (k : ℕ) : s (k + 1) = f (s k) := by
    simpa [s, Nat.succ_eq_add_one] using Function.iterate_succ_apply' f k x
  rcases le_total (s 0) (s 1) with hle | hge
  · have hmon : Monotone s := by
      apply monotone_nat_of_le_succ
      intro k
      induction k with
      | zero => exact hle
      | succ k ih =>
          calc
            s k.succ = f (s k) := by simpa using hstep k
            _ ≤ f (s (k + 1)) := hmono (hs k) (hs (k + 1)) ih
            _ = s (k.succ + 1) := by
              simpa [Nat.succ_eq_add_one] using (hstep (k + 1)).symm
    have hbdd : BddAbove (Set.range s) := by
      refine ⟨b, ?_⟩
      rintro y ⟨k, rfl⟩
      exact (hs k).2
    rcases Real.tendsto_of_bddAbove_monotone hbdd hmon with ⟨l, hl⟩
    have hlmem : l ∈ Set.Icc a b := by
      exact isClosed_Icc.mem_of_tendsto hl (Eventually.of_forall hs)
    have hlWithin : Tendsto s atTop (nhdsWithin l (Set.Icc a b)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hl, Eventually.of_forall hs⟩
    have hfLim : Tendsto (fun k => f (s k)) atTop (𝓝 (f l)) :=
      (hcont l hlmem).tendsto.comp hlWithin
    have hshift : Tendsto (fun k => s (k + 1)) atTop (𝓝 l) :=
      hl.comp (tendsto_add_atTop_nat 1)
    have hsame : (fun k => f (s k)) = fun k => s (k + 1) := by
      funext k
      exact (hstep k).symm
    have hfl : f l = l := by
      apply tendsto_nhds_unique hfLim
      rw [hsame]
      exact hshift
    exact ⟨l, hlmem, hfl, hl⟩
  · have hanti : Antitone s := by
      apply antitone_nat_of_succ_le
      intro k
      induction k with
      | zero => exact hge
      | succ k ih =>
          calc
            s (k.succ + 1) = f (s (k + 1)) := by
              simpa [Nat.succ_eq_add_one] using hstep (k + 1)
            _ ≤ f (s k) := hmono (hs (k + 1)) (hs k) ih
            _ = s k.succ := by simpa using (hstep k).symm
    have hbdd : BddBelow (Set.range s) := by
      refine ⟨a, ?_⟩
      rintro y ⟨k, rfl⟩
      exact (hs k).1
    rcases Real.tendsto_of_bddBelow_antitone hbdd hanti with ⟨l, hl⟩
    have hlmem : l ∈ Set.Icc a b := by
      exact isClosed_Icc.mem_of_tendsto hl (Eventually.of_forall hs)
    have hlWithin : Tendsto s atTop (nhdsWithin l (Set.Icc a b)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hl, Eventually.of_forall hs⟩
    have hfLim : Tendsto (fun k => f (s k)) atTop (𝓝 (f l)) :=
      (hcont l hlmem).tendsto.comp hlWithin
    have hshift : Tendsto (fun k => s (k + 1)) atTop (𝓝 l) :=
      hl.comp (tendsto_add_atTop_nat 1)
    have hsame : (fun k => f (s k)) = fun k => s (k + 1) := by
      funext k
      exact (hstep k).symm
    have hfl : f l = l := by
      apply tendsto_nhds_unique hfLim
      rw [hsame]
      exact hshift
    exact ⟨l, hlmem, hfl, hl⟩

/-- A jointly `C¹` normalized displacement gives, on one fixed compact
energy interval, an order-preserving normalized return map for every
sufficiently small parameter. -/
theorem exists_Icc_eventually_monotone_normalizedReturnMap
    {D : ℝ × ℝ → ℝ} {h : ℝ}
    (hD : ContDiffAt ℝ 1 D (0, h)) :
    ∃ a b : ℝ, a < h ∧ h < b ∧
      ∀ᶠ mu in 𝓝 (0 : ℝ),
        ContinuousOn (normalizedReturnMap D mu) (Set.Icc a b) ∧
          MonotoneOn (normalizedReturnMap D mu) (Set.Icc a b) := by
  have hlocal : ∀ᶠ z in 𝓝 ((0 : ℝ), h), ContDiffAt ℝ 1 D z :=
    hD.eventually (by simp)
  rcases mem_nhds_prod_iff.mp hlocal with ⟨A, hA, B, hB, hAB⟩
  rcases Metric.mem_nhds_iff.mp hA with ⟨epsMu, hepsMu, hballMu⟩
  rcases Metric.mem_nhds_iff.mp hB with ⟨epsE, hepsE, hballE⟩
  let deltaMu : ℝ := epsMu / 2
  let deltaE : ℝ := epsE / 2
  let M : Set ℝ := Set.Icc (-deltaMu) deltaMu
  let J : Set ℝ := Set.Icc (h - deltaE) (h + deltaE)
  have hdeltaMu : 0 < deltaMu := by dsimp [deltaMu]; positivity
  have hdeltaE : 0 < deltaE := by dsimp [deltaE]; positivity
  have hMsub : M ⊆ A := by
    intro mu hmu
    apply hballMu
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have habs : |mu| ≤ deltaMu := abs_le.mpr hmu
    exact habs.trans_lt (by dsimp [deltaMu]; linarith)
  have hJsub : J ⊆ B := by
    intro e he
    apply hballE
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |e - h| ≤ deltaE := by
      rw [abs_le]
      have heL : h - deltaE ≤ e := by
        simpa [J] using he.1
      have heU : e ≤ h + deltaE := by
        simpa [J] using he.2
      exact ⟨by linarith, by linarith⟩
    exact habs.trans_lt (by dsimp [deltaE]; linarith)
  have hC1 : ContDiffOn ℝ 1 D (M ×ˢ J) := by
    intro z hz
    have hzlocal := hAB ⟨hMsub hz.1, hJsub hz.2⟩
    change ContDiffAt ℝ 1 D z at hzlocal
    exact hzlocal.contDiffWithinAt
  obtain ⟨K, hK⟩ := hC1.exists_lipschitzOnWith
    (by norm_num) ((convex_Icc _ _).prod (convex_Icc _ _))
      (isCompact_Icc.prod isCompact_Icc)
  have hmuSmall : ∀ᶠ mu in 𝓝 (0 : ℝ),
      mu ∈ Set.Ioo (-deltaMu) deltaMu ∧
        |mu| * (K : ℝ) < 1 := by
    have hinterval : ∀ᶠ mu in 𝓝 (0 : ℝ),
        mu ∈ Set.Ioo (-deltaMu) deltaMu :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have htend : Tendsto (fun mu : ℝ => |mu| * (K : ℝ))
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun mu : ℝ => |mu| * (K : ℝ)) :=
        _root_.continuous_abs.mul continuous_const
      simpa using hc.tendsto 0
    exact hinterval.and (htend.eventually (eventually_lt_nhds zero_lt_one))
  refine ⟨h - deltaE, h + deltaE, by linarith, by linarith, ?_⟩
  filter_upwards [hmuSmall] with mu hmu
  have hmuM : mu ∈ M := by
    exact ⟨hmu.1.1.le, hmu.1.2.le⟩
  have hsliceLip : LipschitzOnWith K (fun e => D (mu, e)) J := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_prod_same_left] using
      hK.dist_le_mul (mu, x) ⟨hmuM, hx⟩ (mu, y) ⟨hmuM, hy⟩
  have hcont : ContinuousOn (normalizedReturnMap D mu) J := by
    unfold normalizedReturnMap
    exact continuousOn_id.add (continuousOn_const.mul hsliceLip.continuousOn)
  refine ⟨hcont, ?_⟩
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxylt
  · exact le_rfl
  · have hdist := hsliceLip.dist_le_mul y hy x hx
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_pos (sub_pos.mpr hxylt)] at hdist
    have hpert : |mu * (D (mu, y) - D (mu, x))| < y - x := by
      rw [abs_mul]
      calc
        |mu| * |D (mu, y) - D (mu, x)| ≤
            |mu| * ((K : ℝ) * (y - x)) :=
          mul_le_mul_of_nonneg_left hdist (abs_nonneg mu)
        _ = (|mu| * (K : ℝ)) * (y - x) := by ring
        _ < 1 * (y - x) :=
          mul_lt_mul_of_pos_right hmu.2 (sub_pos.mpr hxylt)
        _ = y - x := one_mul _
    have hpertLower := (abs_lt.mp hpert).1
    unfold normalizedReturnMap
    nlinarith

end Hilbert16
