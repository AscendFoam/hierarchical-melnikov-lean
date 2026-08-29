import Hilbert16.Spikes.ChebyshevOrbit

set_option autoImplicit false

namespace Hilbert16.Spikes

open Set

/-- Paper Section 3's open monotonicity interval
`(cos ((i+1)π/n), cos (iπ/n))`. -/
noncomputable def chebyshevCellInterval (n i : ℕ) : Set ℝ :=
  Set.Ioo
    (Real.cos (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)))
    (Real.cos ((i : ℝ) * Real.pi / (n : ℝ)))

/-- The open physical rectangle of the cell `(i,j)`. -/
noncomputable def chebyshevCellRectangle (n i j : ℕ) : Set (ℝ × ℝ) :=
  chebyshevCellInterval n i ×ˢ chebyshevCellInterval n j

/-- A fixed energy ceiling that works in every cell and for every `lambda ≥ 1`.
It is chosen smaller than the paper's allowed `1/2` so it also matches the analytic-kernel
convergence range used by W4. -/
noncomputable def chebyshevCommonEnergyUpper : ℝ := 1 / 4

theorem chebyshevCommonEnergyUpper_pos : 0 < chebyshevCommonEnergyUpper := by
  norm_num [chebyshevCommonEnergyUpper]

theorem chebyshevCommonEnergyUpper_lt_half : chebyshevCommonEnergyUpper < 1 / 2 := by
  norm_num [chebyshevCommonEnergyUpper]

/-- The inverse-branch angle lies in the exact `i`-th Chebyshev angle cell, not merely in
`(0,π)`. -/
theorem chebyshevInverseBranch_angle_mem_cell
    {n i : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : |u| < 1) :
    chebyshevRootPhase n i +
        chebyshevCellOrientation i * Real.arcsin u / (n : ℝ) ∈
      Set.Ioo ((i : ℝ) * Real.pi / (n : ℝ))
        (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
  have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have huBounds := abs_lt.mp hu
  have hasinLo : -(Real.pi / 2) < Real.arcsin u :=
    Real.neg_pi_div_two_lt_arcsin.mpr huBounds.1
  have hasinHi : Real.arcsin u < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr huBounds.2
  have heps : -(Real.pi / 2) < chebyshevCellOrientation i * Real.arcsin u ∧
      chebyshevCellOrientation i * Real.arcsin u < Real.pi / 2 := by
    rcases chebyshevCellOrientation_mem i with hneg | hpos
    · rw [hneg]
      constructor <;> nlinarith
    · rw [hpos, one_mul]
      exact ⟨hasinLo, hasinHi⟩
  let theta := chebyshevRootPhase n i +
    chebyshevCellOrientation i * Real.arcsin u / (n : ℝ)
  have hscaled : (n : ℝ) * theta =
      (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / 2 +
        chebyshevCellOrientation i * Real.arcsin u := by
    dsimp [theta, chebyshevRootPhase]
    field_simp [hn]
  have hloScaled : (n : ℝ) * ((i : ℝ) * Real.pi / (n : ℝ)) <
      (n : ℝ) * theta := by
    rw [hscaled]
    field_simp [hn]
    push_cast
    nlinarith [heps.1]
  have hhiScaled : (n : ℝ) * theta <
      (n : ℝ) * (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
    rw [hscaled]
    field_simp [hn]
    push_cast
    nlinarith [heps.2]
  constructor <;> nlinarith [hloScaled, hhiScaled]

/-- Every point of the inverse branch with `|u|<1` belongs to the corresponding open physical
Chebyshev interval. -/
theorem chebyshevInverseBranch_mem_cellInterval
    {n i : ℕ} (hn : n ≠ 0) (hi : i < n) {u : ℝ} (hu : |u| < 1) :
    chebyshevInverseBranch n i u ∈ chebyshevCellInterval n i := by
  have htheta := chebyshevInverseBranch_angle_mem_cell (i := i) hn hu
  have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have hleftNonneg : 0 ≤ (i : ℝ) * Real.pi / (n : ℝ) := by positivity
  have hrightLePi : (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) ≤ Real.pi := by
    have hiSucc : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
    have hiSuccReal : ((i + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hiSucc
    apply (div_le_iff₀ hnPos).2
    nlinarith [mul_le_mul_of_nonneg_right hiSuccReal Real.pi_pos.le]
  have hthetaMem :
      chebyshevRootPhase n i +
          chebyshevCellOrientation i * Real.arcsin u / (n : ℝ) ∈
        Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_trans hleftNonneg htheta.1.le, le_trans htheta.2.le hrightLePi⟩
  have hleftMem : (i : ℝ) * Real.pi / (n : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hleftNonneg, le_trans htheta.1.le hthetaMem.2⟩
  have hrightMem : (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) ∈
      Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_trans hthetaMem.1 htheta.2.le, hrightLePi⟩
  unfold chebyshevCellInterval chebyshevInverseBranch
  constructor
  · exact Real.strictAntiOn_cos hthetaMem hrightMem htheta.2
  · exact Real.strictAntiOn_cos hleftMem hthetaMem htheta.1

/-- Every sufficiently small explicit energy orbit stays strictly inside its designated cell
rectangle. The same upper bound `1/4` works uniformly in `i,j,n` and `lambda ≥ 1`. -/
theorem chebyshevCellOrbit_mem_cellRectangle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhUpper : h < chebyshevCommonEnergyUpper) :
    chebyshevCellOrbit n i j lambda h t ∈ chebyshevCellRectangle n i j := by
  have habs : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq
      (lt_of_lt_of_le zero_lt_one hlambda) hh.le (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;>
        nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2,
          chebyshevCommonEnergyUpper_lt_half]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;>
        nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1,
          chebyshevCommonEnergyUpper_lt_half]
  exact ⟨chebyshevInverseBranch_mem_cellInterval hn hi habs.1,
    chebyshevInverseBranch_mem_cellInterval hn hj habs.2⟩

/-- The two coordinate derivative calculations assemble into the derivative of the full cell
orbit. -/
theorem chebyshevCellOrbit_hasDerivAt
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    HasDerivAt (chebyshevCellOrbit n i j lambda h)
      (chebyshevCellOrbitVelocity n i j lambda h t) t := by
  exact (chebyshevCellOrbit_fst_branch_hasDerivAt (i := i) (j := j)
    hn hlambda hh hhHalf).prodMk
      (chebyshevCellOrbit_snd_branch_hasDerivAt (i := i) (j := j)
        hn hlambda hh hhHalf)

/-- A positive-energy cell orbit is regular: its velocity never vanishes. -/
theorem chebyshevCellOrbitVelocity_ne_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhHalf : h < 1 / 2) :
    chebyshevCellOrbitVelocity n i j lambda h t ≠ 0 := by
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    have henergy := ellipticOrbitUV_energy_eq
      (lt_of_lt_of_le zero_lt_one hlambda) hh.le (t := t)
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  have hdi := chebyshevInverseBranch_deriv_ne_zero hn hi hstrict.1
  have hdj := chebyshevInverseBranch_deriv_ne_zero hn hj hstrict.2
  have hsqrtH : Real.sqrt (2 * h) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hsqrtLambda : Real.sqrt lambda ≠ 0 :=
    (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)).ne'
  intro hzero
  have hfst := congrArg Prod.fst hzero
  have hsnd := congrArg Prod.snd hzero
  simp only [chebyshevCellOrbitVelocity, Prod.fst_zero, Prod.snd_zero,
    ellipticOrbitUVVelocity] at hfst hsnd
  have hsin : Real.sin t = 0 := by
    have hright : -Real.sqrt (2 * h) * Real.sin t = 0 :=
      (mul_eq_zero.mp hfst).resolve_left hdi
    exact (mul_eq_zero.mp hright).resolve_left (neg_ne_zero.mpr hsqrtH)
  have hcos : Real.cos t = 0 := by
    have hright : Real.sqrt (2 * h) / Real.sqrt lambda * Real.cos t = 0 :=
      (mul_eq_zero.mp hsnd).resolve_left hdj
    apply mul_eq_zero.mp hright |>.resolve_left
    exact div_ne_zero hsqrtH hsqrtLambda
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Distinct positive energy parameters give disjoint explicit cell orbits. -/
theorem chebyshevCellOrbit_range_disjoint_of_ne
    {n i j : ℕ} (hn : n ≠ 0) {lambda h₁ h₂ : ℝ}
    (hlambda : 1 ≤ lambda) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (hh₁Half : h₁ ≤ 1 / 2) (hh₂Half : h₂ ≤ 1 / 2) (hne : h₁ ≠ h₂) :
    Disjoint (Set.range (chebyshevCellOrbit n i j lambda h₁))
      (Set.range (chebyshevCellOrbit n i j lambda h₂)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rcases hz₁ with ⟨t₁, rfl⟩
  rcases hz₂ with ⟨t₂, heq⟩
  have hE₁ := chebyshevCellOrbit_energy_eq (i := i) (j := j)
    hn hlambda hh₁ hh₁Half (t := t₁)
  have hE₂ := chebyshevCellOrbit_energy_eq (i := i) (j := j)
    hn hlambda hh₂ hh₂Half (t := t₂)
  rw [heq] at hE₂
  exact hne (hE₁.symm.trans hE₂)

/-- Distinct legal one-dimensional Chebyshev cells are disjoint. -/
theorem chebyshevCellInterval_disjoint
    {n i k : ℕ} (hn : n ≠ 0) (hi : i < n) (hk : k < n) (hik : i ≠ k) :
    Disjoint (chebyshevCellInterval n i) (chebyshevCellInterval n k) := by
  have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have hangleMem : ∀ m : ℕ, m ≤ n →
      (m : ℝ) * Real.pi / (n : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro m hm
    have hmReal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    constructor
    · positivity
    · apply (div_le_iff₀ hnPos).2
      nlinarith [mul_le_mul_of_nonneg_right hmReal Real.pi_pos.le]
  rw [Set.disjoint_left]
  intro x hxi hxk
  unfold chebyshevCellInterval at hxi hxk
  rcases lt_or_gt_of_ne hik with hiklt | hkilt
  · have hiSuccLe : i + 1 ≤ k := Nat.succ_le_iff.mpr hiklt
    have hkLe : k ≤ n := hk.le
    have hcosLe :
        Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ≤
          Real.cos (((i + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
      exact Real.antitoneOn_cos
        (hangleMem (i + 1) (le_trans hiSuccLe hkLe))
        (hangleMem k hkLe)
        (by
          have hiSuccReal : ((i + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast hiSuccLe
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hiSuccReal Real.pi_pos.le) hnPos.le)
    linarith [hxi.1, hxk.2]
  · have hkSuccLe : k + 1 ≤ i := Nat.succ_le_iff.mpr hkilt
    have hiLe : i ≤ n := hi.le
    have hcosLe :
        Real.cos ((i : ℝ) * Real.pi / (n : ℝ)) ≤
          Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
      exact Real.antitoneOn_cos
        (hangleMem (k + 1) (le_trans hkSuccLe hiLe))
        (hangleMem i hiLe)
        (by
          have hkSuccReal : ((k + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by
            exact_mod_cast hkSuccLe
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkSuccReal Real.pi_pos.le) hnPos.le)
    linarith [hxk.1, hxi.2]

/-- Distinct legal two-dimensional cell rectangles are disjoint. -/
theorem chebyshevCellRectangle_disjoint
    {n i j k l : ℕ} (hn : n ≠ 0)
    (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n)
    (hne : (i, j) ≠ (k, l)) :
    Disjoint (chebyshevCellRectangle n i j) (chebyshevCellRectangle n k l) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  by_cases hik : i = k
  · have hjl : j ≠ l := by
      intro hjl
      exact hne (Prod.ext hik hjl)
    exact (Set.disjoint_left.1 (chebyshevCellInterval_disjoint hn hj hl hjl))
      hz₁.2 hz₂.2
  · exact (Set.disjoint_left.1 (chebyshevCellInterval_disjoint hn hi hk hik))
      hz₁.1 hz₂.1

/-- The open common period annulus in one cell, presented as the union of its explicit positive
energy periodic orbits below the common energy ceiling. -/
noncomputable def chebyshevCellPeriodAnnulus
    (n i j : ℕ) (lambda : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ h ∈ Set.Ioo (0 : ℝ) chebyshevCommonEnergyUpper,
    z ∈ Set.range (chebyshevCellOrbit n i j lambda h)}

theorem chebyshevCellOrbit_range_subset_periodAnnulus
    (n i j : ℕ) (lambda : ℝ) {h : ℝ}
    (hh : h ∈ Set.Ioo (0 : ℝ) chebyshevCommonEnergyUpper) :
    Set.range (chebyshevCellOrbit n i j lambda h) ⊆
      chebyshevCellPeriodAnnulus n i j lambda := by
  intro z hz
  exact ⟨h, hh, hz⟩

theorem chebyshevCellPeriodAnnulus_subset_rectangle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    chebyshevCellPeriodAnnulus n i j lambda ⊆ chebyshevCellRectangle n i j := by
  intro z hz
  rcases hz with ⟨h, hh, t, rfl⟩
  exact chebyshevCellOrbit_mem_cellRectangle hn hi hj hlambda hh.1 hh.2

theorem chebyshevCellPeriodAnnulus_energy_mem
    {n i j : ℕ} (hn : n ≠ 0) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {z : ℝ × ℝ} (hz : z ∈ chebyshevCellPeriodAnnulus n i j lambda) :
    chebyshevHamiltonian n lambda z ∈
      Set.Ioo (0 : ℝ) chebyshevCommonEnergyUpper := by
  rcases hz with ⟨h, hh, t, rfl⟩
  rw [chebyshevCellOrbit_energy_eq (i := i) (j := j) hn hlambda hh.1.le
    (le_trans hh.2.le chebyshevCommonEnergyUpper_lt_half.le)]
  exact hh

theorem chebyshevCellPeriodAnnulus_disjoint_of_cell
    {n i j k l : ℕ} (hn : n ≠ 0)
    (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n)
    {lambda : ℝ} (hlambda : 1 ≤ lambda) (hne : (i, j) ≠ (k, l)) :
    Disjoint (chebyshevCellPeriodAnnulus n i j lambda)
      (chebyshevCellPeriodAnnulus n k l lambda) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hzR₁ := chebyshevCellPeriodAnnulus_subset_rectangle hn hi hj hlambda hz₁
  have hzR₂ := chebyshevCellPeriodAnnulus_subset_rectangle hn hk hl hlambda hz₂
  exact (Set.disjoint_left.1
    (chebyshevCellRectangle_disjoint hn hi hj hk hl hne)) hzR₁ hzR₂

/-- A compact closed subannulus, parameterized by an energy band and one full angular period. -/
noncomputable def chebyshevCellCompactSubannulus
    (n i j : ℕ) (lambda hMin hMax : ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => chebyshevCellOrbit n i j lambda p.1 p.2) ''
    (Set.Icc hMin hMax ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))

theorem continuous_chebyshevCellOrbit_energy_time
    (n i j : ℕ) (lambda : ℝ) :
    Continuous (fun p : ℝ × ℝ => chebyshevCellOrbit n i j lambda p.1 p.2) := by
  unfold chebyshevCellOrbit chebyshevCellInverseMap ellipticOrbitUV
    chebyshevInverseBranch
  fun_prop

theorem isCompact_chebyshevCellCompactSubannulus
    (n i j : ℕ) (lambda hMin hMax : ℝ) :
    IsCompact (chebyshevCellCompactSubannulus n i j lambda hMin hMax) := by
  exact (isCompact_Icc.prod isCompact_Icc).image
    (continuous_chebyshevCellOrbit_energy_time n i j lambda)

theorem chebyshevCellCompactSubannulus_nonempty
    (n i j : ℕ) (lambda : ℝ) {hMin hMax : ℝ} (hband : hMin ≤ hMax) :
    (chebyshevCellCompactSubannulus n i j lambda hMin hMax).Nonempty := by
  refine ⟨chebyshevCellOrbit n i j lambda hMin 0, ?_⟩
  exact ⟨(hMin, 0), ⟨⟨le_rfl, hband⟩,
    ⟨le_rfl, by nlinarith [Real.pi_pos]⟩⟩, rfl⟩

theorem chebyshevCellCompactSubannulus_subset_rectangle
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda hMin hMax : ℝ} (hlambda : 1 ≤ lambda) (hMinPos : 0 < hMin)
    (hMaxUpper : hMax < chebyshevCommonEnergyUpper) :
    chebyshevCellCompactSubannulus n i j lambda hMin hMax ⊆
      chebyshevCellRectangle n i j := by
  intro z hz
  rcases hz with ⟨⟨h, t⟩, ⟨hh, ht⟩, rfl⟩
  exact chebyshevCellOrbit_mem_cellRectangle hn hi hj hlambda
    (lt_of_lt_of_le hMinPos hh.1) (lt_of_le_of_lt hh.2 hMaxUpper)

theorem chebyshevCellCompactSubannulus_subset_periodAnnulus
    (n i j : ℕ) (lambda : ℝ) {hMin hMax : ℝ}
    (hMinPos : 0 < hMin) (hMaxUpper : hMax < chebyshevCommonEnergyUpper) :
    chebyshevCellCompactSubannulus n i j lambda hMin hMax ⊆
      chebyshevCellPeriodAnnulus n i j lambda := by
  intro z hz
  rcases hz with ⟨⟨h, t⟩, ⟨hh, ht⟩, rfl⟩
  exact ⟨h, ⟨lt_of_lt_of_le hMinPos hh.1, lt_of_le_of_lt hh.2 hMaxUpper⟩,
    ⟨t, rfl⟩⟩

theorem chebyshevCellCompactSubannulus_energy_mem
    {n i j : ℕ} (hn : n ≠ 0) {lambda hMin hMax : ℝ}
    (hlambda : 1 ≤ lambda) (hMinNonneg : 0 ≤ hMin)
    (hMaxHalf : hMax ≤ 1 / 2) {z : ℝ × ℝ}
    (hz : z ∈ chebyshevCellCompactSubannulus n i j lambda hMin hMax) :
    chebyshevHamiltonian n lambda z ∈ Set.Icc hMin hMax := by
  rcases hz with ⟨⟨h, t⟩, ⟨hh, ht⟩, rfl⟩
  rw [chebyshevCellOrbit_energy_eq (i := i) (j := j) hn hlambda
    (le_trans hMinNonneg hh.1) (le_trans hh.2 hMaxHalf)]
  exact hh

/-- Closed energy bands in the same cell are disjoint whenever their energy intervals are
strictly separated. -/
theorem chebyshevCellCompactSubannulus_disjoint_of_energy
    {n i j : ℕ} (hn : n ≠ 0) {lambda a b c d : ℝ}
    (hlambda : 1 ≤ lambda) (ha : 0 ≤ a) (hd : d ≤ 1 / 2) (hsep : b < c) :
    Disjoint (chebyshevCellCompactSubannulus n i j lambda a b)
      (chebyshevCellCompactSubannulus n i j lambda c d) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rcases hz₁ with ⟨⟨h₁, t₁⟩, ⟨hh₁, ht₁⟩, rfl⟩
  rcases hz₂ with ⟨⟨h₂, t₂⟩, ⟨hh₂, ht₂⟩, heq⟩
  have hh₁Nonneg : 0 ≤ h₁ := le_trans ha hh₁.1
  have hh₂Nonneg : 0 ≤ h₂ := by linarith [hh₁.2, hsep, hh₂.1]
  have hh₁Half : h₁ ≤ 1 / 2 := by linarith [hh₁.2, hsep, hh₂.1, hh₂.2, hd]
  have hh₂Half : h₂ ≤ 1 / 2 := le_trans hh₂.2 hd
  have hE₁ := chebyshevCellOrbit_energy_eq (i := i) (j := j)
    hn hlambda hh₁Nonneg hh₁Half (t := t₁)
  have hE₂ := chebyshevCellOrbit_energy_eq (i := i) (j := j)
    hn hlambda hh₂Nonneg hh₂Half (t := t₂)
  change chebyshevCellOrbit n i j lambda h₂ t₂ =
    chebyshevCellOrbit n i j lambda h₁ t₁ at heq
  rw [heq] at hE₂
  linarith [hE₁, hE₂, hh₁.2, hsep, hh₂.1]

/-- Compact subannuli in distinct legal cells are disjoint, uniformly over their energy bands. -/
theorem chebyshevCellCompactSubannulus_disjoint_of_cell
    {n i j k l : ℕ} (hn : n ≠ 0)
    (hi : i < n) (hj : j < n) (hk : k < n) (hl : l < n)
    {lambda a b c d : ℝ} (hlambda : 1 ≤ lambda)
    (ha : 0 < a) (hb : b < chebyshevCommonEnergyUpper)
    (hc : 0 < c) (hd : d < chebyshevCommonEnergyUpper)
    (hne : (i, j) ≠ (k, l)) :
    Disjoint (chebyshevCellCompactSubannulus n i j lambda a b)
      (chebyshevCellCompactSubannulus n k l lambda c d) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hzR₁ := chebyshevCellCompactSubannulus_subset_rectangle
    hn hi hj hlambda ha hb hz₁
  have hzR₂ := chebyshevCellCompactSubannulus_subset_rectangle
    hn hk hl hlambda hc hd hz₂
  exact (Set.disjoint_left.1
    (chebyshevCellRectangle_disjoint hn hi hj hk hl hne)) hzR₁ hzR₂

end Hilbert16.Spikes
