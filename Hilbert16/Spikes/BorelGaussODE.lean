import Hilbert16.Spikes.BorelGaussAsymptotics

open Nat Polynomial MeasureTheory Filter Set

namespace Hilbert16.Spikes

noncomputable def ordinaryHypergeometricD1 (a b c z : ℝ) : ℝ :=
  ((ordinaryHypergeometricSeries ℝ a b c).derivSeries.sum z) 1

noncomputable def ordinaryHypergeometricD2 (a b c z : ℝ) : ℝ :=
  (((ordinaryHypergeometricSeries ℝ a b c).derivSeries.derivSeries.sum z) 1) 1

theorem ordinaryHypergeometric_hasDerivAt_D1 {a b c z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    HasDerivAt (ordinaryHypergeometric a b c)
      (ordinaryHypergeometricD1 a b c z) z := by
  exact (ordinaryHypergeometricSeries ℝ a b c).hasFDerivAt_sum hz |>.hasDerivAt

theorem ordinaryHypergeometricD1_hasDerivAt_D2 {a b c z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    HasDerivAt (ordinaryHypergeometricD1 a b c)
      (ordinaryHypergeometricD2 a b c z) z := by
  let p := ordinaryHypergeometricSeries ℝ a b c
  have hz' : ‖z‖ₑ < p.derivSeries.radius :=
    lt_of_lt_of_le hz p.radius_le_radius_derivSeries
  have h := p.derivSeries.hasFDerivAt_sum hz'
  have happ := h.clm_apply (hasFDerivAt_const (x := z) (c := (1 : ℝ)))
  change HasDerivAt (fun y : ℝ => (p.derivSeries.sum y) 1)
    (((p.derivSeries.derivSeries.sum z) 1) 1) z
  apply happ.hasDerivAt.congr_deriv
  simp

theorem ordinaryHypergeometricCoefficient_recurrence {a b c : ℝ}
    (hc : 0 < c) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + c) *
        ordinaryHypergeometricCoefficient a b c (n + 1) =
      ((n : ℝ) + a) * ((n : ℝ) + b) *
        ordinaryHypergeometricCoefficient a b c n := by
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfac1 : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hpc : (ascPochhammer ℝ n).eval c ≠ 0 :=
    (ascPochhammer_pos n c hc).ne'
  have hcn : c + n ≠ 0 := by positivity
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, ascPochhammer_succ_eval]
  field_simp [hfac, hfac1, hpc, hcn]
  ring

theorem ordinaryHypergeometric_hasSum_coeff {a b c z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n * z ^ n)
      (ordinaryHypergeometric a b c z) := by
  have h := (ordinaryHypergeometricSeries ℝ a b c).hasSum
    (show z ∈ Metric.eball (0 : ℝ) (ordinaryHypergeometricSeries ℝ a b c).radius by
      simpa [Metric.mem_eball] using hz)
  simpa [ordinaryHypergeometric, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using h

theorem ordinaryHypergeometricD1_hasSum_coeff {a b c z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ordinaryHypergeometricCoefficient a b c (n + 1) * z ^ n)
      (ordinaryHypergeometricD1 a b c z) := by
  let p := ordinaryHypergeometricSeries ℝ a b c
  have hz' : ‖z‖ₑ < p.derivSeries.radius :=
    lt_of_lt_of_le hz p.radius_le_radius_derivSeries
  have h := p.derivSeries.hasSum
    (show z ∈ Metric.eball (0 : ℝ) p.derivSeries.radius by
      simpa [Metric.mem_eball] using hz')
  have happ := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum h
  change HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ordinaryHypergeometricCoefficient a b c (n + 1) * z ^ n)
    ((p.derivSeries.sum z) 1)
  refine happ.congr_fun (fun n => ?_)
  simp [p, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
  ring

theorem ordinaryHypergeometricD2_hasSum_coeff {a b c z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
      ordinaryHypergeometricCoefficient a b c (n + 2) * z ^ n)
      (ordinaryHypergeometricD2 a b c z) := by
  let p := ordinaryHypergeometricSeries ℝ a b c
  have hz' : ‖z‖ₑ < p.derivSeries.derivSeries.radius :=
    lt_of_lt_of_le hz
      (p.radius_le_radius_derivSeries.trans p.derivSeries.radius_le_radius_derivSeries)
  have h := p.derivSeries.derivSeries.hasSum
    (show z ∈ Metric.eball (0 : ℝ) p.derivSeries.derivSeries.radius by
      simpa [Metric.mem_eball] using hz')
  have happ1 := (ContinuousLinearMap.apply ℝ (ℝ →L[ℝ] ℝ) (1 : ℝ)).hasSum h
  have happ2 := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum happ1
  change HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
      ordinaryHypergeometricCoefficient a b c (n + 2) * z ^ n)
    (((p.derivSeries.derivSeries.sum z) 1) 1)
  refine happ2.congr_fun (fun n => ?_)
  simp [p, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
  ring

theorem ordinaryHypergeometric_ode {a b c z : ℝ} (hc : 0 < c)
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ a b c).radius) :
    z * (1 - z) * ordinaryHypergeometricD2 a b c z +
        (c - (a + b + 1) * z) * ordinaryHypergeometricD1 a b c z -
      a * b * ordinaryHypergeometric a b c z = 0 := by
  let C : ℕ → ℝ := ordinaryHypergeometricCoefficient a b c
  let D1 := ordinaryHypergeometricD1 a b c z
  let D2 := ordinaryHypergeometricD2 a b c z
  let F := ordinaryHypergeometric a b c z
  have hF : HasSum (fun n : ℕ => C n * z ^ n) F := by
    simpa [C, F] using ordinaryHypergeometric_hasSum_coeff hz
  have hD1 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * C (n + 1) * z ^ n) D1 := by
    simpa [C, D1] using ordinaryHypergeometricD1_hasSum_coeff hz
  have hD2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
      C (n + 2) * z ^ n) D2 := by
    simpa [C, D2] using ordinaryHypergeometricD2_hasSum_coeff hz
  let S : ℕ → ℝ
    | 0 => 0
    | n + 1 => ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * C (n + 2) * z ^ (n + 1)
  have hStail : HasSum (fun n : ℕ => S (n + 1)) (z * D2) := by
    refine (hD2.mul_left z).congr_fun (fun n => ?_)
    simp only [S, pow_succ]
    push_cast
    ring
  have hS : HasSum S (z * D2) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [S] using hStail
  have hL0 := hS.add (hD1.mul_left c)
  have hL : HasSum
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + c) * C (n + 1) * z ^ n)
      (z * D2 + c * D1) := by
    refine hL0.congr_fun (fun n => ?_)
    cases n with
    | zero => simp [S]
    | succ n =>
      simp only [S]
      push_cast
      ring
  let U : ℕ → ℝ
    | 0 => 0
    | n + 1 => (a + b + 1) * ((n + 1 : ℕ) : ℝ) * C (n + 1) * z ^ (n + 1)
  have hUtail : HasSum (fun n : ℕ => U (n + 1)) ((a + b + 1) * z * D1) := by
    refine (hD1.mul_left ((a + b + 1) * z)).congr_fun (fun n => ?_)
    simp only [U, pow_succ]
    ring
  have hU : HasSum U ((a + b + 1) * z * D1) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [U] using hUtail
  let T : ℕ → ℝ
    | 0 => 0
    | 1 => 0
    | n + 2 => ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) * C (n + 2) * z ^ (n + 2)
  have hTtail : HasSum (fun n : ℕ => T (n + 2)) (z ^ 2 * D2) := by
    refine (hD2.mul_left (z ^ 2)).congr_fun (fun n => ?_)
    simp only [T, pow_add]
    ring
  have hT : HasSum T (z ^ 2 * D2) := by
    apply (hasSum_nat_add_iff' 2).mp
    rw [show ∑ x ∈ Finset.range 2, T x = 0 by norm_num [T], sub_zero]
    exact hTtail
  have hR0 := (hT.add hU).add (hF.mul_left (a * b))
  have hR : HasSum
      (fun n : ℕ => ((n : ℝ) + a) * ((n : ℝ) + b) * C n * z ^ n)
      (z ^ 2 * D2 + (a + b + 1) * z * D1 + a * b * F) := by
    refine hR0.congr_fun (fun n => ?_)
    cases n with
    | zero => simp [T, U, C, ordinaryHypergeometricCoefficient]
    | succ n =>
      cases n with
      | zero =>
        simp only [T, U, Nat.cast_one, pow_one]
        ring
      | succ n =>
        simp only [T, U]
        push_cast
        ring
  have hterm : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + c) * C (n + 1) * z ^ n =
        ((n : ℝ) + a) * ((n : ℝ) + b) * C n * z ^ n := by
    intro n
    have hrec := ordinaryHypergeometricCoefficient_recurrence (a := a) (b := b) hc n
    dsimp [C]
    calc
      ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + c) *
          ordinaryHypergeometricCoefficient a b c (n + 1) * z ^ n =
        ((((n + 1 : ℕ) : ℝ) * ((n : ℝ) + c) *
          ordinaryHypergeometricCoefficient a b c (n + 1)) * z ^ n) := by ring
      _ = ((((n : ℝ) + a) * ((n : ℝ) + b) *
          ordinaryHypergeometricCoefficient a b c n) * z ^ n) := by rw [hrec]
      _ = ((n : ℝ) + a) * ((n : ℝ) + b) *
          ordinaryHypergeometricCoefficient a b c n * z ^ n := by ring
  have heq : z * D2 + c * D1 =
      z ^ 2 * D2 + (a + b + 1) * z * D1 + a * b * F :=
    hL.unique (hR.congr_fun hterm)
  dsimp [D1, D2, F] at heq ⊢
  nlinarith

/-! ### Uniform Frobenius branch at negative infinity -/

noncomputable def gaussInfinityPhi (r z : ℝ) : ℝ :=
  ordinaryHypergeometric (-r) (-r) (1 - 2 * r) z

noncomputable def gaussInfinityPhiD1 (r z : ℝ) : ℝ :=
  ordinaryHypergeometricD1 (-r) (-r) (1 - 2 * r) z

noncomputable def gaussInfinityPhiD2 (r z : ℝ) : ℝ :=
  ordinaryHypergeometricD2 (-r) (-r) (1 - 2 * r) z

noncomputable def gaussInfinityBranch (r x : ℝ) : ℝ :=
  x ^ r * gaussInfinityPhi r (-(x⁻¹))

noncomputable def gaussInfinityBranchD1 (r x : ℝ) : ℝ :=
  r * x ^ (r - 1) * gaussInfinityPhi r (-(x⁻¹)) +
    x ^ (r - 2) * gaussInfinityPhiD1 r (-(x⁻¹))

noncomputable def gaussInfinityBranchD2 (r x : ℝ) : ℝ :=
  r * (r - 1) * x ^ (r - 2) * gaussInfinityPhi r (-(x⁻¹)) +
    2 * (r - 1) * x ^ (r - 3) * gaussInfinityPhiD1 r (-(x⁻¹)) +
    x ^ (r - 4) * gaussInfinityPhiD2 r (-(x⁻¹))

theorem gaussInfinityPhi_hasDerivAt {r z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    HasDerivAt (gaussInfinityPhi r) (gaussInfinityPhiD1 r z) z := by
  exact ordinaryHypergeometric_hasDerivAt_D1 hz

theorem gaussInfinityPhiD1_hasDerivAt {r z : ℝ}
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    HasDerivAt (gaussInfinityPhiD1 r) (gaussInfinityPhiD2 r z) z := by
  exact ordinaryHypergeometricD1_hasDerivAt_D2 hz

private theorem rpow_mul_inv_sq {q x : ℝ} (hx : 0 < x) :
    x ^ q * (x ^ 2)⁻¹ = x ^ (q - 2) := by
  rw [Real.rpow_sub hx q 2]
  field_simp [hx.ne']
  exact Real.rpow_natCast x 2

theorem gaussInfinityBranch_hasDerivAt {r x : ℝ} (hx : 0 < x)
    (hz : ‖-(x⁻¹)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    HasDerivAt (gaussInfinityBranch r) (gaussInfinityBranchD1 r x) x := by
  have hpow := Real.hasDerivAt_rpow_const (x := x) (p := r) (.inl hx.ne')
  have hinv := hasDerivAt_inv hx.ne'
  have hzmap : HasDerivAt (- fun y : ℝ => y⁻¹) ((x ^ 2)⁻¹) x := by
    simpa only [neg_neg] using hinv.neg
  have hphi := (gaussInfinityPhi_hasDerivAt hz).comp x hzmap
  unfold gaussInfinityBranch gaussInfinityBranchD1
  apply (hpow.mul hphi).congr_deriv
  have hpowrel := rpow_mul_inv_sq (q := r) hx
  rw [Function.comp_apply]
  calc
    r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
        x ^ r * (gaussInfinityPhiD1 r (-x⁻¹) * (x ^ 2)⁻¹) =
      r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
        (x ^ r * (x ^ 2)⁻¹) * gaussInfinityPhiD1 r (-x⁻¹) := by ring
    _ = r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
        x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹) := by rw [hpowrel]

theorem gaussInfinityBranchD1_hasDerivAt {r x : ℝ} (hx : 0 < x)
    (hz : ‖-(x⁻¹)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    HasDerivAt (gaussInfinityBranchD1 r) (gaussInfinityBranchD2 r x) x := by
  have hpow1 := Real.hasDerivAt_rpow_const (x := x) (p := r - 1) (.inl hx.ne')
  have hpow2 := Real.hasDerivAt_rpow_const (x := x) (p := r - 2) (.inl hx.ne')
  have hinv := hasDerivAt_inv hx.ne'
  have hzmap : HasDerivAt (- fun y : ℝ => y⁻¹) ((x ^ 2)⁻¹) x := by
    simpa only [neg_neg] using hinv.neg
  have hphi := (gaussInfinityPhi_hasDerivAt hz).comp x hzmap
  have hphi1 := (gaussInfinityPhiD1_hasDerivAt hz).comp x hzmap
  have hraw := ((hasDerivAt_const x r).mul (hpow1.mul hphi)).add (hpow2.mul hphi1)
  have hfun :
      (fun y : ℝ =>
        r * y ^ (r - 1) * gaussInfinityPhi r (-(y⁻¹)) +
          y ^ (r - 2) * gaussInfinityPhiD1 r (-(y⁻¹))) =ᶠ[nhds x]
      ((fun _ : ℝ => r) *
          ((fun y : ℝ => y ^ (r - 1)) *
            (gaussInfinityPhi r ∘ (- fun y : ℝ => y⁻¹))) +
        (fun y : ℝ => y ^ (r - 2)) *
          (gaussInfinityPhiD1 r ∘ (- fun y : ℝ => y⁻¹))) := by
    filter_upwards with y
    simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Pi.neg_apply]
    ring
  have hraw' := hraw.congr_of_eventuallyEq hfun
  unfold gaussInfinityBranchD1 gaussInfinityBranchD2
  apply hraw'.congr_deriv
  simp only [zero_mul, zero_add, Function.comp_apply]
  have hp1 := rpow_mul_inv_sq (q := r - 1) hx
  have hp2 := rpow_mul_inv_sq (q := r - 2) hx
  have he1 : r - 1 - 2 = r - 3 := by ring
  have he2 : r - 2 - 2 = r - 4 := by ring
  rw [he1] at hp1
  rw [he2] at hp2
  have hepow1 : r - 1 - 1 = r - 2 := by ring
  have hepow2 : r - 2 - 1 = r - 3 := by ring
  calc
    r * ((r - 1) * x ^ (r - 1 - 1) * gaussInfinityPhi r (-x⁻¹) +
          x ^ (r - 1) * (gaussInfinityPhiD1 r (-x⁻¹) * (x ^ 2)⁻¹)) +
        ((r - 2) * x ^ (r - 2 - 1) * gaussInfinityPhiD1 r (-x⁻¹) +
          x ^ (r - 2) * (gaussInfinityPhiD2 r (-x⁻¹) * (x ^ 2)⁻¹)) =
      r * (r - 1) * x ^ (r - 2) * gaussInfinityPhi r (-x⁻¹) +
        (r * (x ^ (r - 1) * (x ^ 2)⁻¹) +
          (r - 2) * x ^ (r - 3)) * gaussInfinityPhiD1 r (-x⁻¹) +
        (x ^ (r - 2) * (x ^ 2)⁻¹) * gaussInfinityPhiD2 r (-x⁻¹) := by
      rw [hepow1, hepow2]
      ring
    _ = r * (r - 1) * x ^ (r - 2) * gaussInfinityPhi r (-x⁻¹) +
        2 * (r - 1) * x ^ (r - 3) * gaussInfinityPhiD1 r (-x⁻¹) +
        x ^ (r - 4) * gaussInfinityPhiD2 r (-x⁻¹) := by
      rw [hp1, hp2]
      ring

theorem gaussInfinityPhi_ode {r z : ℝ} (hc : 0 < 1 - 2 * r)
    (hz : ‖z‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    z * (1 - z) * gaussInfinityPhiD2 r z +
        (1 - 2 * r) * (1 - z) * gaussInfinityPhiD1 r z -
      r ^ 2 * gaussInfinityPhi r z = 0 := by
  have h := ordinaryHypergeometric_ode (a := -r) (b := -r) (c := 1 - 2 * r) hc hz
  dsimp [gaussInfinityPhi, gaussInfinityPhiD1, gaussInfinityPhiD2] at h ⊢
  nlinarith

private theorem rpow_mul_self {q x : ℝ} (hx : 0 < x) :
    x ^ q * x = x ^ (q + 1) := by
  exact (Real.rpow_add_one hx.ne' q).symm

private theorem rpow_mul_sq {q x : ℝ} (hx : 0 < x) :
    x ^ q * x ^ 2 = x ^ (q + 2) := by
  calc
    x ^ q * x ^ 2 = x ^ q * x ^ (2 : ℝ) :=
      congrArg (fun y : ℝ => x ^ q * y) (Real.rpow_natCast x 2).symm
    _ = x ^ (q + 2) := (Real.rpow_add hx q 2).symm

theorem gaussInfinityBranch_ode {r x : ℝ} (hx : 0 < x) (hc : 0 < 1 - 2 * r)
    (hz : ‖-(x⁻¹)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    x * (1 + x) * gaussInfinityBranchD2 r x +
        (1 + x) * gaussInfinityBranchD1 r x -
      r ^ 2 * gaussInfinityBranch r x = 0 := by
  have hphi := gaussInfinityPhi_ode (r := r) (z := -(x⁻¹)) hc hz
  have hself : x ^ (r - 3) * x = x ^ (r - 2) := by
    calc
      x ^ (r - 3) * x = x ^ (r - 3 + 1) := rpow_mul_self hx
      _ = x ^ (r - 2) := by congr 1 <;> ring
  have hsq : x ^ (r - 3) * x ^ 2 = x ^ (r - 1) := by
    calc
      x ^ (r - 3) * x ^ 2 = x ^ (r - 3 + 2) := rpow_mul_sq hx
      _ = x ^ (r - 1) := by congr 1 <;> ring
  have hmul2 : x * x ^ (r - 2) = x ^ (r - 1) := by
    rw [mul_comm, rpow_mul_self hx]
    congr 1 <;> ring
  have hmul3 : x * x ^ (r - 3) = x ^ (r - 2) := by
    rw [mul_comm, rpow_mul_self hx]
    congr 1 <;> ring
  have hmul4 : x * x ^ (r - 4) = x ^ (r - 3) := by
    rw [mul_comm, rpow_mul_self hx]
    congr 1 <;> ring
  unfold gaussInfinityBranch gaussInfinityBranchD1 gaussInfinityBranchD2
  have htarget :
      x * (1 + x) *
          (r * (r - 1) * x ^ (r - 2) * gaussInfinityPhi r (-x⁻¹) +
            2 * (r - 1) * x ^ (r - 3) * gaussInfinityPhiD1 r (-x⁻¹) +
            x ^ (r - 4) * gaussInfinityPhiD2 r (-x⁻¹)) +
        (1 + x) *
          (r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
            x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹)) -
        r ^ 2 * (x ^ r * gaussInfinityPhi r (-x⁻¹)) =
      r ^ 2 * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
        (2 * r - 1) * (1 + x) * x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹) +
        (1 + x) * x ^ (r - 3) * gaussInfinityPhiD2 r (-x⁻¹) := by
    have hmul1 : x * x ^ (r - 1) = x ^ r := by
      rw [mul_comm, rpow_mul_self hx]
      congr 1 <;> ring
    calc
      x * (1 + x) *
            (r * (r - 1) * x ^ (r - 2) * gaussInfinityPhi r (-x⁻¹) +
              2 * (r - 1) * x ^ (r - 3) * gaussInfinityPhiD1 r (-x⁻¹) +
              x ^ (r - 4) * gaussInfinityPhiD2 r (-x⁻¹)) +
          (1 + x) *
            (r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
              x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹)) -
          r ^ 2 * (x ^ r * gaussInfinityPhi r (-x⁻¹)) =
        (1 + x) *
            (r * (r - 1) * (x * x ^ (r - 2)) * gaussInfinityPhi r (-x⁻¹) +
              2 * (r - 1) * (x * x ^ (r - 3)) * gaussInfinityPhiD1 r (-x⁻¹) +
              (x * x ^ (r - 4)) * gaussInfinityPhiD2 r (-x⁻¹)) +
          (1 + x) *
            (r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
              x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹)) -
          r ^ 2 * (x ^ r * gaussInfinityPhi r (-x⁻¹)) := by ring
      _ = (1 + x) *
            (r * (r - 1) * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
              2 * (r - 1) * x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹) +
              x ^ (r - 3) * gaussInfinityPhiD2 r (-x⁻¹)) +
          (1 + x) *
            (r * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
              x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹)) -
          r ^ 2 * (x ^ r * gaussInfinityPhi r (-x⁻¹)) := by
        rw [hmul2, hmul3, hmul4]
      _ = r ^ 2 * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
          (2 * r - 1) * (1 + x) * x ^ (r - 2) * gaussInfinityPhiD1 r (-x⁻¹) +
          (1 + x) * x ^ (r - 3) * gaussInfinityPhiD2 r (-x⁻¹) := by
        calc
          _ = r ^ 2 * x ^ (r - 1) * gaussInfinityPhi r (-x⁻¹) +
              r ^ 2 * ((x * x ^ (r - 1)) - x ^ r) * gaussInfinityPhi r (-x⁻¹) +
              (2 * r - 1) * (1 + x) * x ^ (r - 2) *
                gaussInfinityPhiD1 r (-x⁻¹) +
              (1 + x) * x ^ (r - 3) * gaussInfinityPhiD2 r (-x⁻¹) := by ring
          _ = _ := by rw [hmul1, sub_self, mul_zero, zero_mul, add_zero]
  rw [htarget]
  rw [← hsq, ← hself]
  field_simp [hx.ne'] at hphi
  simp only [one_div] at hphi
  linear_combination (-x ^ (r - 3)) * hphi

/-! ### The Euler continuation satisfies the same negative-axis equation -/

noncomputable def gaussEulerNegativeD1 (alpha x : ℝ) : ℝ :=
  ∫ t : ℝ, (alpha / 2) * t * (1 + x * t) ^ (alpha / 2 - 1)
    ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)

noncomputable def gaussEulerNegativeD2 (alpha x : ℝ) : ℝ :=
  ∫ t : ℝ, (alpha / 2) * (alpha / 2 - 1) * t ^ 2 *
      (1 + x * t) ^ (alpha / 2 - 2)
    ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)

theorem gaussEulerNegative_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => gaussEulerContinuation alpha (-y))
      (gaussEulerNegativeD1 alpha x) x := by
  simpa only [gaussEulerNegativeD1] using
    gaussEulerContinuation_neg_hasDerivAt hα hα1 hx

theorem gaussEulerNegativeD1_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    HasDerivAt (gaussEulerNegativeD1 alpha) (gaussEulerNegativeD2 alpha x) x := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let F : ℝ → ℝ → ℝ := fun y t => u * t * (1 + y * t) ^ (u - 1)
  let F' : ℝ → ℝ → ℝ :=
    fun y t => u * (u - 1) * t ^ 2 * (1 + y * t) ^ (u - 2)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  have hs : Set.Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
  have hFmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (F y) μ := by
    filter_upwards with y
    exact (by fun_prop (disch := linarith) : Measurable (F y)).aestronglyMeasurable
  have hFint : Integrable (F x) μ := by
    simpa [F, μ, u] using gaussEulerNegativeDerivativeIntegrable hα hα1 hx
  have hF'meas : AEStronglyMeasurable (F' x) μ := by
    exact (by fun_prop (disch := linarith) : Measurable (F' x)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ Set.Ioi (0 : ℝ), ‖F' y t‖ ≤ u := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    intro y hy
    have hbase : 1 ≤ 1 + y * t := by nlinarith [mul_pos hy ht.1]
    have hbase0 : 0 ≤ 1 + y * t := zero_le_one.trans hbase
    have hpow0 : 0 ≤ (1 + y * t) ^ (u - 2) := Real.rpow_nonneg hbase0 _
    have hpow1 : (1 + y * t) ^ (u - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hprod : t ^ 2 * (1 + y * t) ^ (u - 2) ≤ 1 :=
      mul_le_one₀ ht2 hpow0 hpow1
    have hnonpos : F' y t ≤ 0 := by
      dsimp [F']
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)) (sq_nonneg t))
        hpow0
    rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
    dsimp [F']
    have hcoef : u * (1 - u) ≤ u := by nlinarith
    calc
      -(u * (u - 1) * t ^ 2 * (1 + y * t) ^ (u - 2)) =
          (u * (1 - u)) * (t ^ 2 * (1 + y * t) ^ (u - 2)) := by ring
      _ ≤ u * (1 - u) :=
        mul_le_of_le_one_right (mul_nonneg hu.le (by linarith)) hprod
      _ ≤ u := hcoef
  have hdiff : ∀ᵐ t ∂μ, ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (F · t) (F' y t) y := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    intro y hy
    have hbase : 0 < 1 + y * t := by nlinarith [mul_pos hy ht.1]
    have hinner : HasDerivAt (fun z : ℝ => 1 + z * t) t y := by
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id y).mul_const t).const_add (1 : ℝ)
    have hpow := hinner.rpow_const (p := u - 1) (.inl hbase.ne')
    have hraw := (hasDerivAt_const y (u * t)).mul hpow
    have hfun :
        (fun z : ℝ => u * t * (1 + z * t) ^ (u - 1)) =ᶠ[nhds y]
          ((fun _ : ℝ => u * t) * (fun z : ℝ => (1 + z * t) ^ (u - 1))) := by
      filter_upwards with z
      rfl
    have hraw' := hraw.congr_of_eventuallyEq hfun
    dsimp [F, F']
    apply hraw'.congr_deriv
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => u) (s := Set.Ioi 0)
    hs hFmeas hFint hF'meas hbound (integrable_const _) hdiff
  dsimp [F, F', μ, u] at h
  have hfun : gaussEulerNegativeD1 alpha =ᶠ[nhds x]
      (fun n : ℝ =>
        ∫ a : ℝ, alpha / 2 * a * (1 + n * a) ^ (alpha / 2 - 1)
          ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
    filter_upwards with y
    rfl
  have h' := h.2.congr_of_eventuallyEq hfun
  apply h'.congr_deriv
  rfl

theorem gaussEulerNegativeSecondDerivativeIntegrable {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      (alpha / 2) * (alpha / 2 - 1) * t ^ 2 *
        (1 + x * t) ^ (alpha / 2 - 2))
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  let _ := ProbabilityTheory.isProbabilityMeasureBeta hu (by linarith : 0 < 1 - u)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)) μ :=
    (by fun_prop (disch := linarith) : Measurable
      (fun t : ℝ => u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ,
      ‖u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)‖ ≤ u := by
    filter_upwards [betaMeasure_ae_mem_Ioo u (1 - u)] with t ht
    have hbase : 1 ≤ 1 + x * t := by nlinarith [mul_pos hx ht.1]
    have hpow0 : 0 ≤ (1 + x * t) ^ (u - 2) :=
      Real.rpow_nonneg (zero_le_one.trans hbase) _
    have hpow1 : (1 + x * t) ^ (u - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hprod : t ^ 2 * (1 + x * t) ^ (u - 2) ≤ 1 :=
      mul_le_one₀ ht2 hpow0 hpow1
    have hnonpos : u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)) (sq_nonneg t))
        hpow0
    rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
    calc
      -(u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)) =
          (u * (1 - u)) * (t ^ 2 * (1 + x * t) ^ (u - 2)) := by ring
      _ ≤ u * (1 - u) :=
        mul_le_of_le_one_right (mul_nonneg hu.le (by linarith)) hprod
      _ ≤ u := by nlinarith
  change Integrable
    (fun t : ℝ => u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)) μ
  exact (integrable_const u).mono' hmeas hbound

noncomputable def gaussEulerNegativeODEIntegrand (alpha x t : ℝ) : ℝ :=
  x * (1 + x) *
      ((alpha / 2) * (alpha / 2 - 1) * t ^ 2 *
        (1 + x * t) ^ (alpha / 2 - 2)) +
    (1 + x) * ((alpha / 2) * t * (1 + x * t) ^ (alpha / 2 - 1)) -
    (alpha / 2) ^ 2 * (1 + x * t) ^ (alpha / 2)

theorem gaussEulerNegativeODEIntegrand_integrable {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    Integrable (gaussEulerNegativeODEIntegrand alpha x)
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
  have h2 := gaussEulerNegativeSecondDerivativeIntegrable hα hα1 hx
  have h1 := gaussEulerNegativeDerivativeIntegrable hα hα1 hx
  have h0 : Integrable (fun t : ℝ => (1 + x * t) ^ (alpha / 2))
      (ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2)) := by
    simpa [sub_eq_add_neg] using
      gaussEulerIntegrand_integrable hα hα1 (show -x < 1 by linarith)
  unfold gaussEulerNegativeODEIntegrand
  exact ((h2.const_mul (x * (1 + x))).add (h1.const_mul (1 + x))).sub
    (h0.const_mul ((alpha / 2) ^ 2))

theorem integral_gaussEulerNegativeODEIntegrand_eq_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    ∫ t : ℝ, gaussEulerNegativeODEIntegrand alpha x t
        ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2) = 0 := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let K : ℝ → ℝ := fun t =>
    x * (1 + x) * (u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)) +
      (1 + x) * (u * t * (1 + x * t) ^ (u - 1)) -
      u ^ 2 * (1 + x * t) ^ u
  let D : ℝ → ℝ := fun t => t ^ (u - 1) * (1 - t) ^ (-u)
  let H : ℝ → ℝ := fun t =>
    t ^ u * (1 - t) ^ (1 - u) * (1 + x * t) ^ (u - 1)
  let Hp : ℝ → ℝ := fun t => -(u⁻¹) * (D t * K t)
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hub : 0 < 1 - u := by linarith
  have hK : Integrable K μ := by
    have hK0 := gaussEulerNegativeODEIntegrand_integrable hα hα1 hx
    unfold gaussEulerNegativeODEIntegrand at hK0
    simpa [K, μ, u] using hK0
  have hKpdf := hK
  dsimp [μ] at hKpdf
  rw [ProbabilityTheory.betaMeasure,
    integrable_withDensity_iff_integrable_smul'
      (betaPDF_measurable u (1 - u)) (betaPDF_ae_lt_top u (1 - u))] at hKpdf
  simp_rw [betaPDF_toReal hu hub, smul_eq_mul] at hKpdf
  have hBne : ProbabilityTheory.beta u (1 - u) ≠ 0 :=
    (ProbabilityTheory.beta_pos hu hub).ne'
  have hdenKOn : IntegrableOn (fun t : ℝ => D t * K t) (Set.Ioo 0 1) := by
    apply IntegrableOn.congr_fun
      ((hKpdf.const_mul (ProbabilityTheory.beta u (1 - u))).integrableOn)
      _ measurableSet_Ioo
    intro t ht
    change ProbabilityTheory.beta u (1 - u) *
        (ProbabilityTheory.betaPDFReal u (1 - u) t * K t) = D t * K t
    rw [ProbabilityTheory.betaPDFReal, if_pos ⟨ht.1, ht.2⟩]
    dsimp [D]
    rw [show 1 - u - 1 = -u by ring]
    field_simp [hBne]
  have hHpOn : IntegrableOn Hp (Set.Ioo 0 1) := by
    change Integrable Hp (volume.restrict (Set.Ioo 0 1))
    simpa only [Hp] using hdenKOn.const_mul (-(u⁻¹))
  have hHpInt : IntervalIntegrable Hp volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    exact hHpOn
  have hAcont : Continuous (fun t : ℝ => t ^ u) :=
    Real.continuous_rpow_const hu.le
  have hBcont : Continuous (fun t : ℝ => (1 - t) ^ (1 - u)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
  have hCcont : ContinuousOn (fun t : ℝ => (1 + x * t) ^ (u - 1)) (Set.Icc 0 1) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.rpow_const
      (fun t ht => Or.inl (by
        have ht0 : 0 ≤ t := ht.1
        have : 0 < 1 + x * t := by nlinarith
        exact this.ne'))
  have hHcont : ContinuousOn H (Set.Icc 0 1) := by
    apply ((hAcont.mul hBcont).continuousOn.mul hCcont).congr
    intro t ht
    rfl
  have hHderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt H (Hp t) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
    have hbase : 0 < 1 + x * t := by nlinarith [mul_pos hx ht0]
    have hA := Real.hasDerivAt_rpow_const (x := t) (p := u) (.inl ht0.ne')
    have hBinner0 := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hBfun : (fun z : ℝ => 1 - z) =ᶠ[nhds t] ((fun _ : ℝ => 1) - id) := by
      filter_upwards with z
      rfl
    have hBinner := hBinner0.congr_of_eventuallyEq hBfun
    have hB := hBinner.rpow_const (p := 1 - u) (.inl ht1.ne')
    have hCinner0 := ((hasDerivAt_id t).mul_const x).const_add (1 : ℝ)
    have hCfun : (fun z : ℝ => 1 + x * z) =ᶠ[nhds t]
        (fun z : ℝ => 1 + id z * x) := by
      filter_upwards with z
      simp only [id_eq, mul_comm]
    have hCinner := hCinner0.congr_of_eventuallyEq hCfun
    have hC := hCinner.rpow_const (p := u - 1) (.inl hbase.ne')
    have hraw := (hA.mul hB).mul hC
    have hfun : H =ᶠ[nhds t]
        (((fun z : ℝ => z ^ u) * (fun z : ℝ => (1 - z) ^ (1 - u))) *
          (fun z : ℝ => (1 + x * z) ^ (u - 1))) := by
      filter_upwards with z
      rfl
    have hraw' := hraw.congr_of_eventuallyEq hfun
    apply hraw'.congr_deriv
    have htPow : t ^ u = t ^ (u - 1) * t := by
      calc
        t ^ u = t ^ ((u - 1) + 1) := by congr 1 <;> ring
        _ = t ^ (u - 1) * t ^ (1 : ℝ) := Real.rpow_add ht0 (u - 1) 1
        _ = t ^ (u - 1) * t := by rw [Real.rpow_one]
    have hsubPow : (1 - t) ^ (1 - u) = (1 - t) ^ (-u) * (1 - t) := by
      calc
        (1 - t) ^ (1 - u) = (1 - t) ^ ((-u) + 1) := by congr 1 <;> ring
        _ = (1 - t) ^ (-u) * (1 - t) ^ (1 : ℝ) :=
          Real.rpow_add ht1 (-u) 1
        _ = (1 - t) ^ (-u) * (1 - t) := by rw [Real.rpow_one]
    have hbasePow : (1 + x * t) ^ (u - 1) =
        (1 + x * t) ^ (u - 2) * (1 + x * t) := by
      calc
        (1 + x * t) ^ (u - 1) = (1 + x * t) ^ ((u - 2) + 1) := by
          congr 1 <;> ring
        _ = (1 + x * t) ^ (u - 2) * (1 + x * t) ^ (1 : ℝ) :=
          Real.rpow_add hbase (u - 2) 1
        _ = (1 + x * t) ^ (u - 2) * (1 + x * t) := by rw [Real.rpow_one]
    have hbasePowU : (1 + x * t) ^ u =
        (1 + x * t) ^ (u - 1) * (1 + x * t) := by
      calc
        (1 + x * t) ^ u = (1 + x * t) ^ ((u - 1) + 1) := by
          congr 1 <;> ring
        _ = (1 + x * t) ^ (u - 1) * (1 + x * t) ^ (1 : ℝ) :=
          Real.rpow_add hbase (u - 1) 1
        _ = (1 + x * t) ^ (u - 1) * (1 + x * t) := by rw [Real.rpow_one]
    have heSub : 1 - u - 1 = -u := by ring
    have heBase : u - 1 - 1 = u - 2 := by ring
    dsimp [Hp, D, K]
    rw [heSub, heBase, htPow, hsubPow, hbasePowU, hbasePow]
    field_simp [hu.ne']
    ring
  have hFTC : ∫ t : ℝ in 0..1, Hp t = H 1 - H 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hHcont hHderiv hHpInt
  have hH0 : H 0 = 0 := by
    simp [H, Real.zero_rpow hu.ne']
  have hH1 : H 1 = 0 := by
    simp [H, Real.zero_rpow (by linarith : 1 - u ≠ 0)]
  rw [hH1, hH0, sub_self] at hFTC
  have hscale : ∫ t : ℝ in 0..1, Hp t =
      -(u⁻¹) * ∫ t : ℝ in 0..1, D t * K t := by
    dsimp [Hp]
    rw [intervalIntegral.integral_const_mul]
  rw [hscale] at hFTC
  have hcoef : -(u⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hu.ne')
  have hdenZero : ∫ t : ℝ in 0..1, D t * K t = 0 :=
    (mul_eq_zero.mp hFTC).resolve_left hcoef
  change ∫ t : ℝ, K t ∂μ = 0
  rw [betaMeasure_integral_eq_intervalIntegral hu hub]
  change (ProbabilityTheory.beta u (1 - u))⁻¹ *
    (∫ t : ℝ in 0..1, t ^ (u - 1) * (1 - t) ^ (1 - u - 1) * K t) = 0
  rw [show 1 - u - 1 = -u by ring]
  change (ProbabilityTheory.beta u (1 - u))⁻¹ *
    (∫ t : ℝ in 0..1, D t * K t) = 0
  rw [hdenZero, mul_zero]

theorem gaussEulerNegative_ode {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 0 < x) :
    x * (1 + x) * gaussEulerNegativeD2 alpha x +
        (1 + x) * gaussEulerNegativeD1 alpha x -
      (alpha / 2) ^ 2 * gaussEulerContinuation alpha (-x) = 0 := by
  let u : ℝ := alpha / 2
  let μ : Measure ℝ := ProbabilityTheory.betaMeasure u (1 - u)
  let f2 : ℝ → ℝ := fun t =>
    u * (u - 1) * t ^ 2 * (1 + x * t) ^ (u - 2)
  let f1 : ℝ → ℝ := fun t => u * t * (1 + x * t) ^ (u - 1)
  let f0 : ℝ → ℝ := fun t => (1 + x * t) ^ u
  have h2 : Integrable f2 μ := by
    simpa [f2, μ, u] using gaussEulerNegativeSecondDerivativeIntegrable hα hα1 hx
  have h1 : Integrable f1 μ := by
    simpa [f1, μ, u] using gaussEulerNegativeDerivativeIntegrable hα hα1 hx
  have h0 : Integrable f0 μ := by
    simpa [f0, μ, u, sub_eq_add_neg] using
      gaussEulerIntegrand_integrable hα hα1 (show -x < 1 by linarith)
  have hadd := MeasureTheory.integral_add
    (h2.const_mul (x * (1 + x))) (h1.const_mul (1 + x))
  have haddPi :
      ∫ t : ℝ,
          ((fun z : ℝ => x * (1 + x) * f2 z) +
            (fun z : ℝ => (1 + x) * f1 z)) t ∂μ =
        (∫ t : ℝ, x * (1 + x) * f2 t ∂μ) +
          ∫ t : ℝ, (1 + x) * f1 t ∂μ := by
    simpa only [Pi.add_apply] using hadd
  have hsub := MeasureTheory.integral_sub
    ((h2.const_mul (x * (1 + x))).add (h1.const_mul (1 + x)))
    (h0.const_mul (u ^ 2))
  have hzero := integral_gaussEulerNegativeODEIntegrand_eq_zero hα hα1 hx
  unfold gaussEulerNegativeD2 gaussEulerNegativeD1 gaussEulerContinuation
  simp only [neg_mul, sub_neg_eq_add]
  change x * (1 + x) * (∫ t : ℝ, f2 t ∂μ) +
      (1 + x) * (∫ t : ℝ, f1 t ∂μ) -
      u ^ 2 * (∫ t : ℝ, f0 t ∂μ) = 0
  calc
    x * (1 + x) * (∫ t : ℝ, f2 t ∂μ) +
          (1 + x) * (∫ t : ℝ, f1 t ∂μ) -
          u ^ 2 * (∫ t : ℝ, f0 t ∂μ) =
        ∫ t : ℝ,
          x * (1 + x) * f2 t + (1 + x) * f1 t - u ^ 2 * f0 t ∂μ := by
      change x * (1 + x) * (∫ t : ℝ, f2 t ∂μ) +
          (1 + x) * (∫ t : ℝ, f1 t ∂μ) -
          u ^ 2 * (∫ t : ℝ, f0 t ∂μ) =
        ∫ t : ℝ,
          (((fun z : ℝ => x * (1 + x) * f2 z) +
            (fun z : ℝ => (1 + x) * f1 z)) t - u ^ 2 * f0 t) ∂μ
      rw [hsub, haddPi]
      simp only [MeasureTheory.integral_const_mul]
    _ = ∫ t : ℝ, gaussEulerNegativeODEIntegrand alpha x t
          ∂ProbabilityTheory.betaMeasure (alpha / 2) (1 - alpha / 2) := by
      apply integral_congr_ae
      filter_upwards with t
      rfl
    _ = 0 := hzero

end Hilbert16.Spikes
