import Hilbert16.Spikes.BorelGaussODE

open Nat Polynomial MeasureTheory Filter Set

namespace Hilbert16.Spikes

noncomputable def gaussPlusBranch (alpha x : ℝ) : ℝ :=
  gaussInfinityBranch (alpha / 2) x

noncomputable def gaussPlusBranchD1 (alpha x : ℝ) : ℝ :=
  gaussInfinityBranchD1 (alpha / 2) x

noncomputable def gaussPlusBranchD2 (alpha x : ℝ) : ℝ :=
  gaussInfinityBranchD2 (alpha / 2) x

noncomputable def gaussMinusBranch (alpha x : ℝ) : ℝ :=
  gaussInfinityBranch (-alpha / 2) x

noncomputable def gaussMinusBranchD1 (alpha x : ℝ) : ℝ :=
  gaussInfinityBranchD1 (-alpha / 2) x

noncomputable def gaussMinusBranchD2 (alpha x : ℝ) : ℝ :=
  gaussInfinityBranchD2 (-alpha / 2) x

theorem gaussPlusBranch_eq (alpha x : ℝ) :
    gaussPlusBranch alpha x =
      x ^ (alpha / 2) * gaussPhiPlus alpha (-(x⁻¹)) := by
  unfold gaussPlusBranch gaussInfinityBranch gaussInfinityPhi gaussPhiPlus
  rw [show -(alpha / 2) = -alpha / 2 by ring,
    show 1 - 2 * (alpha / 2) = 1 - alpha by ring]

theorem gaussMinusBranch_eq (alpha x : ℝ) :
    gaussMinusBranch alpha x =
      x ^ (-alpha / 2) * gaussPhiMinus alpha (-(x⁻¹)) := by
  unfold gaussMinusBranch gaussInfinityBranch gaussInfinityPhi gaussPhiMinus
  rw [show -(-alpha / 2) = alpha / 2 by ring,
    show 1 - 2 * (-alpha / 2) = 1 + alpha by ring]

theorem negativeAxisConnectionRHS_eq_branches (alpha x : ℝ) :
    negativeAxisConnectionRHS alpha x =
      gaussConnectionA alpha * gaussPlusBranch alpha x +
        gaussConnectionB alpha * gaussMinusBranch alpha x := by
  rw [gaussPlusBranch_eq, gaussMinusBranch_eq]
  unfold negativeAxisConnectionRHS
  ring

theorem gaussPlusBranch_radius_condition {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    ‖-(x⁻¹)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-(alpha / 2)) (-(alpha / 2))
        (1 - 2 * (alpha / 2))).radius := by
  rw [show -(alpha / 2) = -alpha / 2 by ring,
    show 1 - 2 * (alpha / 2) = 1 - alpha by ring,
    gaussPhiPlus_radius_eq_one hα hα1, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_lt_one]
  simpa [Real.norm_eq_abs] using negativeAxis_inverse_mem_unitDisk hx

theorem gaussMinusBranch_radius_condition {alpha x : ℝ}
    (hα : 0 < alpha) (hx : 1 < x) :
    ‖-(x⁻¹)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-(-alpha / 2)) (-(-alpha / 2))
        (1 - 2 * (-alpha / 2))).radius := by
  rw [show -(-alpha / 2) = alpha / 2 by ring,
    show 1 - 2 * (-alpha / 2) = 1 + alpha by ring,
    gaussPhiMinus_radius_eq_one hα, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_lt_one]
  simpa [Real.norm_eq_abs] using negativeAxis_inverse_mem_unitDisk hx

theorem gaussPlusBranch_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussPlusBranch alpha) (gaussPlusBranchD1 alpha x) x := by
  exact gaussInfinityBranch_hasDerivAt (by linarith)
    (gaussPlusBranch_radius_condition hα hα1 hx)

theorem gaussPlusBranchD1_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussPlusBranchD1 alpha) (gaussPlusBranchD2 alpha x) x := by
  exact gaussInfinityBranchD1_hasDerivAt (by linarith)
    (gaussPlusBranch_radius_condition hα hα1 hx)

theorem gaussMinusBranch_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hx : 1 < x) :
    HasDerivAt (gaussMinusBranch alpha) (gaussMinusBranchD1 alpha x) x := by
  exact gaussInfinityBranch_hasDerivAt (by linarith)
    (gaussMinusBranch_radius_condition hα hx)

theorem gaussMinusBranchD1_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hx : 1 < x) :
    HasDerivAt (gaussMinusBranchD1 alpha) (gaussMinusBranchD2 alpha x) x := by
  exact gaussInfinityBranchD1_hasDerivAt (by linarith)
    (gaussMinusBranch_radius_condition hα hx)

theorem gaussPlusBranch_ode {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    x * (1 + x) * gaussPlusBranchD2 alpha x +
        (1 + x) * gaussPlusBranchD1 alpha x -
      (alpha / 2) ^ 2 * gaussPlusBranch alpha x = 0 := by
  exact gaussInfinityBranch_ode (by linarith) (by linarith)
    (gaussPlusBranch_radius_condition hα hα1 hx)

theorem gaussMinusBranch_ode {alpha x : ℝ}
    (hα : 0 < alpha) (hx : 1 < x) :
    x * (1 + x) * gaussMinusBranchD2 alpha x +
        (1 + x) * gaussMinusBranchD1 alpha x -
      (alpha / 2) ^ 2 * gaussMinusBranch alpha x = 0 := by
  have h := gaussInfinityBranch_ode (r := -alpha / 2) (x := x)
    (by linarith) (by linarith) (gaussMinusBranch_radius_condition hα hx)
  dsimp [gaussMinusBranch, gaussMinusBranchD1, gaussMinusBranchD2] at h ⊢
  nlinarith

/-! ### Normalized limits of the two infinity branches -/

theorem gaussInfinityPhi_comp_neg_inv_tendsto {r : ℝ}
    (hrad : 0 <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    Tendsto (fun x : ℝ => gaussInfinityPhi r (-(x⁻¹))) atTop (nhds 1) := by
  have hz0 : ‖(0 : ℝ)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius := by
    simpa using hrad
  have hzlim : Tendsto (fun x : ℝ => -(x⁻¹)) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.neg :
      Tendsto (fun x : ℝ => -(x⁻¹)) atTop (nhds (-0)))
  have h := (gaussInfinityPhi_hasDerivAt hz0).continuousAt.tendsto.comp hzlim
  rw [← show gaussInfinityPhi r 0 = 1 by simp [gaussInfinityPhi]]
  apply h.congr'
  filter_upwards with x
  rfl

theorem gaussInfinityPhiD1_comp_neg_inv_tendsto {r : ℝ}
    (hrad : 0 <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius) :
    Tendsto (fun x : ℝ => gaussInfinityPhiD1 r (-(x⁻¹))) atTop
      (nhds (gaussInfinityPhiD1 r 0)) := by
  have hz0 : ‖(0 : ℝ)‖ₑ <
      (ordinaryHypergeometricSeries ℝ (-r) (-r) (1 - 2 * r)).radius := by
    simpa using hrad
  have hzlim : Tendsto (fun x : ℝ => -(x⁻¹)) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.neg :
      Tendsto (fun x : ℝ => -(x⁻¹)) atTop (nhds (-0)))
  exact (gaussInfinityPhiD1_hasDerivAt hz0).continuousAt.tendsto.comp hzlim

private theorem gaussPlus_radius_pos {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    0 < (ordinaryHypergeometricSeries ℝ (-(alpha / 2)) (-(alpha / 2))
      (1 - 2 * (alpha / 2))).radius := by
  rw [show -(alpha / 2) = -alpha / 2 by ring,
    show 1 - 2 * (alpha / 2) = 1 - alpha by ring,
    gaussPhiPlus_radius_eq_one hα hα1]
  norm_num

private theorem gaussMinus_radius_pos {alpha : ℝ} (hα : 0 < alpha) :
    0 < (ordinaryHypergeometricSeries ℝ (-(-alpha / 2)) (-(-alpha / 2))
      (1 - 2 * (-alpha / 2))).radius := by
  rw [show -(-alpha / 2) = alpha / 2 by ring,
    show 1 - 2 * (-alpha / 2) = 1 + alpha by ring,
    gaussPhiMinus_radius_eq_one hα]
  norm_num

theorem gaussPlusBranch_normalized_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (fun x : ℝ => gaussPlusBranch alpha x / x ^ (alpha / 2))
      atTop (nhds 1) := by
  have hphi := gaussInfinityPhi_comp_neg_inv_tendsto
    (gaussPlus_radius_pos hα hα1)
  apply hphi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussPlusBranch gaussInfinityBranch
  field_simp [(Real.rpow_pos_of_pos hx (alpha / 2)).ne']

theorem gaussMinusBranch_normalized_tendsto {alpha : ℝ}
    (hα : 0 < alpha) :
    Tendsto (fun x : ℝ => gaussMinusBranch alpha x / x ^ (alpha / 2))
      atTop (nhds 0) := by
  have hphi := gaussInfinityPhi_comp_neg_inv_tendsto (gaussMinus_radius_pos hα)
  have hpow : Tendsto (fun x : ℝ => x ^ (-alpha)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hα
  have hprod := hpow.mul hphi
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussMinusBranch gaussInfinityBranch
  symm
  calc
    x ^ (-alpha / 2) * gaussInfinityPhi (-alpha / 2) (-x⁻¹) /
          x ^ (alpha / 2) =
        (x ^ (-alpha / 2) / x ^ (alpha / 2)) *
          gaussInfinityPhi (-alpha / 2) (-x⁻¹) := by ring
    _ = x ^ ((-alpha / 2) - alpha / 2) *
          gaussInfinityPhi (-alpha / 2) (-x⁻¹) := by
      rw [Real.rpow_sub hx]
    _ = x ^ (-alpha) * gaussInfinityPhi (-alpha / 2) (-x⁻¹) := by
      congr 2 <;> ring

noncomputable def gaussPlusDecayOperator (alpha x : ℝ) : ℝ :=
  x ^ (alpha / 2) *
    (x * gaussPlusBranchD1 alpha x - (alpha / 2) * gaussPlusBranch alpha x)

noncomputable def gaussMinusDecayOperator (alpha x : ℝ) : ℝ :=
  x ^ (alpha / 2) *
    (x * gaussMinusBranchD1 alpha x - (alpha / 2) * gaussMinusBranch alpha x)

private theorem rpow_mul_self_connection {q x : ℝ} (hx : 0 < x) :
    x ^ q * x = x ^ (q + 1) := (Real.rpow_add_one hx.ne' q).symm

theorem gaussPlusDecayOperator_eq {alpha x : ℝ} (hx : 0 < x) :
    gaussPlusDecayOperator alpha x =
      x ^ (alpha - 1) * gaussInfinityPhiD1 (alpha / 2) (-(x⁻¹)) := by
  let u : ℝ := alpha / 2
  have h1 : x * x ^ (u - 1) = x ^ u := by
    rw [mul_comm, rpow_mul_self_connection hx]
    congr 1 <;> ring
  have h2 : x * x ^ (u - 2) = x ^ (u - 1) := by
    rw [mul_comm, rpow_mul_self_connection hx]
    congr 1 <;> ring
  have h3 : x ^ u * x ^ (u - 1) = x ^ (alpha - 1) := by
    rw [← Real.rpow_add hx]
    congr 1 <;> dsimp [u] <;> ring
  unfold gaussPlusDecayOperator gaussPlusBranch gaussPlusBranchD1
  unfold gaussInfinityBranch gaussInfinityBranchD1
  change x ^ u *
      (x * (u * x ^ (u - 1) * gaussInfinityPhi u (-x⁻¹) +
        x ^ (u - 2) * gaussInfinityPhiD1 u (-x⁻¹)) -
        u * (x ^ u * gaussInfinityPhi u (-x⁻¹))) =
    x ^ (alpha - 1) * gaussInfinityPhiD1 u (-x⁻¹)
  calc
    _ = x ^ u *
        ((u * (x * x ^ (u - 1)) - u * x ^ u) *
            gaussInfinityPhi u (-x⁻¹) +
          (x * x ^ (u - 2)) * gaussInfinityPhiD1 u (-x⁻¹)) := by ring
    _ = x ^ u * (x ^ (u - 1) * gaussInfinityPhiD1 u (-x⁻¹)) := by
      rw [h1, h2]
      ring
    _ = x ^ (alpha - 1) * gaussInfinityPhiD1 u (-x⁻¹) := by
      calc
        _ = (x ^ u * x ^ (u - 1)) * gaussInfinityPhiD1 u (-x⁻¹) := by ring
        _ = _ := by rw [h3]

theorem gaussMinusDecayOperator_eq {alpha x : ℝ} (hx : 0 < x) :
    gaussMinusDecayOperator alpha x =
      -alpha * gaussInfinityPhi (-alpha / 2) (-(x⁻¹)) +
        x ^ (-1 : ℝ) * gaussInfinityPhiD1 (-alpha / 2) (-(x⁻¹)) := by
  let u : ℝ := alpha / 2
  have h1 : x * x ^ (-u - 1) = x ^ (-u) := by
    rw [mul_comm, rpow_mul_self_connection hx]
    congr 1 <;> ring
  have h2 : x * x ^ (-u - 2) = x ^ (-u - 1) := by
    rw [mul_comm, rpow_mul_self_connection hx]
    congr 1 <;> ring
  have h3 : x ^ u * x ^ (-u) = 1 := by
    rw [← Real.rpow_add hx]
    simp
  have h4 : x ^ u * x ^ (-u - 1) = x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1 <;> ring
  unfold gaussMinusDecayOperator gaussMinusBranch gaussMinusBranchD1
  unfold gaussInfinityBranch gaussInfinityBranchD1
  rw [show -alpha / 2 = -(alpha / 2) by ring]
  change x ^ u *
      (x * ((-u) * x ^ (-u - 1) * gaussInfinityPhi (-u) (-x⁻¹) +
        x ^ (-u - 2) * gaussInfinityPhiD1 (-u) (-x⁻¹)) -
        u * (x ^ (-u) * gaussInfinityPhi (-u) (-x⁻¹))) = _
  calc
    _ = x ^ u *
        (((-u) * (x * x ^ (-u - 1)) - u * x ^ (-u)) *
            gaussInfinityPhi (-u) (-x⁻¹) +
          (x * x ^ (-u - 2)) * gaussInfinityPhiD1 (-u) (-x⁻¹)) := by ring
    _ = x ^ u *
        ((-2 * u) * x ^ (-u) * gaussInfinityPhi (-u) (-x⁻¹) +
          x ^ (-u - 1) * gaussInfinityPhiD1 (-u) (-x⁻¹)) := by
      rw [h1, h2]
      ring
    _ = (-2 * u) * gaussInfinityPhi (-u) (-x⁻¹) +
        x ^ (-1 : ℝ) * gaussInfinityPhiD1 (-u) (-x⁻¹) := by
      calc
        _ = (-2 * u) * (x ^ u * x ^ (-u)) * gaussInfinityPhi (-u) (-x⁻¹) +
            (x ^ u * x ^ (-u - 1)) * gaussInfinityPhiD1 (-u) (-x⁻¹) := by ring
        _ = _ := by rw [h3, h4, mul_one]
    _ = -alpha * gaussInfinityPhi (-(alpha / 2)) (-x⁻¹) +
        x ^ (-1 : ℝ) * gaussInfinityPhiD1 (-(alpha / 2)) (-x⁻¹) := by
      dsimp [u]
      ring

theorem gaussPlusDecayOperator_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (gaussPlusDecayOperator alpha) atTop (nhds 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ (-(1 - alpha))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (sub_pos.mpr hα1)
  have hphi := gaussInfinityPhiD1_comp_neg_inv_tendsto
    (gaussPlus_radius_pos hα hα1)
  have h := hp.mul hphi
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [gaussPlusDecayOperator_eq hx]
  congr 2 <;> ring

theorem gaussMinusDecayOperator_tendsto {alpha : ℝ}
    (hα : 0 < alpha) :
    Tendsto (gaussMinusDecayOperator alpha) atTop (nhds (-alpha)) := by
  have hphi := gaussInfinityPhi_comp_neg_inv_tendsto (gaussMinus_radius_pos hα)
  have hphi1 := gaussInfinityPhiD1_comp_neg_inv_tendsto (gaussMinus_radius_pos hα)
  have hinv : Tendsto (fun x : ℝ => x ^ (-1 : ℝ)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num))
  have hconst : Tendsto (fun _ : ℝ => -alpha) atTop (nhds (-alpha)) :=
    tendsto_const_nhds
  have h := (hconst.mul hphi).add (hinv.mul hphi1)
  simp only [mul_one, zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gaussMinusDecayOperator_eq hx).symm

/-! ### The connection remainder and its two vanishing infinity data -/

noncomputable def gaussConnectionRemainder (alpha x : ℝ) : ℝ :=
  gaussEulerContinuation alpha (-x) -
    gaussConnectionA alpha * gaussPlusBranch alpha x -
    gaussConnectionB alpha * gaussMinusBranch alpha x

noncomputable def gaussConnectionRemainderD1 (alpha x : ℝ) : ℝ :=
  gaussEulerNegativeD1 alpha x -
    gaussConnectionA alpha * gaussPlusBranchD1 alpha x -
    gaussConnectionB alpha * gaussMinusBranchD1 alpha x

noncomputable def gaussConnectionRemainderD2 (alpha x : ℝ) : ℝ :=
  gaussEulerNegativeD2 alpha x -
    gaussConnectionA alpha * gaussPlusBranchD2 alpha x -
    gaussConnectionB alpha * gaussMinusBranchD2 alpha x

noncomputable def gaussConnectionRemainderDecayOperator (alpha x : ℝ) : ℝ :=
  x ^ (alpha / 2) *
    (x * gaussConnectionRemainderD1 alpha x -
      (alpha / 2) * gaussConnectionRemainder alpha x)

theorem gaussConnectionRemainder_normalized_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (fun x : ℝ =>
      gaussConnectionRemainder alpha x / x ^ (alpha / 2)) atTop (nhds 0) := by
  have hE := gaussEulerContinuation_leading_tendsto hα hα1
  have hP := gaussPlusBranch_normalized_tendsto hα hα1
  have hM := gaussMinusBranch_normalized_tendsto hα
  have hA : Tendsto (fun _ : ℝ => gaussConnectionA alpha) atTop
      (nhds (gaussConnectionA alpha)) := tendsto_const_nhds
  have hB : Tendsto (fun _ : ℝ => gaussConnectionB alpha) atTop
      (nhds (gaussConnectionB alpha)) := tendsto_const_nhds
  have h := (hE.sub (hA.mul hP)).sub (hB.mul hM)
  have h' : Tendsto
      (fun x : ℝ => gaussEulerContinuation alpha (-x) / x ^ (alpha / 2) -
        gaussConnectionA alpha * (gaussPlusBranch alpha x / x ^ (alpha / 2)) -
        gaussConnectionB alpha * (gaussMinusBranch alpha x / x ^ (alpha / 2)))
      atTop (nhds 0) := by
    convert h using 1 <;> ring
  apply h'.congr'
  filter_upwards with x
  unfold gaussConnectionRemainder
  ring

theorem gaussConnectionRemainderDecayOperator_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (gaussConnectionRemainderDecayOperator alpha) atTop (nhds 0) := by
  have hE := gaussEulerContinuation_decay_operator_tendsto hα hα1
  have hP := gaussPlusDecayOperator_tendsto hα hα1
  have hM := gaussMinusDecayOperator_tendsto hα
  have hA : Tendsto (fun _ : ℝ => gaussConnectionA alpha) atTop
      (nhds (gaussConnectionA alpha)) := tendsto_const_nhds
  have hB : Tendsto (fun _ : ℝ => gaussConnectionB alpha) atTop
      (nhds (gaussConnectionB alpha)) := tendsto_const_nhds
  have h := (hE.sub (hA.mul hP)).sub (hB.mul hM)
  have h' : Tendsto
      (fun x : ℝ =>
        x ^ (alpha / 2) *
            (x * gaussEulerNegativeD1 alpha x -
              (alpha / 2) * gaussEulerContinuation alpha (-x)) -
          gaussConnectionA alpha * gaussPlusDecayOperator alpha x -
          gaussConnectionB alpha * gaussMinusDecayOperator alpha x)
      atTop (nhds 0) := by
    have hlim : -alpha * gaussConnectionB alpha - gaussConnectionA alpha * 0 -
        gaussConnectionB alpha * -alpha = 0 := by ring
    rw [hlim] at h
    apply h.congr'
    filter_upwards with x
    unfold gaussEulerNegativeD1
    ring
  apply h'.congr'
  filter_upwards with x
  unfold gaussConnectionRemainderDecayOperator gaussConnectionRemainderD1
  unfold gaussConnectionRemainder gaussPlusDecayOperator gaussMinusDecayOperator
  ring

theorem gaussConnectionRemainder_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussConnectionRemainder alpha)
      (gaussConnectionRemainderD1 alpha x) x := by
  have hE := gaussEulerNegative_hasDerivAt hα hα1 (by linarith : 0 < x)
  have hP := gaussPlusBranch_hasDerivAt hα hα1 hx
  have hM := gaussMinusBranch_hasDerivAt hα hx
  have hraw := (hE.sub ((hasDerivAt_const x (gaussConnectionA alpha)).mul hP)).sub
    ((hasDerivAt_const x (gaussConnectionB alpha)).mul hM)
  have hfun : gaussConnectionRemainder alpha =ᶠ[nhds x]
      ((fun y : ℝ => gaussEulerContinuation alpha (-y)) -
        (fun _ : ℝ => gaussConnectionA alpha) * gaussPlusBranch alpha -
        (fun _ : ℝ => gaussConnectionB alpha) * gaussMinusBranch alpha) := by
    filter_upwards with y
    rfl
  have hraw' := hraw.congr_of_eventuallyEq hfun
  apply hraw'.congr_deriv
  unfold gaussConnectionRemainderD1
  simp only [zero_mul, zero_add]

theorem gaussConnectionRemainderD1_hasDerivAt {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussConnectionRemainderD1 alpha)
      (gaussConnectionRemainderD2 alpha x) x := by
  have hE := gaussEulerNegativeD1_hasDerivAt hα hα1 (by linarith : 0 < x)
  have hP := gaussPlusBranchD1_hasDerivAt hα hα1 hx
  have hM := gaussMinusBranchD1_hasDerivAt hα hx
  have hraw := (hE.sub ((hasDerivAt_const x (gaussConnectionA alpha)).mul hP)).sub
    ((hasDerivAt_const x (gaussConnectionB alpha)).mul hM)
  have hfun : gaussConnectionRemainderD1 alpha =ᶠ[nhds x]
      (gaussEulerNegativeD1 alpha -
        (fun _ : ℝ => gaussConnectionA alpha) * gaussPlusBranchD1 alpha -
        (fun _ : ℝ => gaussConnectionB alpha) * gaussMinusBranchD1 alpha) := by
    filter_upwards with y
    rfl
  have hraw' := hraw.congr_of_eventuallyEq hfun
  apply hraw'.congr_deriv
  unfold gaussConnectionRemainderD2
  simp only [zero_mul, zero_add]

theorem gaussConnectionRemainder_ode {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    x * (1 + x) * gaussConnectionRemainderD2 alpha x +
        (1 + x) * gaussConnectionRemainderD1 alpha x -
      (alpha / 2) ^ 2 * gaussConnectionRemainder alpha x = 0 := by
  have hE := gaussEulerNegative_ode hα hα1 (by linarith : 0 < x)
  have hP := gaussPlusBranch_ode hα hα1 hx
  have hM := gaussMinusBranch_ode hα hx
  unfold gaussConnectionRemainder gaussConnectionRemainderD1
  unfold gaussConnectionRemainderD2
  linear_combination hE - gaussConnectionA alpha * hP - gaussConnectionB alpha * hM

/-! ### Conserved scaled Wronskians -/

theorem scaledWronskian_hasDerivAt_zero
    {f f1 g g1 : ℝ → ℝ} {f2 g2 u x : ℝ}
    (hx : 1 < x)
    (hf : HasDerivAt f (f1 x) x) (hf1 : HasDerivAt f1 f2 x)
    (hg : HasDerivAt g (g1 x) x) (hg1 : HasDerivAt g1 g2 x)
    (hfODE : x * (1 + x) * f2 + (1 + x) * f1 x - u ^ 2 * f x = 0)
    (hgODE : x * (1 + x) * g2 + (1 + x) * g1 x - u ^ 2 * g x = 0) :
    HasDerivAt (fun y : ℝ => y * (f y * g1 y - f1 y * g y)) 0 x := by
  have hraw := (hasDerivAt_id x).mul ((hf.mul hg1).sub (hf1.mul hg))
  apply hraw.congr_deriv
  simp only [id_eq, one_mul]
  have hx1 : 1 + x ≠ 0 := by linarith
  have hmul :
      ((f x * g1 x - f1 x * g x +
          x * ((f1 x * g1 x + f x * g2) - (f2 * g x + f1 x * g1 x))) *
        (1 + x)) = 0 := by
    linear_combination f x * hgODE - g x * hfODE
  exact (mul_eq_zero.mp hmul).resolve_right hx1

noncomputable def gaussRemainderWronskianPlus (alpha x : ℝ) : ℝ :=
  x * (gaussConnectionRemainder alpha x * gaussPlusBranchD1 alpha x -
    gaussConnectionRemainderD1 alpha x * gaussPlusBranch alpha x)

noncomputable def gaussRemainderWronskianMinus (alpha x : ℝ) : ℝ :=
  x * (gaussConnectionRemainder alpha x * gaussMinusBranchD1 alpha x -
    gaussConnectionRemainderD1 alpha x * gaussMinusBranch alpha x)

noncomputable def gaussBranchWronskian (alpha x : ℝ) : ℝ :=
  x * (gaussPlusBranch alpha x * gaussMinusBranchD1 alpha x -
    gaussPlusBranchD1 alpha x * gaussMinusBranch alpha x)

theorem gaussRemainderWronskianPlus_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (gaussRemainderWronskianPlus alpha) atTop (nhds 0) := by
  have hR := gaussConnectionRemainder_normalized_tendsto hα hα1
  have hRq := gaussConnectionRemainderDecayOperator_tendsto hα hα1
  have hP := gaussPlusBranch_normalized_tendsto hα hα1
  have hPq := gaussPlusDecayOperator_tendsto hα hα1
  have h := (hR.mul hPq).sub (hP.mul hRq)
  simp only [zero_mul, one_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussConnectionRemainderDecayOperator gaussPlusDecayOperator
  unfold gaussRemainderWronskianPlus
  field_simp [(Real.rpow_pos_of_pos hx (alpha / 2)).ne']
  ring

theorem gaussRemainderWronskianMinus_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (gaussRemainderWronskianMinus alpha) atTop (nhds 0) := by
  have hR := gaussConnectionRemainder_normalized_tendsto hα hα1
  have hRq := gaussConnectionRemainderDecayOperator_tendsto hα hα1
  have hM := gaussMinusBranch_normalized_tendsto hα
  have hMq := gaussMinusDecayOperator_tendsto hα
  have h := (hR.mul hMq).sub (hM.mul hRq)
  simp only [zero_mul, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussConnectionRemainderDecayOperator gaussMinusDecayOperator
  unfold gaussRemainderWronskianMinus
  field_simp [(Real.rpow_pos_of_pos hx (alpha / 2)).ne']
  ring

theorem gaussBranchWronskian_tendsto {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    Tendsto (gaussBranchWronskian alpha) atTop (nhds (-alpha)) := by
  have hP := gaussPlusBranch_normalized_tendsto hα hα1
  have hPq := gaussPlusDecayOperator_tendsto hα hα1
  have hM := gaussMinusBranch_normalized_tendsto hα
  have hMq := gaussMinusDecayOperator_tendsto hα
  have h := (hP.mul hMq).sub (hM.mul hPq)
  simp only [one_mul, zero_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussPlusDecayOperator gaussMinusDecayOperator gaussBranchWronskian
  field_simp [(Real.rpow_pos_of_pos hx (alpha / 2)).ne']
  ring

theorem gaussRemainderWronskianPlus_hasDerivAt_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussRemainderWronskianPlus alpha) 0 x := by
  exact scaledWronskian_hasDerivAt_zero hx
    (gaussConnectionRemainder_hasDerivAt hα hα1 hx)
    (gaussConnectionRemainderD1_hasDerivAt hα hα1 hx)
    (gaussPlusBranch_hasDerivAt hα hα1 hx)
    (gaussPlusBranchD1_hasDerivAt hα hα1 hx)
    (gaussConnectionRemainder_ode hα hα1 hx)
    (gaussPlusBranch_ode hα hα1 hx)

theorem gaussRemainderWronskianMinus_hasDerivAt_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussRemainderWronskianMinus alpha) 0 x := by
  exact scaledWronskian_hasDerivAt_zero hx
    (gaussConnectionRemainder_hasDerivAt hα hα1 hx)
    (gaussConnectionRemainderD1_hasDerivAt hα hα1 hx)
    (gaussMinusBranch_hasDerivAt hα hx)
    (gaussMinusBranchD1_hasDerivAt hα hx)
    (gaussConnectionRemainder_ode hα hα1 hx)
    (gaussMinusBranch_ode hα hx)

theorem gaussBranchWronskian_hasDerivAt_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    HasDerivAt (gaussBranchWronskian alpha) 0 x := by
  exact scaledWronskian_hasDerivAt_zero hx
    (gaussPlusBranch_hasDerivAt hα hα1 hx)
    (gaussPlusBranchD1_hasDerivAt hα hα1 hx)
    (gaussMinusBranch_hasDerivAt hα hx)
    (gaussMinusBranchD1_hasDerivAt hα hx)
    (gaussPlusBranch_ode hα hα1 hx)
    (gaussMinusBranch_ode hα hx)

private theorem eq_limit_of_hasDerivAt_zero_on_Ioi {W : ℝ → ℝ} {L : ℝ}
    (hderiv : ∀ x : ℝ, 1 < x → HasDerivAt W 0 x)
    (hlim : Tendsto W atTop (nhds L)) :
    ∀ x : ℝ, 1 < x → W x = L := by
  intro x hx
  have hdiff : DifferentiableOn ℝ W (Set.Ioi 1) := by
    intro y hy
    exact (hderiv y hy).differentiableAt.differentiableWithinAt
  have hdz : Set.EqOn (deriv W) 0 (Set.Ioi 1) := by
    intro y hy
    exact (hderiv y hy).deriv
  have hconst : W x = W 2 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hdz hx (by norm_num)
  have hconstLim : Tendsto W atTop (nhds (W 2)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => W 2) atTop (nhds (W 2))).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact (isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hdz
      hy (by norm_num)).symm
  have htwo : W 2 = L := tendsto_nhds_unique hconstLim hlim
  exact hconst.trans htwo

theorem gaussRemainderWronskianPlus_eq_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    gaussRemainderWronskianPlus alpha x = 0 :=
  eq_limit_of_hasDerivAt_zero_on_Ioi
    (fun y hy => gaussRemainderWronskianPlus_hasDerivAt_zero hα hα1 hy)
    (gaussRemainderWronskianPlus_tendsto hα hα1) x hx

theorem gaussRemainderWronskianMinus_eq_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    gaussRemainderWronskianMinus alpha x = 0 :=
  eq_limit_of_hasDerivAt_zero_on_Ioi
    (fun y hy => gaussRemainderWronskianMinus_hasDerivAt_zero hα hα1 hy)
    (gaussRemainderWronskianMinus_tendsto hα hα1) x hx

theorem gaussBranchWronskian_eq_neg_alpha {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    gaussBranchWronskian alpha x = -alpha :=
  eq_limit_of_hasDerivAt_zero_on_Ioi
    (fun y hy => gaussBranchWronskian_hasDerivAt_zero hα hα1 hy)
    (gaussBranchWronskian_tendsto hα hα1) x hx

theorem gaussConnectionRemainder_eq_zero {alpha x : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) (hx : 1 < x) :
    gaussConnectionRemainder alpha x = 0 := by
  have hP := gaussRemainderWronskianPlus_eq_zero hα hα1 hx
  have hM := gaussRemainderWronskianMinus_eq_zero hα hα1 hx
  have hPM := gaussBranchWronskian_eq_neg_alpha hα hα1 hx
  unfold gaussRemainderWronskianPlus at hP
  unfold gaussRemainderWronskianMinus at hM
  unfold gaussBranchWronskian at hPM
  have hdet :
      x * gaussConnectionRemainder alpha x *
        (gaussPlusBranch alpha x * gaussMinusBranchD1 alpha x -
          gaussPlusBranchD1 alpha x * gaussMinusBranch alpha x) = 0 := by
    linear_combination gaussPlusBranch alpha x * hM - gaussMinusBranch alpha x * hP
  have hRalpha : gaussConnectionRemainder alpha x * (-alpha) = 0 := by
    calc
      gaussConnectionRemainder alpha x * (-alpha) =
          gaussConnectionRemainder alpha x *
            (x * (gaussPlusBranch alpha x * gaussMinusBranchD1 alpha x -
              gaussPlusBranchD1 alpha x * gaussMinusBranch alpha x)) := by rw [hPM]
      _ = x * gaussConnectionRemainder alpha x *
          (gaussPlusBranch alpha x * gaussMinusBranchD1 alpha x -
            gaussPlusBranchD1 alpha x * gaussMinusBranch alpha x) := by ring
      _ = 0 := hdet
  exact (mul_eq_zero.mp hRalpha).resolve_right (neg_ne_zero.mpr hα.ne')

/-- The fully proved negative-axis Gauss connection formula for the Euler/Beta continuation. -/
theorem negativeAxisConnectionFormula {alpha : ℝ}
    (hα : 0 < alpha) (hα1 : alpha < 1) :
    NegativeAxisConnectionFormula alpha := by
  intro x hx
  have hrem := gaussConnectionRemainder_eq_zero hα hα1 hx
  rw [negativeAxisConnectionRHS_eq_branches]
  unfold gaussConnectionRemainder at hrem
  linarith

end Hilbert16.Spikes
