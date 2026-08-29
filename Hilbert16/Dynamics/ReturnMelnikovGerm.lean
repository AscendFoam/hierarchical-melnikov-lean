import Hilbert16.Dynamics.SmoothLocalFlowFinite
import Hilbert16.Dynamics.ParametricIntegralC1
import Hilbert16.Dynamics.ChebyshevFlowIdentification

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set
open scoped Topology

namespace Hilbert16

/-!
# Germ identification of the genuine return Melnikov factor
-/

/-- The physical angular-time density is jointly `C¹` in positive energy
and angle, uniformly on the regular half-energy annulus. -/
theorem contDiffOn_chebyshevHamiltonianAngularTimeDensity_joint
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    ContDiffOn ℝ 1
      (fun z : ℝ × ℝ =>
        Spikes.chebyshevHamiltonianAngularTimeDensity
          n i j lambda z.1 z.2)
      (Set.Ioo (0 : ℝ) (1 / 2) ×ˢ (Set.univ : Set ℝ)) := by
  intro z hz
  have hh : 0 < z.1 := hz.1.1
  have hhHalf : z.1 < 1 / 2 := hz.1.2
  have hsqrtH : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => Real.sqrt (2 * w.1)) z := by
    have hinner : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => 2 * w.1) z := by
      fun_prop
    exact hinner.sqrt (by positivity)
  have hangle : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ => Spikes.chebyshevHamiltonianAngle i j w.2) z := by
    unfold Spikes.chebyshevHamiltonianAngle
    fun_prop
  have hcos : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        Real.cos (Spikes.chebyshevHamiltonianAngle i j w.2)) z :=
    Real.contDiff_cos.contDiffAt.comp z hangle
  have hsin : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        Real.sin (Spikes.chebyshevHamiltonianAngle i j w.2)) z :=
    Real.contDiff_sin.contDiffAt.comp z hangle
  let u : ℝ × ℝ → ℝ := fun w =>
    Real.sqrt (2 * w.1) *
      Real.cos (Spikes.chebyshevHamiltonianAngle i j w.2)
  let v : ℝ × ℝ → ℝ := fun w =>
    Real.sqrt (2 * w.1) / Real.sqrt lambda *
      Real.sin (Spikes.chebyshevHamiltonianAngle i j w.2)
  have huDiff : ContDiffAt ℝ 1 u z := by
    exact hsqrtH.mul hcos
  have hvDiff : ContDiffAt ℝ 1 v z := by
    exact (hsqrtH.div_const (Real.sqrt lambda)).mul hsin
  have hsqrtSq : Real.sqrt (2 * z.1) ^ 2 = 2 * z.1 :=
    Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (2 * z.1) := Real.sqrt_nonneg _
  have hsqrtLt : Real.sqrt (2 * z.1) < 1 := by
    nlinarith
  have huAbs : |u z| < 1 := by
    dsimp [u]
    calc
      |Real.sqrt (2 * z.1) *
          Real.cos (Spikes.chebyshevHamiltonianAngle i j z.2)| ≤
          Real.sqrt (2 * z.1) := by
        rw [abs_mul, abs_of_nonneg hsqrtNonneg]
        exact mul_le_of_le_one_right hsqrtNonneg (Real.abs_cos_le_one _)
      _ < 1 := hsqrtLt
  have hsqrtLambda : 1 ≤ Real.sqrt lambda := by
    exact Real.one_le_sqrt.mpr hlambda
  have hvAbs : |v z| < 1 := by
    dsimp [v]
    have hdivNonneg : 0 ≤ Real.sqrt (2 * z.1) / Real.sqrt lambda :=
      div_nonneg hsqrtNonneg (Real.sqrt_nonneg _)
    calc
      |Real.sqrt (2 * z.1) / Real.sqrt lambda *
          Real.sin (Spikes.chebyshevHamiltonianAngle i j z.2)| ≤
          Real.sqrt (2 * z.1) / Real.sqrt lambda := by
        rw [abs_mul, abs_of_nonneg hdivNonneg]
        exact mul_le_of_le_one_right hdivNonneg (Real.abs_sin_le_one _)
      _ ≤ Real.sqrt (2 * z.1) := by
        exact div_le_self hsqrtNonneg hsqrtLambda
      _ < 1 := hsqrtLt
  have hbranchU : ContDiffAt ℝ 1
      (fun w => Spikes.chebyshevInverseBranch n i (u w)) z :=
    (contDiffAt_chebyshevInverseBranch n i
      (ne_of_gt (abs_lt.mp huAbs).1)
      (ne_of_lt (abs_lt.mp huAbs).2)).comp z huDiff
  have hbranchV : ContDiffAt ℝ 1
      (fun w => Spikes.chebyshevInverseBranch n j (v w)) z :=
    (contDiffAt_chebyshevInverseBranch n j
      (ne_of_gt (abs_lt.mp hvAbs).1)
      (ne_of_lt (abs_lt.mp hvAbs).2)).comp z hvDiff
  have horbit : ContDiffAt ℝ 1
      (fun w : ℝ × ℝ =>
        Spikes.chebyshevHamiltonianAngularOrbit n i j lambda w.1 w.2) z := by
    have hpair := hbranchU.prodMk hbranchV
    simpa [Spikes.chebyshevHamiltonianAngularOrbit,
      Spikes.chebyshevCellOrbit, Spikes.chebyshevCellInverseMap,
      Spikes.ellipticOrbitUV, u, v] using hpair
  have hx : ContDiffAt ℝ 1 (fun w : ℝ × ℝ =>
      Spikes.chebyshevForwardDerivative n
        (Spikes.chebyshevHamiltonianAngularOrbit n i j lambda w.1 w.2).1) z :=
    (contDiff_realPolynomial_eval
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative).contDiffAt.comp z horbit.fst
  have hy : ContDiffAt ℝ 1 (fun w : ℝ × ℝ =>
      Spikes.chebyshevForwardDerivative n
        (Spikes.chebyshevHamiltonianAngularOrbit n i j lambda w.1 w.2).2) z :=
    (contDiff_realPolynomial_eval
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative).contDiffAt.comp z horbit.snd
  have hfactor : ContDiffAt ℝ 1 (fun w : ℝ × ℝ =>
      Spikes.chebyshevHamiltonianAngularTimeFactor n i j lambda w.1 w.2) z := by
    unfold Spikes.chebyshevHamiltonianAngularTimeFactor
    fun_prop
  have hfactorNe :
      Spikes.chebyshevHamiltonianAngularTimeFactor n i j lambda z.1 z.2 ≠ 0 :=
    (Spikes.chebyshevHamiltonianAngularTimeFactor_pos
      hn hi hj hlambda hh.le hhHalf).ne'
  unfold Spikes.chebyshevHamiltonianAngularTimeDensity
  exact (hfactor.inv hfactorNe).contDiffWithinAt

/-- The positive section period varies `C¹` with energy at every regular
positive level. -/
theorem contDiffAt_chebyshevHamiltonianSectionPeriod
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda)
    (hh : 0 < h) (hhHalf : h < 1 / 2) :
    ContDiffAt ℝ 1
      (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda) h := by
  let f : ℝ → ℝ → ℝ := fun e t =>
    Spikes.chebyshevHamiltonianAngularTimeDensity n i j lambda e t
  let U : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (1 / 2) ×ˢ Set.univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hf : ContDiffOn ℝ 1 f.uncurry U := by
    change ContDiffOn ℝ 1
      (fun z : ℝ × ℝ =>
        Spikes.chebyshevHamiltonianAngularTimeDensity
          n i j lambda z.1 z.2) U
    exact contDiffOn_chebyshevHamiltonianAngularTimeDensity_joint
      hn hi hj hlambda
  let a := Spikes.chebyshevHamiltonianSectionAngularStart i j
  have hsegment (b : ℝ) :
      ({h} : Set ℝ) ×ˢ Set.uIcc 0 b ⊆ U := by
    rintro ⟨e, t⟩ ⟨he, ht⟩
    change e = h at he
    subst e
    exact ⟨⟨hh, hhHalf⟩, Set.mem_univ t⟩
  have hleft := contDiffAt_parametricIntervalIntegral_const_of_contDiffOn
    f 0 (a + 2 * Real.pi) hU hf (hsegment (a + 2 * Real.pi))
  have hright := contDiffAt_parametricIntervalIntegral_const_of_contDiffOn
    f 0 a hU hf (hsegment a)
  change ContDiffAt ℝ 1
    (fun e => (∫ t in 0..a + 2 * Real.pi, f e t) -
      ∫ t in 0..a, f e t) h
  exact hleft.sub hright

/-- For a return setup built from the explicit unperturbed period, its
zero-parameter Melnikov factor agrees on a whole energy germ with the
compiled first Melnikov displacement.  This is the equality needed to
transport the nonzero energy derivative, not only zerohood. -/
theorem C1LocalFlow.eventually_chebyshevReturnSetupOfSectionPeriod_melnikov_eq_first
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2)
    (hX : ∀ z : PhaseSpace,
      X 0 z = chebyshevPhaseHamiltonianVector n lambda z)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ)
        (Spikes.chebyshevHamiltonianSectionPeriod n i j lambda h),
      ((0, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain)
    {P : ℝ × ℝ → ℝ} (hP : Continuous P) :
    let S := Phi.chebyshevReturnSetupOfSectionPeriod
      hn hi hj hlambda hh hhHalf hX hsegment
    (fun e => S.melnikovIntegral (chebyshevEnergyProduction n P) (0, e)) =ᶠ[𝓝 h]
      (fun e => Spikes.chebyshevFirstMelnikovDisplacement n i j P lambda e) := by
  dsimp only
  let period : ℝ → ℝ :=
    Spikes.chebyshevHamiltonianSectionPeriod n i j lambda
  let S := Phi.chebyshevReturnSetupOfSectionPeriod
    hn hi hj hlambda hh hhHalf hX hsegment
  let scaledInput : ℝ × ℝ → ParameterPhaseSpace × ℝ := fun er =>
    ((0, chebyshevPhaseSectionPoint n i j lambda er.1),
      period er.1 * er.2)
  have hperiodDiff : ContDiffAt ℝ 1 period h := by
    exact contDiffAt_chebyshevHamiltonianSectionPeriod
      hn hi hj hlambda hh hhHalf
  have hscaledDiff (r : ℝ) : ContDiffAt ℝ 1 scaledInput (h, r) := by
    have hsection := contDiffAt_chebyshevPhaseSectionPoint
      n i j lambda hh hhHalf
    have hpcomp : ContDiffAt ℝ 1
        (fun er : ℝ × ℝ => period er.1) (h, r) :=
      hperiodDiff.comp (h, r) contDiffAt_fst
    have hzero : ContDiffAt ℝ 1 (fun _ : ℝ × ℝ => (0 : ℝ)) (h, r) :=
      contDiffAt_const
    dsimp [scaledInput]
    exact (hzero.prodMk
      (hsection.comp (h, r) contDiffAt_fst)).prodMk
        (hpcomp.mul contDiffAt_snd)
  have hperiodPos : 0 < period h :=
    Spikes.chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda hh.le hhHalf
  have hscaledEventually : ∀ᶠ e in 𝓝 h,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, scaledInput (e, r) ∈ Phi.domain := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have htime : period h * r ∈ Set.Icc (0 : ℝ) (period h) := by
      exact ⟨mul_nonneg hperiodPos.le hr.1,
        (mul_le_mul_of_nonneg_left hr.2 hperiodPos.le).trans_eq (mul_one _)⟩
    have hbaseDomain : scaledInput (h, r) ∈ Phi.domain := by
      simpa [scaledInput] using hsegment (period h * r) htime
    exact (hscaledDiff r).continuousAt.eventually_mem
      (Phi.isOpen_domain.mem_nhds hbaseDomain)
  have hposEventually : ∀ᶠ e in 𝓝 h, 0 < e :=
    continuousAt_const.eventually_lt continuousAt_id hh
  have hhalfEventually : ∀ᶠ e in 𝓝 h, e < 1 / 2 :=
    continuousAt_id.eventually_lt continuousAt_const hhHalf
  let candidate : ℝ → ((ℝ × ℝ) × ℝ) := fun e =>
    ((0, e), period e)
  have hcandidateDiff : ContDiffAt ℝ 1 candidate h := by
    exact (contDiffAt_const.prodMk contDiffAt_id).prodMk hperiodDiff
  have hcandidateAt : candidate h = S.base := by
    rfl
  have hcandidateTendsto : Tendsto candidate (𝓝 h) (𝓝 S.base) := by
    rw [← hcandidateAt]
    exact hcandidateDiff.continuousAt
  have hunique : ∀ᶠ e in 𝓝 h,
      (fun xt => chebyshevSectionCoordinate n j
        (Phi.chebyshevByEnergy n i j lambda xt)) (candidate e) =
          (fun xt => chebyshevSectionCoordinate n j
            (Phi.chebyshevByEnergy n i j lambda xt)) S.base ↔
        S.returnTime.time (0, e) = period e := by
    exact hcandidateTendsto.eventually S.returnTime.eventually_unique
  filter_upwards [hscaledEventually, hposEventually, hhalfEventually, hunique] with
      e hscaled he hhalf hu
  have hsegmentE : ∀ t ∈ Set.Icc (0 : ℝ) (period e),
      ((0, chebyshevPhaseSectionPoint n i j lambda e), t) ∈ Phi.domain := by
    intro t ht
    let r : ℝ := t / period e
    have hperiodEPos : 0 < period e :=
      Spikes.chebyshevHamiltonianSectionPeriod_pos
        hn hi hj hlambda he.le hhalf
    have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg ht.1 hperiodEPos.le,
        (div_le_one hperiodEPos).2 ht.2⟩
    have hm : period e * r = t := by
      exact mul_div_cancel₀ t hperiodEPos.ne'
    simpa [scaledInput, r, hm] using hscaled r hr
  have hreturnsE := Phi.chebyshevUnperturbed_returns_after_sectionPeriod
    hn hi hj hlambda he hhalf hX hsegmentE
  have hlevel :
      (fun xt => chebyshevSectionCoordinate n j
        (Phi.chebyshevByEnergy n i j lambda xt)) (candidate e) =
          (fun xt => chebyshevSectionCoordinate n j
            (Phi.chebyshevByEnergy n i j lambda xt)) S.base := by
    change chebyshevSectionCoordinate n j
        (Phi.chebyshevByEnergy n i j lambda ((0, e), period e)) =
      chebyshevSectionCoordinate n j
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda
          ((0, S.h₀), S.T₀))
    rw [hreturnsE, S.returns_to_base]
    rw [chebyshevPhaseSectionPoint_on_section]
    exact (chebyshevPhaseSectionPoint_on_section
      S.n S.i S.j S.lambda S.h₀).symm
  have htime : S.returnTime.time (0, e) = period e := hu.mp hlevel
  have htraj := Phi.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc
    hn hi hj hlambda he hhalf hX hsegmentE
  have hperiodEPos : 0 < period e :=
    Spikes.chebyshevHamiltonianSectionPeriod_pos
      hn hi hj hlambda he.le hhalf
  have hpdy : S.unperturbedTimePdy P e =
      Spikes.chebyshevHamiltonianSectionTimePdy
        hn hi hj P hlambda he.le hhalf := by
    unfold ChebyshevReturnSetup.unperturbedTimePdy
      Spikes.chebyshevHamiltonianSectionTimePdy
    rw [htime]
    apply Spikes.parameterizedPdy_congr
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) (period e) := by
        rw [Set.uIcc_of_le hperiodEPos.le] at ht
        exact ht
      simpa [S, period, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod] using
        htraj htIcc
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) (period e) := by
        rw [Set.uIcc_of_le hperiodEPos.le] at ht
        exact ht
      have hcurve := htraj htIcc
      simp [S, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod,
        hcurve]
  calc
    S.melnikovIntegral (chebyshevEnergyProduction n P) (0, e) =
        -S.unperturbedTimePdy P e := by
      simpa [S, C1LocalFlow.chebyshevReturnSetupOfSectionPeriod] using
        S.melnikovIntegral_zero_eq_neg_unperturbedTimePdy P e
    _ = -Spikes.chebyshevHamiltonianSectionTimePdy
          hn hi hj P hlambda he.le hhalf := by rw [hpdy]
    _ = -Spikes.chebyshevHamiltonianAngularPdy n i j P lambda e := by
      rw [Spikes.chebyshevHamiltonianSectionTimePdy_eq_angularPdy
        hn hi hj hP hlambda he.le hhalf]
    _ = Spikes.chebyshevFirstMelnikovDisplacement n i j P lambda e := by
      exact (Spikes.chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianAngularPdy
        n i j P lambda e).symm

end Hilbert16
