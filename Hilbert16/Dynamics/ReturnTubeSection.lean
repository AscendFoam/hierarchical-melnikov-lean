import Hilbert16.Dynamics.ChebyshevAngularSection
import Hilbert16.Dynamics.ReturnIsolation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Filter Set
open scoped Topology

/-!
# Identification of the angular cut with the local return section
-/

/-- Near the marked positive-ray point, the signed forward-coordinate ray
is exactly the energy-parametrized Chebyshev Poincare section. -/
theorem eventually_eq_chebyshevPhaseSectionPoint_of_positiveRay
    {n i j : ℕ} (hn : n ≠ 0) (_hi : i < n) (_hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) :
    ∀ᶠ z in 𝓝 (chebyshevPhaseSectionPoint n i j lambda h),
      chebyshevSignedForwardY n i j lambda z = 0 →
      0 < chebyshevForwardX n z →
        z = chebyshevPhaseSectionPoint n i j lambda
          (chebyshevPhaseEnergy n lambda z) := by
  let p : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (n : ℤ)
  let base : PhaseSpace := chebyshevPhaseSectionPoint n i j lambda h
  let x₀ : ℝ := (phaseSpaceProdEquiv base).1
  let y₀ : ℝ := (phaseSpaceProdEquiv base).2
  let energy : PhaseSpace → ℝ := chebyshevPhaseEnergy n lambda
  let sec : PhaseSpace → PhaseSpace := fun z =>
    chebyshevPhaseSectionPoint n i j lambda (energy z)
  let zx : PhaseSpace → ℝ := fun z => (phaseSpaceProdEquiv z).1
  let zy : PhaseSpace → ℝ := fun z => (phaseSpaceProdEquiv z).2
  let sx : PhaseSpace → ℝ := fun z => (phaseSpaceProdEquiv (sec z)).1
  let sy : PhaseSpace → ℝ := fun z => (phaseSpaceProdEquiv (sec z)).2
  have hbaseEnergy : energy base = h := by
    exact chebyshevPhaseSectionPoint_energy_eq hn hlambda hh.le hhHalf.le
  have hsqrtPos : 0 < Real.sqrt (2 * h) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) hh)
  have hsqrtLt : Real.sqrt (2 * h) < 1 := by
    have hsquare : Real.sqrt (2 * h) ^ 2 = 2 * h :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (2 * h)]
  have hx₀ : x₀ = Spikes.chebyshevInverseBranch n i (Real.sqrt (2 * h)) := by
    simpa [x₀, base] using
      chebyshevPhaseSectionPoint_fst_eq_inverseBranch n i j lambda h
  have hy₀ : y₀ = Spikes.chebyshevInverseBranch n j 0 := by
    simp [y₀, base, chebyshevPhaseSectionPoint, chebyshevPhaseOrbit,
      Spikes.chebyshevCellOrbit, Spikes.chebyshevCellInverseMap,
      Spikes.ellipticOrbitUV]
  have hpXne : p.derivative.eval x₀ ≠ 0 := by
    have hprod := Spikes.chebyshevForwardDerivative_mul_inverseDeriv_eq_one
      (i := i) hn (u := Real.sqrt (2 * h)) (by
        rw [abs_of_pos hsqrtPos]
        exact hsqrtLt)
    have hforward : Spikes.chebyshevForwardDerivative n
        (Spikes.chebyshevInverseBranch n i (Real.sqrt (2 * h))) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hprod
      norm_num at hprod
    simpa [Spikes.chebyshevForwardDerivative, p, hx₀] using hforward
  have hpYne : p.derivative.eval y₀ ≠ 0 := by
    have hprod := Spikes.chebyshevForwardDerivative_mul_inverseDeriv_eq_one
      (i := j) hn (u := (0 : ℝ)) (by norm_num)
    have hforward : Spikes.chebyshevForwardDerivative n
        (Spikes.chebyshevInverseBranch n j 0) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hprod
      norm_num at hprod
    simpa [Spikes.chebyshevForwardDerivative, p, hy₀] using hforward
  have hpXstrict : HasStrictDerivAt (fun x : ℝ => p.eval x)
      (p.derivative.eval x₀) x₀ := p.hasStrictDerivAt x₀
  have hpYstrict : HasStrictDerivAt (fun y : ℝ => p.eval y)
      (p.derivative.eval y₀) y₀ := p.hasStrictDerivAt y₀
  have hzx : Tendsto zx (𝓝 base) (𝓝 x₀) := by
    exact phaseSpaceProdEquiv.continuous.continuousAt.fst
  have hzy : Tendsto zy (𝓝 base) (𝓝 y₀) := by
    exact phaseSpaceProdEquiv.continuous.continuousAt.snd
  have henergy : Tendsto energy (𝓝 base) (𝓝 h) := by
    have hc : ContinuousAt (chebyshevPhaseEnergy n lambda) base :=
      (contDiff_chebyshevPhaseEnergy n lambda).continuous.continuousAt
    rw [← hbaseEnergy]
    change ContinuousAt energy base
    simpa only [energy] using hc
  have hsec : Tendsto sec (𝓝 base) (𝓝 base) := by
    have hs := (contDiffAt_chebyshevPhaseSectionPoint n i j lambda hh hhHalf).continuousAt
    have hcomp : Tendsto
        (chebyshevPhaseSectionPoint n i j lambda ∘ energy)
        (𝓝 base) (𝓝 (chebyshevPhaseSectionPoint n i j lambda h)) :=
      hs.tendsto.comp henergy
    simpa [sec, base, Function.comp_def] using hcomp
  have hsx : Tendsto sx (𝓝 base) (𝓝 x₀) := by
    exact phaseSpaceProdEquiv.continuous.continuousAt.fst.tendsto.comp hsec
  have hsy : Tendsto sy (𝓝 base) (𝓝 y₀) := by
    exact phaseSpaceProdEquiv.continuous.continuousAt.snd.tendsto.comp hsec
  have henergyRange : ∀ᶠ z in 𝓝 base,
      0 < energy z ∧ energy z < 1 / 2 :=
    (henergy.eventually (eventually_gt_nhds hh)).and
      (henergy.eventually (eventually_lt_nhds hhHalf))
  have hzxInv : ∀ᶠ z in 𝓝 base,
      hpXstrict.localInverse _ _ _ hpXne (p.eval (zx z)) = zx z :=
    hzx.eventually (hpXstrict.eventually_left_inverse hpXne)
  have hsxInv : ∀ᶠ z in 𝓝 base,
      hpXstrict.localInverse _ _ _ hpXne (p.eval (sx z)) = sx z :=
    hsx.eventually (hpXstrict.eventually_left_inverse hpXne)
  have hzyInv : ∀ᶠ z in 𝓝 base,
      hpYstrict.localInverse _ _ _ hpYne (p.eval (zy z)) = zy z :=
    hzy.eventually (hpYstrict.eventually_left_inverse hpYne)
  have hsyInv : ∀ᶠ z in 𝓝 base,
      hpYstrict.localInverse _ _ _ hpYne (p.eval (sy z)) = sy z :=
    hsy.eventually (hpYstrict.eventually_left_inverse hpYne)
  filter_upwards [henergyRange, hzxInv, hsxInv, hzyInv, hsyInv]
    with z he hzxi hsxi hzyi hsyi
  intro hyRay hxPos
  let e := energy z
  have hsqrtEPos : 0 < Real.sqrt (2 * e) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) he.1)
  have hsqrtELe : Real.sqrt (2 * e) ≤ 1 := by
    have hsquare : Real.sqrt (2 * e) ^ 2 = 2 * e :=
      Real.sq_sqrt (mul_nonneg (by norm_num) he.1.le)
    have hsqrtNonneg := Real.sqrt_nonneg (2 * e)
    nlinarith
  have hcoeffNe :
      -Spikes.chebyshevCellJacobianOrientation i j * Real.sqrt lambda ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr
      (Spikes.chebyshevCellJacobianOrientation_ne_zero i j))
      (Real.sqrt_ne_zero'.mpr (lt_of_lt_of_le zero_lt_one hlambda))
  have hpzy : p.eval (zy z) = 0 := by
    change (-Spikes.chebyshevCellJacobianOrientation i j * Real.sqrt lambda) *
      p.eval (zy z) = 0 at hyRay
    exact (mul_eq_zero.mp hyRay).resolve_left hcoeffNe
  have hpsy : p.eval (sy z) = 0 := by
    simp [sy, sec, energy, p, chebyshevPhaseSectionPoint,
      chebyshevPhaseOrbit, Spikes.chebyshevCellOrbit,
      Spikes.chebyshevCellInverseMap, Spikes.ellipticOrbitUV,
      Spikes.eval_chebyshevInverseBranch hn]
  have hyEq : zy z = sy z := by
    calc
      zy z = hpYstrict.localInverse _ _ _ hpYne (p.eval (zy z)) := hzyi.symm
      _ = hpYstrict.localInverse _ _ _ hpYne (p.eval (sy z)) := by rw [hpzy, hpsy]
      _ = sy z := hsyi
  have hpyEq : p.eval (zy z) = p.eval (sy z) := congrArg p.eval hyEq
  have hpSx : p.eval (sx z) = Real.sqrt (2 * e) := by
    simpa [sx, sec, energy, e, p] using
      chebyshevPhaseSectionPoint_forwardCoordinate_eq
        (n := n) (i := i) (j := j) hn he.1.le he.2.le
  have hsectionEnergy : chebyshevPhaseEnergy n lambda (sec z) = e := by
    exact chebyshevPhaseSectionPoint_energy_eq hn hlambda he.1.le he.2.le
  have hsquares : p.eval (zx z) ^ 2 = p.eval (sx z) ^ 2 := by
    have hzEnergy : chebyshevPhaseEnergy n lambda z = e := rfl
    unfold chebyshevPhaseEnergy Spikes.chebyshevHamiltonian at hzEnergy hsectionEnergy
    dsimp [energy, e, zx, zy, sx, sy, sec, p] at hzEnergy hsectionEnergy hpyEq ⊢
    have hpySqEq := congrArg (fun y : ℝ => y ^ 2) hpyEq
    have henergyEq := hzEnergy.trans hsectionEnergy.symm
    have hnumEq :
        p.eval (zx z) ^ 2 + lambda * p.eval (zy z) ^ 2 =
          p.eval (sx z) ^ 2 + lambda * p.eval (sy z) ^ 2 := by
      dsimp [p, zx, zy, sx, sy, sec, energy] at henergyEq ⊢
      linarith
    exact add_left_cancel (by
      calc
        lambda * p.eval (zy z) ^ 2 + p.eval (zx z) ^ 2 =
            p.eval (zx z) ^ 2 + lambda * p.eval (zy z) ^ 2 := by ring
        _ = p.eval (sx z) ^ 2 + lambda * p.eval (sy z) ^ 2 := hnumEq
        _ = lambda * p.eval (zy z) ^ 2 + p.eval (sx z) ^ 2 := by
          rw [hpySqEq]
          ring)
  have hpzxPos : 0 < p.eval (zx z) := by
    simpa [chebyshevForwardX, zx, p] using hxPos
  have hxEval : p.eval (zx z) = p.eval (sx z) := by
    rw [hpSx]
    nlinarith
  have hxEq : zx z = sx z := by
    calc
      zx z = hpXstrict.localInverse _ _ _ hpXne (p.eval (zx z)) := hzxi.symm
      _ = hpXstrict.localInverse _ _ _ hpXne (p.eval (sx z)) := by rw [hxEval]
      _ = sx z := hsxi
  apply phaseSpaceProdEquiv.injective
  apply Prod.ext
  · exact hxEq
  · exact hyEq

/-- On the explicit unperturbed oval, the positive forward-coordinate ray
has exactly the marked section point as its intersection. -/
theorem chebyshevPhaseOrbit_eq_sectionPoint_of_positiveRay
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhHalf : h < 1 / 2)
    (hy : chebyshevSignedForwardY n i j lambda
      (chebyshevPhaseOrbit n i j lambda h t) = 0)
    (hx : 0 < chebyshevForwardX n
      (chebyshevPhaseOrbit n i j lambda h t)) :
    chebyshevPhaseOrbit n i j lambda h t =
      chebyshevPhaseSectionPoint n i j lambda h := by
  have henergy := Spikes.ellipticOrbitUV_energy_eq
    (lt_of_lt_of_le zero_lt_one hlambda) hh.le (t := t)
  have hstrict : |(Spikes.ellipticOrbitUV lambda h t).1| < 1 ∧
      |(Spikes.ellipticOrbitUV lambda h t).2| < 1 := by
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (Spikes.ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) *
          (Spikes.ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (Spikes.ellipticOrbitUV lambda h t).1]
  have hevalX := Spikes.eval_chebyshevInverseBranch
    (i := i) hn hstrict.1.le
  have hevalY := Spikes.eval_chebyshevInverseBranch
    (i := j) hn hstrict.2.le
  have hcoeffNe :
      -Spikes.chebyshevCellJacobianOrientation i j * Real.sqrt lambda ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr
      (Spikes.chebyshevCellJacobianOrientation_ne_zero i j))
      (Real.sqrt_ne_zero'.mpr (lt_of_lt_of_le zero_lt_one hlambda))
  have hvzero : (Spikes.ellipticOrbitUV lambda h t).2 = 0 := by
    simp only [chebyshevSignedForwardY,
      phaseSpaceProdEquiv_chebyshevPhaseOrbit,
      Spikes.chebyshevCellOrbit_snd] at hy
    rw [hevalY] at hy
    exact (mul_eq_zero.mp hy).resolve_left hcoeffNe
  have hupos : 0 < (Spikes.ellipticOrbitUV lambda h t).1 := by
    simp only [chebyshevForwardX, phaseSpaceProdEquiv_chebyshevPhaseOrbit,
      Spikes.chebyshevCellOrbit_fst] at hx
    rw [hevalX] at hx
    exact hx
  have husqrt : (Spikes.ellipticOrbitUV lambda h t).1 =
      Real.sqrt (2 * h) := by
    have hsquare : Real.sqrt (2 * h) ^ 2 = 2 * h :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hh.le)
    have hsqrtNonneg := Real.sqrt_nonneg (2 * h)
    rw [hvzero] at henergy
    norm_num at henergy
    nlinarith
  have huvEq : Spikes.ellipticOrbitUV lambda h t =
      Spikes.ellipticOrbitUV lambda h 0 := by
    apply Prod.ext
    · simpa [Spikes.ellipticOrbitUV] using husqrt
    · simpa [Spikes.ellipticOrbitUV] using hvzero
  apply phaseSpaceProdEquiv.injective
  simp only [phaseSpaceProdEquiv_chebyshevPhaseOrbit,
    chebyshevPhaseSectionPoint]
  exact congrArg (Spikes.chebyshevCellInverseMap n i j) huvEq

theorem continuous_chebyshevForwardX (n : ℕ) :
    Continuous (chebyshevForwardX n) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hp : Continuous (fun x : ℝ => p.eval x) :=
    (contDiff_realPolynomial_eval p).continuous
  unfold chebyshevForwardX
  fun_prop

theorem continuous_chebyshevSignedForwardY
    (n i j : ℕ) (lambda : ℝ) :
    Continuous (chebyshevSignedForwardY n i j lambda) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hp : Continuous (fun y : ℝ => p.eval y) :=
    (contDiff_realPolynomial_eval p).continuous
  unfold chebyshevSignedForwardY
  fun_prop

/-- Any prescribed open energy neighborhood of the base root determines an
open tube around the whole unperturbed oval whose positive angular cut is
localized to that energy-parametrized section neighborhood. -/
theorem exists_chebyshevLocalizedPositiveRayTube
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) {V : Set ℝ} (hVopen : IsOpen V) (hhV : h ∈ V) :
    ∃ U : Set PhaseSpace, IsOpen U ∧
      Set.range (chebyshevPhaseOrbit n i j lambda h) ⊆ U ∧
      ∀ z ∈ U,
        chebyshevSignedForwardY n i j lambda z = 0 →
        0 < chebyshevForwardX n z →
          chebyshevPhaseEnergy n lambda z ∈ V ∧
            z = chebyshevPhaseSectionPoint n i j lambda
              (chebyshevPhaseEnergy n lambda z) := by
  let base := chebyshevPhaseSectionPoint n i j lambda h
  have hidentify := eventually_eq_chebyshevPhaseSectionPoint_of_positiveRay
    hn hi hj hlambda hh hhHalf
  have henergyV : ∀ᶠ z in 𝓝 base,
      chebyshevPhaseEnergy n lambda z ∈ V := by
    have hcont : ContinuousAt (chebyshevPhaseEnergy n lambda) base :=
      (contDiff_chebyshevPhaseEnergy n lambda).continuous.continuousAt
    have hbaseEnergy : chebyshevPhaseEnergy n lambda base = h :=
      chebyshevPhaseSectionPoint_energy_eq hn hlambda hh.le hhHalf.le
    have htend : Tendsto (chebyshevPhaseEnergy n lambda) (𝓝 base) (𝓝 h) := by
      rw [← hbaseEnergy]
      exact hcont
    exact htend.eventually (hVopen.mem_nhds hhV)
  have hlocal : ∀ᶠ z in 𝓝 base,
      (chebyshevSignedForwardY n i j lambda z = 0 →
        0 < chebyshevForwardX n z →
          z = chebyshevPhaseSectionPoint n i j lambda
            (chebyshevPhaseEnergy n lambda z)) ∧
      chebyshevPhaseEnergy n lambda z ∈ V :=
    hidentify.and henergyV
  rcases mem_nhds_iff.mp hlocal with ⟨N, hNsub, hNopen, hbaseN⟩
  let U : Set PhaseSpace :=
    {z | chebyshevSignedForwardY n i j lambda z ≠ 0} ∪
      {z | chebyshevForwardX n z < 0} ∪ N
  have hUopen : IsOpen U := by
    have hopenY : IsOpen
        {z | chebyshevSignedForwardY n i j lambda z ≠ 0} := by
      exact isOpen_ne.preimage
        (continuous_chebyshevSignedForwardY n i j lambda)
    have hopenX : IsOpen {z | chebyshevForwardX n z < 0} := by
      exact isOpen_Iio.preimage (continuous_chebyshevForwardX n)
    exact (hopenY.union hopenX).union hNopen
  have hcarrier : Set.range (chebyshevPhaseOrbit n i j lambda h) ⊆ U := by
    rintro z ⟨t, rfl⟩
    by_cases hyzero : chebyshevSignedForwardY n i j lambda
        (chebyshevPhaseOrbit n i j lambda h t) = 0
    · by_cases hxneg : chebyshevForwardX n
          (chebyshevPhaseOrbit n i j lambda h t) < 0
      · exact Or.inl (Or.inr hxneg)
      · have hradius := chebyshevForwardRadiusSq_phaseOrbit_eq
          hn hlambda hh.le hhHalf (i := i) (j := j) (t := t)
        have hxpos : 0 < chebyshevForwardX n
            (chebyshevPhaseOrbit n i j lambda h t) := by
          unfold chebyshevForwardRadiusSq at hradius
          rw [hyzero] at hradius
          norm_num at hradius
          have hnonneg := le_of_not_gt hxneg
          nlinarith
        have heq := chebyshevPhaseOrbit_eq_sectionPoint_of_positiveRay
          hn hlambda hh hhHalf hyzero hxpos
        refine Or.inr ?_
        rw [heq]
        simpa [base] using hbaseN
    · exact Or.inl (Or.inl hyzero)
  refine ⟨U, hUopen, hcarrier, ?_⟩
  intro z hz hyzero hxpos
  have hzN : z ∈ N := by
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact (hz hyzero).elim
      · exact (not_lt_of_ge hxpos.le hz).elim
    · exact hz
  have hloc := hNsub hzN
  exact ⟨hloc.2, hloc.1 hyzero hxpos⟩

/-- The whole local return branch, not only its fixed points, lands on the
positive energy-parametrized section. -/
theorem ChebyshevReturnSetup.eventually_returnPoint_eq_sectionPoint_energyReturnMap
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      S.returnPoint muh = chebyshevPhaseSectionPoint
        S.n S.i S.j S.lambda (S.energyReturnMap muh.1 muh.2) := by
  let basePoint := chebyshevPhaseSectionPoint S.n S.i S.j S.lambda S.h₀
  have hbaseFlow : S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda S.base =
      basePoint := by
    simpa [ChebyshevReturnSetup.base, basePoint] using S.returns_to_base
  have hreturnAt : S.returnPoint (0, S.h₀) = basePoint := by
    change S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda
      ((0, S.h₀), S.returnTime.time (0, S.h₀)) = basePoint
    have htime : S.returnTime.time (0, S.h₀) = S.T₀ := by
      simpa [ChebyshevReturnSetup.base] using S.returnTime.time_at
    rw [htime]
    simpa [ChebyshevReturnSetup.base] using hbaseFlow
  have hretTend : Tendsto S.returnPoint
      (𝓝 ((0 : ℝ), S.h₀)) (𝓝 basePoint) := by
    have hret := S.returnTime.contDiffAt_returnPoint S.contDiffAt_flowByEnergy
    have hret' : ContinuousAt S.returnPoint (0, S.h₀) := by
      change ContinuousAt
        (S.returnTime.returnPoint
          (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)) (0, S.h₀)
      simpa [ChebyshevReturnSetup.base] using hret.continuousAt
    rw [← hreturnAt]
    exact hret'
  have hidentify := hretTend.eventually
    (eventually_eq_chebyshevPhaseSectionPoint_of_positiveRay
      S.n_ne_zero S.i_lt S.j_lt S.lambda_ge_one S.h₀_pos S.h₀_lt_half)
  have hlevel : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      chebyshevSectionCoordinate S.n S.j (S.returnPoint muh) = 0 := by
    have hlocal := S.returnTime.eventually_returnPoint_level
      (flow := S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda)
      (sectionFn := chebyshevSectionCoordinate S.n S.j)
    have hbaseSection : chebyshevSectionCoordinate S.n S.j
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda S.base) = 0 := by
      rw [hbaseFlow]
      exact chebyshevPhaseSectionPoint_on_section _ _ _ _ _
    filter_upwards [hlocal] with muh hmuh
    exact hmuh.trans hbaseSection
  have hyzero : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      chebyshevSignedForwardY S.n S.i S.j S.lambda (S.returnPoint muh) = 0 := by
    filter_upwards [hlevel] with muh hmuh
    have hy : (phaseSpaceProdEquiv (S.returnPoint muh)).2 =
        Spikes.chebyshevInverseBranch S.n S.j 0 := by
      unfold chebyshevSectionCoordinate at hmuh
      linarith
    simp only [chebyshevSignedForwardY]
    rw [hy, Spikes.eval_chebyshevInverseBranch S.n_ne_zero (by norm_num)]
    ring
  have hbaseForward : 0 < chebyshevForwardX S.n basePoint := by
    have heval : chebyshevForwardX S.n basePoint = Real.sqrt (2 * S.h₀) := by
      simpa [chebyshevForwardX, basePoint] using
        (chebyshevPhaseSectionPoint_forwardCoordinate_eq
          (n := S.n) (i := S.i) (j := S.j)
          (lambda := S.lambda) (h := S.h₀)
          S.n_ne_zero S.h₀_pos.le S.h₀_lt_half.le)
    rw [heval]
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) S.h₀_pos)
  have hxpos : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      0 < chebyshevForwardX S.n (S.returnPoint muh) := by
    have htend := (continuous_chebyshevForwardX S.n).continuousAt.tendsto.comp hretTend
    exact htend.eventually (eventually_gt_nhds hbaseForward)
  filter_upwards [hidentify, hyzero, hxpos] with muh hident hy hx
  have heq := hident hy hx
  rw [S.energyReturnMap_eq_returnCoordinate]
  exact heq

/-- The nearby local return branch lands on the positive angular ray.  This
is exported separately because iteration arguments need the ray property
before they know that the returned energy stays in their chosen interval. -/
theorem ChebyshevReturnSetup.eventually_returnPoint_mem_chebyshevPositiveRay
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X) :
    ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      chebyshevSignedForwardY S.n S.i S.j S.lambda (S.returnPoint muh) = 0 ∧
        0 < chebyshevForwardX S.n (S.returnPoint muh) := by
  have hendpoint := S.eventually_returnPoint_eq_sectionPoint_energyReturnMap
  have hmapCont : ContDiffAt ℝ 1
      (fun muh : ℝ × ℝ => S.energyReturnMap muh.1 muh.2)
      (0, S.h₀) := by
    unfold ChebyshevReturnSetup.energyReturnMap
    exact contDiffAt_snd.add S.contDiffAt_energyDisplacement
  have hmapAt : S.energyReturnMap 0 S.h₀ = S.h₀ := by
    unfold ChebyshevReturnSetup.energyReturnMap
    rw [S.energyDisplacement_zero_at_base]
    ring
  have hmapRange : ∀ᶠ muh in 𝓝 ((0 : ℝ), S.h₀),
      0 < S.energyReturnMap muh.1 muh.2 ∧
        S.energyReturnMap muh.1 muh.2 < 1 / 2 := by
    have htend : Tendsto
        (fun muh : ℝ × ℝ => S.energyReturnMap muh.1 muh.2)
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 S.h₀) := by
      have hc := hmapCont.continuousAt
      change Tendsto
        (fun muh : ℝ × ℝ => S.energyReturnMap muh.1 muh.2)
        (𝓝 ((0 : ℝ), S.h₀)) (𝓝 (S.energyReturnMap 0 S.h₀)) at hc
      rw [hmapAt] at hc
      exact hc
    exact (htend.eventually (eventually_gt_nhds S.h₀_pos)).and
      (htend.eventually (eventually_lt_nhds S.h₀_lt_half))
  filter_upwards [hendpoint, hmapRange] with muh heq he
  rw [heq]
  constructor
  · simp [chebyshevSignedForwardY, chebyshevPhaseSectionPoint,
      chebyshevPhaseOrbit, Spikes.chebyshevCellOrbit,
      Spikes.chebyshevCellInverseMap, Spikes.ellipticOrbitUV,
      Spikes.eval_chebyshevInverseBranch S.n_ne_zero]
  · unfold chebyshevForwardX
    rw [chebyshevPhaseSectionPoint_forwardCoordinate_eq
      S.n_ne_zero he.1.le he.2.le]
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) he.1)

end Hilbert16
