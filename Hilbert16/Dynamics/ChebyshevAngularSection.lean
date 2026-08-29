import Hilbert16.Dynamics.AngularSection
import Hilbert16.Dynamics.PerturbedEnergy
import Hilbert16.Dynamics.ThreeAdicOrbitGeometry
import Hilbert16.Spikes.ChebyshevOrbit

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Hilbert16

open Filter Set
open Hilbert16.Spikes
open scoped Topology

/-!
# Angular coordinates around one Chebyshev center

The forward polynomial coordinates turn every small cell oval into the
ellipse `u² + v² = 2h`.  Multiplying the second coordinate by the cell
orientation gives a strictly positive angular cross product for the
Hamiltonian flow.  Positivity persists on an open tube for the perturbed
field and feeds the elementary positive-ray theorem.
-/

noncomputable def chebyshevForwardX (n : ℕ) (z : PhaseSpace) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (phaseSpaceProdEquiv z).1

noncomputable def chebyshevSignedForwardY
    (n i j : ℕ) (lambda : ℝ) (z : PhaseSpace) : ℝ :=
  -chebyshevCellJacobianOrientation i j * Real.sqrt lambda *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (phaseSpaceProdEquiv z).2

noncomputable def chebyshevForwardXRate
    (n : ℕ) (lambda : ℝ) (P : ℝ × ℝ → ℝ)
    (mu : ℝ) (z : PhaseSpace) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
      (phaseSpaceProdEquiv z).1 *
    (chebyshevPerturbedVector n lambda P mu (phaseSpaceProdEquiv z)).1

noncomputable def chebyshevSignedForwardYRate
    (n i j : ℕ) (lambda : ℝ) (P : ℝ × ℝ → ℝ)
    (mu : ℝ) (z : PhaseSpace) : ℝ :=
  (-chebyshevCellJacobianOrientation i j * Real.sqrt lambda) *
    ((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval
      (phaseSpaceProdEquiv z).2 *
        (chebyshevPerturbedVector n lambda P mu (phaseSpaceProdEquiv z)).2)

noncomputable def chebyshevForwardRadiusSq
    (n i j : ℕ) (lambda : ℝ) (z : PhaseSpace) : ℝ :=
  chebyshevForwardX n z ^ 2 +
    chebyshevSignedForwardY n i j lambda z ^ 2

noncomputable def chebyshevAngularCross
    (n i j : ℕ) (lambda : ℝ) (P : ℝ × ℝ → ℝ)
    (mu : ℝ) (z : PhaseSpace) : ℝ :=
  chebyshevForwardX n z *
      chebyshevSignedForwardYRate n i j lambda P mu z -
    chebyshevSignedForwardY n i j lambda z *
      chebyshevForwardXRate n lambda P mu z

theorem continuous_chebyshevForwardRadiusSq
    (n i j : ℕ) (lambda : ℝ) :
    Continuous (chebyshevForwardRadiusSq n i j lambda) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hp : Continuous (fun x : ℝ => p.eval x) :=
    (contDiff_realPolynomial_eval p).continuous
  unfold chebyshevForwardRadiusSq chebyshevForwardX chebyshevSignedForwardY
  fun_prop

theorem continuous_chebyshevAngularCross
    (n i j : ℕ) (lambda : ℝ) {P : ℝ × ℝ → ℝ}
    (hP : Continuous P) :
    Continuous (fun muz : ℝ × PhaseSpace =>
      chebyshevAngularCross n i j lambda P muz.1 muz.2) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hp : Continuous (fun x : ℝ => p.eval x) :=
    (contDiff_realPolynomial_eval p).continuous
  have hdp : Continuous (fun x : ℝ => p.derivative.eval x) :=
    (contDiff_realPolynomial_eval p.derivative).continuous
  unfold chebyshevAngularCross chebyshevForwardX chebyshevSignedForwardY
    chebyshevForwardXRate chebyshevSignedForwardYRate
    chebyshevPerturbedVector chebyshevHamiltonianDx chebyshevHamiltonianDy
  fun_prop

theorem chebyshevForwardX_comp_hasDerivAt
    {n : ℕ} {lambda mu t : ℝ} {P : ℝ × ℝ → ℝ}
    {gamma : ℝ → PhaseSpace}
    (hgamma : HasDerivAt gamma
      (chebyshevPerturbedPhaseVector n lambda P mu (gamma t)) t) :
    HasDerivAt (fun s => chebyshevForwardX n (gamma s))
      (chebyshevForwardXRate n lambda P mu (gamma t)) t := by
  have hprod : HasDerivAt (phaseSpaceProdEquiv ∘ gamma)
      (chebyshevPerturbedVector n lambda P mu
        (phaseSpaceProdEquiv (gamma t))) t := by
    have hout : HasFDerivAt phaseSpaceProdEquiv
        phaseSpaceProdEquiv.toContinuousLinearMap (gamma t) :=
      phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
    have hcomp := hout.comp_hasDerivAt t hgamma
    simpa [chebyshevPerturbedPhaseVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hcomp
  simpa [chebyshevForwardX, chebyshevForwardXRate, Function.comp_def] using
    ((Polynomial.Chebyshev.T ℝ (n : ℤ)).hasDerivAt
      (phaseSpaceProdEquiv (gamma t)).1).comp t hprod.fst

theorem chebyshevSignedForwardY_comp_hasDerivAt
    {n i j : ℕ} {lambda mu t : ℝ} {P : ℝ × ℝ → ℝ}
    {gamma : ℝ → PhaseSpace}
    (hgamma : HasDerivAt gamma
      (chebyshevPerturbedPhaseVector n lambda P mu (gamma t)) t) :
    HasDerivAt (fun s => chebyshevSignedForwardY n i j lambda (gamma s))
      (chebyshevSignedForwardYRate n i j lambda P mu (gamma t)) t := by
  have hprod : HasDerivAt (phaseSpaceProdEquiv ∘ gamma)
      (chebyshevPerturbedVector n lambda P mu
        (phaseSpaceProdEquiv (gamma t))) t := by
    have hout : HasFDerivAt phaseSpaceProdEquiv
        phaseSpaceProdEquiv.toContinuousLinearMap (gamma t) :=
      phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
    have hcomp := hout.comp_hasDerivAt t hgamma
    simpa [chebyshevPerturbedPhaseVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hcomp
  have hy := ((Polynomial.Chebyshev.T ℝ (n : ℤ)).hasDerivAt
      (phaseSpaceProdEquiv (gamma t)).2).comp t hprod.snd
  simpa [chebyshevSignedForwardY, chebyshevSignedForwardYRate,
    Function.comp_def, mul_assoc] using
      hy.const_mul (-chebyshevCellJacobianOrientation i j * Real.sqrt lambda)

/-- Any periodic carrier contained in an oriented nonvanishing Chebyshev
tube meets its positive forward-coordinate ray. -/
theorem PeriodicOrbit.exists_mem_chebyshevPositiveRay_of_subset
    {n i j : ℕ} {lambda mu : ℝ} {P : ℝ × ℝ → ℝ}
    (O : PeriodicOrbit
      (fun z => chebyshevPerturbedPhaseVector n lambda P mu z))
    {U : Set PhaseSpace} (hOU : O.carrier ⊆ U)
    (hradius : ∀ z ∈ U, 0 < chebyshevForwardRadiusSq n i j lambda z)
    (hcross : ∀ z ∈ U, 0 < chebyshevAngularCross n i j lambda P mu z) :
    ∃ z ∈ O.carrier,
      chebyshevSignedForwardY n i j lambda z = 0 ∧
        0 < chebyshevForwardX n z := by
  rcases O.exists_periodicParametrization with ⟨gamma, hgamma, hrange⟩
  rcases hgamma with ⟨T, hT, hint, hperiod, hnonconst⟩
  let u : ℝ → ℝ := fun t => chebyshevForwardX n (gamma t)
  let v : ℝ → ℝ := fun t =>
    chebyshevSignedForwardY n i j lambda (gamma t)
  let du : ℝ → ℝ := fun t =>
    chebyshevForwardXRate n lambda P mu (gamma t)
  let dv : ℝ → ℝ := fun t =>
    chebyshevSignedForwardYRate n i j lambda P mu (gamma t)
  have hu : ∀ t, HasDerivAt u (du t) t := by
    intro t
    exact chebyshevForwardX_comp_hasDerivAt (hint t)
  have hv : ∀ t, HasDerivAt v (dv t) t := by
    intro t
    exact chebyshevSignedForwardY_comp_hasDerivAt (hint t)
  have hgammaT : gamma T = gamma 0 := by
    simpa using hperiod 0
  have hperiodU : u T = u 0 := congrArg (chebyshevForwardX n) hgammaT
  have hperiodV : v T = v 0 :=
    congrArg (chebyshevSignedForwardY n i j lambda) hgammaT
  have hmem (t : ℝ) : gamma t ∈ U := by
    apply hOU
    rw [← hrange]
    exact ⟨t, rfl⟩
  have hrad : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < u t ^ 2 + v t ^ 2 := by
    intro t ht
    exact hradius (gamma t) (hmem t)
  have hcross' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < u t * dv t - v t * du t := by
    intro t ht
    exact hcross (gamma t) (hmem t)
  rcases exists_mem_positiveRay_of_periodic_of_angularCross_pos
      hT hu hv hperiodU hperiodV hrad hcross' with ⟨t, ht, hvzero, hupos⟩
  refine ⟨gamma t, ?_, hvzero, hupos⟩
  rw [← hrange]
  exact ⟨t, rfl⟩

theorem chebyshevForwardRadiusSq_phaseOrbit_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    chebyshevForwardRadiusSq n i j lambda
      (chebyshevPhaseOrbit n i j lambda h t) = 2 * h := by
  have huv := ellipticOrbitUV_energy_eq
    (lt_of_lt_of_le zero_lt_one hlambda) hh (t := t)
  have hstrict : |(ellipticOrbitUV lambda h t).1| < 1 ∧
      |(ellipticOrbitUV lambda h t).2| < 1 := by
    constructor
    · rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).2]
    · have hscale : 0 ≤ (lambda - 1) * (ellipticOrbitUV lambda h t).2 ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hlambda) (sq_nonneg _)
      rw [abs_lt, neg_lt]
      constructor <;> nlinarith [sq_nonneg (ellipticOrbitUV lambda h t).1]
  have hx := eval_chebyshevInverseBranch (i := i) hn hstrict.1.le
  have hy := eval_chebyshevInverseBranch (i := j) hn hstrict.2.le
  have hsigmaSq : chebyshevCellJacobianOrientation i j ^ 2 = 1 := by
    rcases chebyshevCellJacobianOrientation_mem i j with hs | hs <;> simp [hs]
  have hnegSigmaSq : (-chebyshevCellJacobianOrientation i j) ^ 2 = 1 := by
    calc
      (-chebyshevCellJacobianOrientation i j) ^ 2 =
          chebyshevCellJacobianOrientation i j ^ 2 := by ring
      _ = 1 := hsigmaSq
  have hsqrtSq : Real.sqrt lambda ^ 2 = lambda :=
    Real.sq_sqrt (le_trans zero_le_one hlambda)
  simp only [chebyshevForwardRadiusSq, chebyshevForwardX,
    chebyshevSignedForwardY, phaseSpaceProdEquiv_chebyshevPhaseOrbit,
    chebyshevCellOrbit_fst, chebyshevCellOrbit_snd]
  rw [hx, hy]
  calc
    (ellipticOrbitUV lambda h t).1 ^ 2 +
        (-chebyshevCellJacobianOrientation i j * Real.sqrt lambda *
          (ellipticOrbitUV lambda h t).2) ^ 2 =
        (ellipticOrbitUV lambda h t).1 ^ 2 +
          lambda * (ellipticOrbitUV lambda h t).2 ^ 2 := by
      simp only [mul_pow]
      rw [hnegSigmaSq, hsqrtSq]
      ring
    _ = 2 * h := huv

theorem chebyshevAngularCross_phaseOrbit_zero_pos
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h t : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) (P : ℝ × ℝ → ℝ) :
    0 < chebyshevAngularCross n i j lambda P 0
      (chebyshevPhaseOrbit n i j lambda h t) := by
  let z := chebyshevCellOrbit n i j lambda h t
  let px := chebyshevForwardDerivative n z.1
  let py := chebyshevForwardDerivative n z.2
  let sigma := chebyshevCellJacobianOrientation i j
  have horient := chebyshevCellOrbit_timeFactor_orientation_pos
    hn hi hj hlambda hh.le hhHalf (t := t)
  have hradius := chebyshevForwardRadiusSq_phaseOrbit_eq
    hn hlambda hh.le hhHalf (i := i) (j := j) (t := t)
  have hsqrtPos : 0 < Real.sqrt lambda :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hlambda)
  have hsigmaSq : chebyshevCellJacobianOrientation i j ^ 2 = 1 := by
    rcases chebyshevCellJacobianOrientation_mem i j with hs | hs <;>
      simp [hs]
  have hnegSigmaSq : (-chebyshevCellJacobianOrientation i j) ^ 2 = 1 := by
    calc
      (-chebyshevCellJacobianOrientation i j) ^ 2 =
          chebyshevCellJacobianOrientation i j ^ 2 := by ring
      _ = 1 := hsigmaSq
  have hsqrtSq : Real.sqrt lambda ^ 2 = lambda :=
    Real.sq_sqrt (le_trans zero_le_one hlambda)
  have hfactor : 0 < sigma * (Real.sqrt lambda * px * py) := by
    simpa [z, px, py, sigma] using horient
  have hformula :
      chebyshevAngularCross n i j lambda P 0
        (chebyshevPhaseOrbit n i j lambda h t) =
        (sigma * (Real.sqrt lambda * px * py)) * (2 * h) := by
    simp only [chebyshevAngularCross, chebyshevForwardX,
      chebyshevSignedForwardY, chebyshevForwardXRate,
      chebyshevSignedForwardYRate, chebyshevPerturbedVector,
      chebyshevHamiltonianDx, chebyshevHamiltonianDy,
      chebyshevForwardDerivative, phaseSpaceProdEquiv_chebyshevPhaseOrbit,
      zero_mul, add_zero, z, px, py, sigma]
    rw [← hradius]
    simp only [chebyshevForwardRadiusSq, chebyshevForwardX,
      chebyshevSignedForwardY, phaseSpaceProdEquiv_chebyshevPhaseOrbit]
    simp only [mul_pow]
    rw [hnegSigmaSq, hsqrtSq]
    ring
  rw [hformula]
  exact mul_pos hfactor (mul_pos (by norm_num) hh)

/-- Compactness and joint continuity thicken an unperturbed Chebyshev oval
to one fixed open phase tube on which nonvanishing and angular orientation
hold for every sufficiently small perturbation parameter. -/
theorem exists_chebyshevOrientedAngularTube
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h)
    (hhHalf : h < 1 / 2) {P : ℝ × ℝ → ℝ}
    (hP : Continuous P) :
    ∃ U : Set PhaseSpace, IsOpen U ∧
      Set.range (chebyshevPhaseOrbit n i j lambda h) ⊆ U ∧
      ∀ᶠ mu in 𝓝 (0 : ℝ), ∀ z ∈ U,
        0 < chebyshevForwardRadiusSq n i j lambda z ∧
          0 < chebyshevAngularCross n i j lambda P mu z := by
  let K : Set PhaseSpace :=
    Set.range (chebyshevPhaseOrbit n i j lambda h)
  let G : Set (ℝ × PhaseSpace) :=
    {muz | 0 < chebyshevForwardRadiusSq n i j lambda muz.2 ∧
      0 < chebyshevAngularCross n i j lambda P muz.1 muz.2}
  have hGopen : IsOpen G := by
    apply IsOpen.inter
    · exact isOpen_Ioi.preimage
        ((continuous_chebyshevForwardRadiusSq n i j lambda).comp continuous_snd)
    · exact isOpen_Ioi.preimage
        (continuous_chebyshevAngularCross n i j lambda hP)
  have hfiber : ({(0 : ℝ)} : Set ℝ) ×ˢ K ⊆ G := by
    rintro ⟨mu, z⟩ ⟨hmu, hz⟩
    have hmu : mu = 0 := Set.mem_singleton_iff.mp hmu
    subst mu
    rcases hz with ⟨t, rfl⟩
    constructor
    · rw [chebyshevForwardRadiusSq_phaseOrbit_eq hn hlambda hh.le hhHalf]
      positivity
    · exact chebyshevAngularCross_phaseOrbit_zero_pos
        hn hi hj hlambda hh hhHalf P
  obtain ⟨A, U, hAopen, hUopen, hzeroA, hKU, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton
      (isCompact_range_chebyshevPhaseOrbit n i j lambda h) hGopen hfiber
  refine ⟨U, hUopen, hKU, ?_⟩
  filter_upwards [hAopen.mem_nhds (hzeroA (Set.mem_singleton 0))]
    with mu hmu
  intro z hz
  exact hprod (show (mu, z) ∈ A ×ˢ U from ⟨hmu, hz⟩)

end Hilbert16
