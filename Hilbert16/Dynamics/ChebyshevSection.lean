import Hilbert16.Dynamics.ReturnTime
import Hilbert16.Spikes.ChebyshevPeriodAnnulus
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

set_option autoImplicit false

namespace Hilbert16

open Hilbert16.Spikes

theorem contDiff_realPolynomial_eval (p : Polynomial ℝ) :
    ContDiff ℝ 1 (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow n)

theorem contDiff_chebyshevPolynomial_eval (n : ℕ) :
    ContDiff ℝ 1 (fun x : ℝ => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x) :=
  contDiff_realPolynomial_eval _

theorem contDiffAt_chebyshevInverseBranch
    (n i : ℕ) {u : ℝ} (huNeg : u ≠ -1) (huPos : u ≠ 1) :
    ContDiffAt ℝ 1 (chebyshevInverseBranch n i) u := by
  have ha : ContDiffAt ℝ 1 Real.arcsin u := Real.contDiffAt_arcsin huNeg huPos
  have hinner : ContDiffAt ℝ 1 (fun v : ℝ =>
      chebyshevRootPhase n i +
        chebyshevCellOrientation i * Real.arcsin v / (n : ℝ)) u := by
    fun_prop (disch := assumption)
  exact Real.contDiff_cos.contDiffAt.comp u hinner

/-- The explicit Chebyshev cell orbit transported to the public Euclidean phase space. -/
noncomputable def chebyshevPhaseOrbit
    (n i j : ℕ) (lambda h t : ℝ) : PhaseSpace :=
  phaseSpaceProdEquiv.symm (chebyshevCellOrbit n i j lambda h t)

@[simp]
theorem phaseSpaceProdEquiv_chebyshevPhaseOrbit
    (n i j : ℕ) (lambda h t : ℝ) :
    phaseSpaceProdEquiv (chebyshevPhaseOrbit n i j lambda h t) =
      chebyshevCellOrbit n i j lambda h t := by
  simp [chebyshevPhaseOrbit]

/-- A global affine scalar defining the local horizontal section through angular time zero of the
`j`-th inverse branch. -/
noncomputable def chebyshevSectionCoordinate (n j : ℕ) (z : PhaseSpace) : ℝ :=
  (phaseSpaceProdEquiv z).2 - chebyshevInverseBranch n j 0

/-- The Chebyshev Hamiltonian transported to the public Euclidean phase space. -/
noncomputable def chebyshevPhaseEnergy (n : ℕ) (lambda : ℝ) (z : PhaseSpace) : ℝ :=
  chebyshevHamiltonian n lambda (phaseSpaceProdEquiv z)

/-- The unperturbed Hamiltonian vector field transported to `PhaseSpace`. -/
noncomputable def chebyshevPhaseHamiltonianVector
    (n : ℕ) (lambda : ℝ) (z : PhaseSpace) : PhaseSpace :=
  phaseSpaceProdEquiv.symm
    (chebyshevHamiltonianVector n lambda (phaseSpaceProdEquiv z))

/-- Fréchet derivative of the affine horizontal section coordinate. -/
noncomputable def chebyshevSectionFDeriv : PhaseSpace →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ ℝ ℝ ∘L phaseSpaceProdEquiv.toContinuousLinearMap

/-- Energy-parametrized base point on the horizontal section, chosen at angular time zero. -/
noncomputable def chebyshevPhaseSectionPoint
    (n i j : ℕ) (lambda h : ℝ) : PhaseSpace :=
  chebyshevPhaseOrbit n i j lambda h 0

theorem contDiff_chebyshevSectionCoordinate (n j : ℕ) :
    ContDiff ℝ 1 (chebyshevSectionCoordinate n j) := by
  unfold chebyshevSectionCoordinate
  fun_prop

theorem chebyshevSectionCoordinate_hasFDerivAt (n j : ℕ) (z : PhaseSpace) :
    HasFDerivAt (chebyshevSectionCoordinate n j) chebyshevSectionFDeriv z := by
  have hbase : HasFDerivAt phaseSpaceProdEquiv
      phaseSpaceProdEquiv.toContinuousLinearMap z :=
    phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt (fun x : PhaseSpace =>
    (phaseSpaceProdEquiv x).2 - chebyshevInverseBranch n j 0)
    (ContinuousLinearMap.snd ℝ ℝ ℝ ∘L phaseSpaceProdEquiv.toContinuousLinearMap) z
  exact hbase.snd.sub_const (chebyshevInverseBranch n j 0)

theorem contDiff_chebyshevPhaseEnergy (n : ℕ) (lambda : ℝ) :
    ContDiff ℝ 1 (chebyshevPhaseEnergy n lambda) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx : ContDiff ℝ 1 (fun z : PhaseSpace => p.eval (phaseSpaceProdEquiv z).1) :=
    (contDiff_realPolynomial_eval p).comp (by fun_prop)
  have hy : ContDiff ℝ 1 (fun z : PhaseSpace => p.eval (phaseSpaceProdEquiv z).2) :=
    (contDiff_realPolynomial_eval p).comp (by fun_prop)
  have hsum : ContDiff ℝ 1 (fun z : PhaseSpace =>
      p.eval (phaseSpaceProdEquiv z).1 ^ 2 +
        lambda * p.eval (phaseSpaceProdEquiv z).2 ^ 2) :=
    (hx.pow 2).add (contDiff_const.mul (hy.pow 2))
  change ContDiff ℝ 1 (fun z : PhaseSpace =>
    (p.eval (phaseSpaceProdEquiv z).1 ^ 2 +
      lambda * p.eval (phaseSpaceProdEquiv z).2 ^ 2) / 2)
  simpa only [div_eq_mul_inv, smul_eq_mul, one_mul, mul_comm] using
    hsum.const_smul (1 / 2 : ℝ)

theorem chebyshevPhaseEnergy_phaseOrbit_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h t : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    chebyshevPhaseEnergy n lambda (chebyshevPhaseOrbit n i j lambda h t) = h := by
  unfold chebyshevPhaseEnergy
  rw [phaseSpaceProdEquiv_chebyshevPhaseOrbit]
  exact chebyshevCellOrbit_energy_eq hn hlambda hh hhHalf

theorem contDiffAt_chebyshevPhaseSectionPoint
    (n i j : ℕ) (lambda : ℝ) {h : ℝ} (hh : 0 < h) (hhHalf : h < 1 / 2) :
    ContDiffAt ℝ 1 (chebyshevPhaseSectionPoint n i j lambda) h := by
  have hsqrt : ContDiffAt ℝ 1 (fun e : ℝ => Real.sqrt (2 * e)) h := by
    have hmul : ContDiffAt ℝ 1 (fun e : ℝ => 2 * e) h := by fun_prop
    exact hmul.sqrt (by positivity)
  have hsqrtSq : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (2 * h) := Real.sqrt_nonneg _
  have hsqrtLt : Real.sqrt (2 * h) < 1 := by nlinarith
  have hbranch : ContDiffAt ℝ 1
      (fun e : ℝ => chebyshevInverseBranch n i (Real.sqrt (2 * e))) h :=
    (contDiffAt_chebyshevInverseBranch n i (by nlinarith) (by nlinarith)).comp h hsqrt
  have hpair : ContDiffAt ℝ 1 (fun e : ℝ =>
      (chebyshevInverseBranch n i (Real.sqrt (2 * e)),
        chebyshevInverseBranch n j 0)) h :=
    hbranch.prodMk contDiffAt_const
  have hmap := phaseSpaceProdEquiv.symm.contDiff.contDiffAt.comp h hpair
  have heq : chebyshevPhaseSectionPoint n i j lambda = fun e : ℝ =>
      phaseSpaceProdEquiv.symm
        (chebyshevInverseBranch n i (Real.sqrt (2 * e)),
          chebyshevInverseBranch n j 0) := by
    funext e
    simp only [chebyshevPhaseSectionPoint, chebyshevPhaseOrbit, chebyshevCellOrbit,
      chebyshevCellInverseMap, ellipticOrbitUV, Real.cos_zero, mul_one, Real.sin_zero,
      mul_zero, Prod.map_apply]
  rw [heq]
  change ContDiffAt ℝ 1 (phaseSpaceProdEquiv.symm ∘ fun e : ℝ =>
    (chebyshevInverseBranch n i (Real.sqrt (2 * e)),
      chebyshevInverseBranch n j 0)) h
  exact hmap

theorem chebyshevPhaseSectionPoint_on_section
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevSectionCoordinate n j (chebyshevPhaseSectionPoint n i j lambda h) = 0 :=
  by
    simp [chebyshevPhaseSectionPoint, chebyshevSectionCoordinate, chebyshevPhaseOrbit,
      chebyshevCellOrbit, chebyshevCellInverseMap, ellipticOrbitUV]

theorem chebyshevPhaseSectionPoint_energy_eq
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2) :
    chebyshevPhaseEnergy n lambda (chebyshevPhaseSectionPoint n i j lambda h) = h :=
  chebyshevPhaseEnergy_phaseOrbit_eq hn hlambda hh hhHalf

theorem chebyshevSectionCoordinate_phaseOrbit_zero
    (n i j : ℕ) (lambda h : ℝ) :
    chebyshevSectionCoordinate n j (chebyshevPhaseOrbit n i j lambda h 0) = 0 := by
  simp [chebyshevSectionCoordinate, chebyshevPhaseOrbit, chebyshevCellOrbit,
    chebyshevCellInverseMap, ellipticOrbitUV]

/-- The explicit orbit crosses the section transversely at angular time zero. -/
theorem chebyshevSectionCoordinate_phaseOrbit_hasDerivAt_zero
    {n i j : ℕ} (hn : n ≠ 0) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 ≤ h) (hhHalf : h < 1 / 2) :
    HasDerivAt
      (fun t : ℝ => chebyshevSectionCoordinate n j
        (chebyshevPhaseOrbit n i j lambda h t))
      (deriv (chebyshevInverseBranch n j) 0 *
        (Real.sqrt (2 * h) / Real.sqrt lambda)) 0 := by
  have hsnd := chebyshevCellOrbit_snd_branch_hasDerivAt (i := i) (j := j)
    hn hlambda hh hhHalf (t := (0 : ℝ))
  have hsub := hsnd.sub_const (chebyshevInverseBranch n j 0)
  simpa [chebyshevSectionCoordinate, chebyshevPhaseOrbit,
    chebyshevCellOrbitVelocity, ellipticOrbitUV, ellipticOrbitUVVelocity] using hsub

theorem chebyshevSectionCoordinate_phaseOrbit_deriv_ne_zero
    {n j : ℕ} (hn : n ≠ 0) (hj : j < n) {lambda h : ℝ}
    (hlambda : 1 ≤ lambda) (hh : 0 < h) :
    deriv (chebyshevInverseBranch n j) 0 *
      (Real.sqrt (2 * h) / Real.sqrt lambda) ≠ 0 := by
  apply mul_ne_zero
  · exact chebyshevInverseBranch_deriv_ne_zero hn hj (by norm_num)
  · exact div_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity))
      (Real.sqrt_ne_zero'.mpr (lt_of_lt_of_le zero_lt_one hlambda))

/-- The horizontal section is transverse to the actual Hamiltonian vector field at the explicit
angular-time-zero point. -/
theorem chebyshevSectionFDeriv_phaseHamiltonianVector_ne_zero
    {n i j : ℕ} (hn : n ≠ 0) (hi : i < n) (hj : j < n)
    {lambda h : ℝ} (hlambda : 1 ≤ lambda) (hh : 0 < h) (hhHalf : h < 1 / 2) :
    chebyshevSectionFDeriv
      (chebyshevPhaseHamiltonianVector n lambda
        (chebyshevPhaseSectionPoint n i j lambda h)) ≠ 0 := by
  let orbit := chebyshevCellOrbit n i j lambda h 0
  let velocity := chebyshevCellOrbitVelocity n i j lambda h 0
  let factor := Real.sqrt lambda *
    chebyshevForwardDerivative n orbit.1 * chebyshevForwardDerivative n orbit.2
  let vector := chebyshevHamiltonianVector n lambda orbit
  have horientation := chebyshevCellOrbit_timeFactor_orientation_pos
    hn hi hj hlambda hh.le hhHalf (t := (0 : ℝ))
  change 0 < chebyshevCellJacobianOrientation i j * factor at horientation
  have hfactor : factor ≠ 0 := by
    intro hzero
    rw [show factor = 0 from hzero, mul_zero] at horientation
    exact (lt_irrefl 0) horientation
  have hvelocity : velocity.2 ≠ 0 := by
    simpa [velocity, chebyshevCellOrbitVelocity, ellipticOrbitUV,
      ellipticOrbitUVVelocity] using
      chebyshevSectionCoordinate_phaseOrbit_deriv_ne_zero hn hj hlambda hh
  have hvectorIdentity := chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector
    hn hlambda hh.le hhHalf (i := i) (j := j) (t := (0 : ℝ))
  have hsnd := congrArg Prod.snd hvectorIdentity
  change factor * velocity.2 = -vector.2 at hsnd
  have hvectorSnd : vector.2 ≠ 0 := by
    intro hzero
    rw [hzero, neg_zero] at hsnd
    exact (mul_ne_zero hfactor hvelocity) hsnd
  change (phaseSpaceProdEquiv
    (chebyshevPhaseHamiltonianVector n lambda
      (chebyshevPhaseSectionPoint n i j lambda h))).2 ≠ 0
  simpa [chebyshevPhaseHamiltonianVector, chebyshevPhaseSectionPoint,
    chebyshevPhaseOrbit, orbit, vector] using hvectorSnd

end Hilbert16
