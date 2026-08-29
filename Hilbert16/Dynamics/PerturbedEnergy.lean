import Hilbert16.Dynamics.MelnikovIntegral
import Hilbert16.Spikes.ChebyshevMelnikov

set_option autoImplicit false

namespace Hilbert16

open Hilbert16.Spikes Set

/-- The paper's one-component perturbation of the Chebyshev Hamiltonian
vector field: `(H_y + mu P, -H_x)`. -/
noncomputable def chebyshevPerturbedVector
    (n : ℕ) (lambda : ℝ) (P : ℝ × ℝ → ℝ) (mu : ℝ)
    (z : ℝ × ℝ) : ℝ × ℝ :=
  (chebyshevHamiltonianDy n lambda z + mu * P z,
    -chebyshevHamiltonianDx n z)

/-- The perturbed vector field transported to the public Euclidean phase
space used by the local-flow API. -/
noncomputable def chebyshevPerturbedPhaseVector
    (n : ℕ) (lambda : ℝ) (P : ℝ × ℝ → ℝ)
    (mu : ℝ) (z : PhaseSpace) : PhaseSpace :=
  phaseSpaceProdEquiv.symm
    (chebyshevPerturbedVector n lambda P mu (phaseSpaceProdEquiv z))

/-- Energy production with the perturbation parameter removed. -/
noncomputable def chebyshevEnergyProduction
    (n : ℕ) (P : ℝ × ℝ → ℝ) (z : PhaseSpace) : ℝ :=
  chebyshevHamiltonianDx n (phaseSpaceProdEquiv z) *
    P (phaseSpaceProdEquiv z)

/-- Along the actual perturbed vector field, `2H` has derivative
`2 mu H_x P`. This is the pointwise algebraic heart of the Melnikov
factorization. -/
theorem chebyshevHamiltonianNumerator_comp_hasDerivAt_perturbed
    {n : ℕ} {lambda mu t : ℝ} {P : ℝ × ℝ → ℝ}
    {gamma : ℝ → ℝ × ℝ}
    (hgamma : RealInnerProdHasDerivAt gamma
      (chebyshevPerturbedVector n lambda P mu (gamma t)) t) :
    RealInnerHasDerivAt
      (fun s : ℝ => chebyshevHamiltonianNumerator n lambda (gamma s))
      (2 * mu * chebyshevHamiltonianDx n (gamma t) * P (gamma t)) t := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx := (p.hasDerivAt (gamma t).1).comp t hgamma.fst
  have hy := (p.hasDerivAt (gamma t).2).comp t hgamma.snd
  have hsum := (hx.pow 2).add ((hy.pow 2).const_mul lambda)
  have hsum' : RealInnerHasDerivAt
      (fun s : ℝ =>
        p.eval (gamma s).1 ^ 2 + lambda * p.eval (gamma s).2 ^ 2)
      (2 * p.eval (gamma t).1 *
          (p.derivative.eval (gamma t).1 *
            (chebyshevPerturbedVector n lambda P mu (gamma t)).1) +
        lambda * (2 * p.eval (gamma t).2 *
          (p.derivative.eval (gamma t).2 *
            (chebyshevPerturbedVector n lambda P mu (gamma t)).2))) t := by
    convert hsum using 1
    · funext s
      simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, pow_two]
    · simp only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        mul_assoc]
  have hrate :
      2 * p.eval (gamma t).1 *
          (p.derivative.eval (gamma t).1 *
            (chebyshevPerturbedVector n lambda P mu (gamma t)).1) +
        lambda * (2 * p.eval (gamma t).2 *
          (p.derivative.eval (gamma t).2 *
            (chebyshevPerturbedVector n lambda P mu (gamma t)).2)) =
      2 * mu * chebyshevHamiltonianDx n (gamma t) * P (gamma t) := by
    simp [chebyshevPerturbedVector, chebyshevHamiltonianDx,
      chebyshevHamiltonianDy, p]
    ring
  rw [hrate] at hsum'
  simpa only [chebyshevHamiltonianNumerator, p] using hsum'

/-- Phase-space derivative identity for the actual perturbed vector field. -/
theorem chebyshevPhaseEnergy_comp_hasDerivAt_perturbed
    {n : ℕ} {lambda mu t : ℝ} {P : ℝ × ℝ → ℝ}
    {gamma : ℝ → PhaseSpace}
    (hgamma : HasDerivAt gamma
      (chebyshevPerturbedPhaseVector n lambda P mu (gamma t)) t) :
    HasDerivAt
      (fun s : ℝ => chebyshevPhaseEnergy n lambda (gamma s))
      (mu * chebyshevEnergyProduction n P (gamma t)) t := by
  have hout : HasFDerivAt phaseSpaceProdEquiv
      phaseSpaceProdEquiv.toContinuousLinearMap (gamma t) :=
    phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
  have hprod : HasDerivAt (phaseSpaceProdEquiv ∘ gamma)
      (phaseSpaceProdEquiv.toContinuousLinearMap
        (chebyshevPerturbedPhaseVector n lambda P mu (gamma t))) t :=
    hout.comp_hasDerivAt t hgamma
  have hprod' : RealInnerProdHasDerivAt
      (fun s : ℝ => phaseSpaceProdEquiv (gamma s))
      (chebyshevPerturbedVector n lambda P mu
        (phaseSpaceProdEquiv (gamma t))) t := by
    simpa [chebyshevPerturbedPhaseVector, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hprod
  have hnum := chebyshevHamiltonianNumerator_comp_hasDerivAt_perturbed hprod'
  have hhalf := hnum.div_const (2 : ℝ)
  convert hhalf using 1 <;> try rfl
  unfold chebyshevEnergyProduction
  ring

/-- The energy-production observable is continuous whenever the polynomial
perturbation (or, more generally, the supplied scalar perturbation) is. -/
theorem continuous_chebyshevEnergyProduction
    (n : ℕ) {P : ℝ × ℝ → ℝ} (hP : Continuous P) :
    Continuous (chebyshevEnergyProduction n P) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx : Continuous (fun z : PhaseSpace => (phaseSpaceProdEquiv z).1) :=
    phaseSpaceProdEquiv.continuous.fst
  have hp : Continuous (fun z : PhaseSpace => p.eval (phaseSpaceProdEquiv z).1) :=
    (contDiff_realPolynomial_eval p).continuous.comp hx
  have hdp : Continuous (fun z : PhaseSpace =>
      p.derivative.eval (phaseSpaceProdEquiv z).1) :=
    (contDiff_realPolynomial_eval p.derivative).continuous.comp hx
  have hPcomp : Continuous (fun z : PhaseSpace => P (phaseSpaceProdEquiv z)) :=
    hP.comp phaseSpaceProdEquiv.continuous
  change Continuous (fun z : PhaseSpace =>
    (p.eval (phaseSpaceProdEquiv z).1 *
      p.derivative.eval (phaseSpaceProdEquiv z).1) *
        P (phaseSpaceProdEquiv z))
  exact (hp.mul hdp).mul hPcomp

/-- The energy-production observable is jointly `C¹` in phase space when
the supplied perturbation is `C¹`.  In particular this applies to every
degree-audited multivariate polynomial perturbation. -/
theorem contDiff_chebyshevEnergyProduction
    (n : ℕ) {P : ℝ × ℝ → ℝ} (hP : ContDiff ℝ 1 P) :
    ContDiff ℝ 1 (chebyshevEnergyProduction n P) := by
  let p := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hx : ContDiff ℝ 1 (fun z : PhaseSpace ↦ (phaseSpaceProdEquiv z).1) := by
    fun_prop
  have hp : ContDiff ℝ 1 (fun z : PhaseSpace ↦
      p.eval (phaseSpaceProdEquiv z).1) :=
    (contDiff_realPolynomial_eval p).comp hx
  have hdp : ContDiff ℝ 1 (fun z : PhaseSpace ↦
      p.derivative.eval (phaseSpaceProdEquiv z).1) :=
    (contDiff_realPolynomial_eval p.derivative).comp hx
  have hPcomp : ContDiff ℝ 1 (fun z : PhaseSpace ↦
      P (phaseSpaceProdEquiv z)) := hP.comp (by fun_prop)
  change ContDiff ℝ 1 (fun z : PhaseSpace ↦
    (p.eval (phaseSpaceProdEquiv z).1 *
      p.derivative.eval (phaseSpaceProdEquiv z).1) *
        P (phaseSpaceProdEquiv z))
  exact (hp.mul hdp).mul hPcomp

/-- Actual-field specialization of the generic parameter-integral theorem:
the normalized energy displacement of a `C¹` perturbation is jointly `C¹`
at the unperturbed return. -/
theorem ChebyshevReturnSetup.contDiffAt_actualMelnikov
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ) (hP : ContDiff ℝ 1 P) :
    ContDiffAt ℝ 1
      (S.melnikovIntegral (chebyshevEnergyProduction S.n P)) (0, S.h₀) :=
  S.contDiffAt_melnikovIntegral _
    (contDiff_chebyshevEnergyProduction S.n hP)

/-- For a local flow whose vector field is exactly the paper's perturbed
Chebyshev field, the genuine return displacement has the exact factorization
`Delta(mu,h) = mu D(mu,h)`. The derivative hypothesis of the generic FTC
lemma has disappeared: it is now proved from the ODE field itself. -/
theorem ChebyshevReturnSetup.energyDisplacement_eq_mu_mul_actualMelnikov
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ)
    (hX : ∀ (mu : ℝ) (z : PhaseSpace),
      X mu z = chebyshevPerturbedPhaseVector S.n S.lambda P mu z)
    (hP : Continuous P) {mu h : ℝ}
    (hh : 0 ≤ h) (hhHalf : h ≤ 1 / 2)
    (hsegment : ∀ t ∈ Set.uIcc 0 (S.returnTime.time (mu, h)),
      ((mu, chebyshevPhaseSectionPoint
          S.n S.i S.j S.lambda h), t) ∈ S.localFlow.domain) :
    S.energyDisplacement (mu, h) =
      mu * S.melnikovIntegral
        (chebyshevEnergyProduction S.n P) (mu, h) := by
  apply S.energyDisplacement_eq_mu_mul_melnikovIntegral
    (chebyshevEnergyProduction S.n P) hh hhHalf hsegment
  · have hQ := continuous_chebyshevEnergyProduction S.n hP
    intro t ht
    apply hQ.continuousAt.comp_continuousWithinAt
    exact (S.localFlow.chebyshevByEnergy_hasDerivAt
      S.n S.i S.j S.lambda mu h t (hsegment t ht)).continuousAt.continuousWithinAt
  · intro t ht
    apply chebyshevPhaseEnergy_comp_hasDerivAt_perturbed
    have hflow := S.localFlow.chebyshevByEnergy_hasDerivAt
      S.n S.i S.j S.lambda mu h t (hsegment t ht)
    rw [hX] at hflow
    exact hflow

/-- The `P dy` integral along the genuine unperturbed return segment, with
the velocity supplied by the Hamiltonian vector field in physical product
coordinates. -/
noncomputable def ChebyshevReturnSetup.unperturbedTimePdy
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ) (h : ℝ) : ℝ :=
  Spikes.parameterizedPdy P
    (fun t => phaseSpaceProdEquiv
      (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, h), t)))
    (fun t => Spikes.chebyshevHamiltonianVector S.n S.lambda
      (phaseSpaceProdEquiv
        (S.localFlow.chebyshevByEnergy S.n S.i S.j S.lambda ((0, h), t))))
    0 (S.returnTime.time (0, h))

/-- On every unperturbed return segment, the time-integral normalization is
exactly `-∫ P dy`. This removes the sign ambiguity between energy production
and the paper's oriented one-form convention. -/
theorem ChebyshevReturnSetup.melnikovIntegral_zero_eq_neg_unperturbedTimePdy
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    (P : ℝ × ℝ → ℝ) (h : ℝ) :
    S.melnikovIntegral (chebyshevEnergyProduction S.n P) (0, h) =
      -S.unperturbedTimePdy P h := by
  unfold ChebyshevReturnSetup.melnikovIntegral
    ChebyshevReturnSetup.unperturbedTimePdy Spikes.parameterizedPdy
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [chebyshevEnergyProduction, Spikes.chebyshevHamiltonianVector]
  ring

/-- The physical product-coordinate return curve really has the Hamiltonian
velocity on every unperturbed segment in the local-flow domain. -/
theorem ChebyshevReturnSetup.unperturbedTimeCurve_hasDerivAt
    {X : ℝ → PhaseSpace → PhaseSpace} (S : ChebyshevReturnSetup X)
    {h t : ℝ}
    (ht : ((0, chebyshevPhaseSectionPoint
      S.n S.i S.j S.lambda h), t) ∈ S.localFlow.domain) :
    HasDerivAt
      (fun s : ℝ => phaseSpaceProdEquiv
        (S.localFlow.chebyshevByEnergy
          S.n S.i S.j S.lambda ((0, h), s)))
      (Spikes.chebyshevHamiltonianVector S.n S.lambda
        (phaseSpaceProdEquiv
          (S.localFlow.chebyshevByEnergy
            S.n S.i S.j S.lambda ((0, h), t)))) t := by
  have hflow := S.localFlow.chebyshevByEnergy_hasDerivAt
    S.n S.i S.j S.lambda 0 h t ht
  rw [S.unperturbed_eq] at hflow
  have hout : HasFDerivAt phaseSpaceProdEquiv
      phaseSpaceProdEquiv.toContinuousLinearMap
        (S.localFlow.chebyshevByEnergy
          S.n S.i S.j S.lambda ((0, h), t)) :=
    phaseSpaceProdEquiv.toContinuousLinearMap.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt t hflow
  simpa [chebyshevPhaseHamiltonianVector, Function.comp_def,
    ContinuousLinearMap.comp_apply] using hcomp

end Hilbert16
