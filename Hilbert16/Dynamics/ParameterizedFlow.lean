import Hilbert16.Dynamics.ChebyshevSection
import Hilbert16.Foundations.PeriodicOrbit

set_option autoImplicit false

namespace Hilbert16

open Set

/-- A genuinely `C¹` local flow for a parameter-dependent planar vector field. This is the exact
foundation still to be constructed from Picard iteration; no existence theorem for this structure
is assumed here. -/
structure C1LocalFlow (X : ℝ → PhaseSpace → PhaseSpace) where
  flow : ParameterPhaseSpace × ℝ → PhaseSpace
  domain : Set (ParameterPhaseSpace × ℝ)
  isOpen_domain : IsOpen domain
  zero_mem : ∀ (mu : ℝ) (x : PhaseSpace), ((mu, x), 0) ∈ domain
  time_segment_mem : ∀ (mu : ℝ) (x : PhaseSpace) {a b : ℝ}, a ≤ b →
    ((mu, x), a) ∈ domain → ((mu, x), b) ∈ domain →
      ∀ t ∈ Set.Icc a b, ((mu, x), t) ∈ domain
  contDiffOn_flow : ContDiffOn ℝ 1 flow domain
  initial : ∀ (mu : ℝ) (x : PhaseSpace), ((mu, x), 0) ∈ domain →
    flow ((mu, x), 0) = x
  ode : ∀ (mu : ℝ) (x : PhaseSpace) (t : ℝ), ((mu, x), t) ∈ domain →
    HasDerivAt (fun s : ℝ => flow ((mu, x), s))
      (X mu (flow ((mu, x), t))) t

/-- Restrict a parameterized flow to the explicit energy-parametrized Chebyshev section. -/
noncomputable def C1LocalFlow.chebyshevByEnergy
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    (n i j : ℕ) (lambda : ℝ) : (ℝ × ℝ) × ℝ → PhaseSpace :=
  fun z => Phi.flow
    ((z.1.1, chebyshevPhaseSectionPoint n i j lambda z.1.2), z.2)

theorem C1LocalFlow.contDiffAt_chebyshevByEnergy
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    (n i j : ℕ) (lambda : ℝ) {z : (ℝ × ℝ) × ℝ}
    (hh : 0 < z.1.2) (hhHalf : z.1.2 < 1 / 2)
    (hz : ((z.1.1, chebyshevPhaseSectionPoint n i j lambda z.1.2), z.2) ∈
      Phi.domain) :
    ContDiffAt ℝ 1 (Phi.chebyshevByEnergy n i j lambda) z := by
  have hsection := contDiffAt_chebyshevPhaseSectionPoint n i j lambda hh hhHalf
  have henergyArg : ContDiffAt ℝ 1 (fun w : (ℝ × ℝ) × ℝ => w.1.2) z := by
    fun_prop
  have hsectionComp : ContDiffAt ℝ 1
      (chebyshevPhaseSectionPoint n i j lambda ∘
        fun w : (ℝ × ℝ) × ℝ => w.1.2) z :=
    hsection.comp z henergyArg
  have hmu : ContDiffAt ℝ 1 (fun w : (ℝ × ℝ) × ℝ => w.1.1) z := by
    fun_prop
  have hinput : ContDiffAt ℝ 1 (fun w : (ℝ × ℝ) × ℝ =>
      ((w.1.1, chebyshevPhaseSectionPoint n i j lambda w.1.2), w.2)) z :=
    (hmu.prodMk hsectionComp).prodMk contDiffAt_snd
  have hflow : ContDiffAt ℝ 1 Phi.flow
      ((z.1.1, chebyshevPhaseSectionPoint n i j lambda z.1.2), z.2) :=
    (Phi.contDiffOn_flow _ hz).contDiffAt (Phi.isOpen_domain.mem_nhds hz)
  change ContDiffAt ℝ 1 (Phi.flow ∘ fun w : (ℝ × ℝ) × ℝ =>
    ((w.1.1, chebyshevPhaseSectionPoint n i j lambda w.1.2), w.2)) z
  exact hflow.comp z hinput

theorem C1LocalFlow.chebyshevByEnergy_initial
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    (n i j : ℕ) (lambda mu h : ℝ)
    (hz : ((mu, chebyshevPhaseSectionPoint n i j lambda h), 0) ∈ Phi.domain) :
    Phi.chebyshevByEnergy n i j lambda ((mu, h), 0) =
      chebyshevPhaseSectionPoint n i j lambda h := by
  exact Phi.initial mu _ hz

theorem C1LocalFlow.chebyshevByEnergy_hasDerivAt
    {X : ℝ → PhaseSpace → PhaseSpace} (Phi : C1LocalFlow X)
    (n i j : ℕ) (lambda mu h t : ℝ)
    (hz : ((mu, chebyshevPhaseSectionPoint n i j lambda h), t) ∈ Phi.domain) :
    HasDerivAt (fun s : ℝ => Phi.chebyshevByEnergy n i j lambda ((mu, h), s))
      (X mu (Phi.chebyshevByEnergy n i j lambda ((mu, h), t))) t := by
  exact Phi.ode mu _ t hz

end Hilbert16
