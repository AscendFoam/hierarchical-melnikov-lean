import Hilbert16.Dynamics.SimpleRoot
import Hilbert16.Foundations.StateSpace

set_option autoImplicit false

namespace Hilbert16

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The local return-time output of the implicit-function theorem for a level equation
`F (x,t) = F u`. The iff field records local uniqueness of the selected return time. -/
structure LocalLevelTime (F : E × ℝ → ℝ) (u : E × ℝ) where
  time : E → ℝ
  time_at : time u.1 = u.2
  contDiffAt_time : ContDiffAt ℝ 1 time u.1
  eventually_level : ∀ᶠ x in 𝓝 u.1, F (x, time x) = F u
  eventually_unique : ∀ᶠ v in 𝓝 u, F v = F u ↔ time v.1 = v.2

/-- A `C¹` scalar level equation has a locally unique `C¹` hitting time when its time
derivative is nonzero. -/
noncomputable def ContDiffAt.localLevelTime_of_hasDerivAt
    {F : E × ℝ → ℝ} {u : E × ℝ} {d : ℝ} (hF : ContDiffAt ℝ 1 F u)
    (hslice : HasDerivAt (fun t : ℝ => F (u.1, t)) d u.2) (hd : d ≠ 0) :
    LocalLevelTime F u := by
  have hpartial :
      (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ℝ) 1 ≠ 0 := by
    have hfromF : HasDerivAt (fun t : ℝ => F (u.1, t))
        ((fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ℝ) 1) u.2 := by
      simpa [Function.comp_def] using
        ((hF.hasStrictFDerivAt one_ne_zero).hasFDerivAt.comp u.2
          (hasFDerivAt_prodMk_right u.1 u.2)).hasDerivAt
    rw [hfromF.unique hslice]
    exact hd
  let hinv : (fderiv ℝ F u ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_apply_one_ne_zero _ hpartial
  exact
    { time := hF.implicitFunction one_ne_zero hinv
      time_at := hF.implicitFunction_apply_self one_ne_zero hinv
      contDiffAt_time := hF.contDiffAt_implicitFunction one_ne_zero hinv
      eventually_level := hF.eventually_apply_implicitFunction one_ne_zero hinv
      eventually_unique := hF.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv }

/-- Transverse-section specialization. A `C¹` candidate flow and a `C¹` section function reduce
the return-time construction to the nonzero time derivative of their composition. -/
noncomputable def localReturnTime_of_transverseSection
    {flow : E × ℝ → PhaseSpace} {sectionFn : PhaseSpace → ℝ}
    {u : E × ℝ} {d : ℝ} (hflow : ContDiffAt ℝ 1 flow u)
    (hsection : ContDiffAt ℝ 1 sectionFn (flow u))
    (htransverse : HasDerivAt (fun t : ℝ => sectionFn (flow (u.1, t))) d u.2)
    (hd : d ≠ 0) :
    LocalLevelTime (fun xt => sectionFn (flow xt)) u :=
  ContDiffAt.localLevelTime_of_hasDerivAt (hsection.comp u hflow) htransverse hd

/-- The return point obtained by substituting a local hitting-time branch into a candidate flow. -/
def LocalLevelTime.returnPoint {F : E × ℝ → ℝ} {u : E × ℝ}
    (T : LocalLevelTime F u) (flow : E × ℝ → PhaseSpace) : E → PhaseSpace :=
  fun x => flow (x, T.time x)

theorem LocalLevelTime.contDiffAt_returnPoint
    {F : E × ℝ → ℝ} {u : E × ℝ} (T : LocalLevelTime F u)
    {flow : E × ℝ → PhaseSpace} (hflow : ContDiffAt ℝ 1 flow u) :
    ContDiffAt ℝ 1 (T.returnPoint flow) u.1 := by
  have hu : (u.1, T.time u.1) = u := Prod.ext rfl T.time_at
  have hpair : ContDiffAt ℝ 1 (fun x : E => (x, T.time x)) u.1 :=
    contDiffAt_id.prodMk T.contDiffAt_time
  rw [← hu] at hflow
  change ContDiffAt ℝ 1 (fun x : E => flow (x, T.time x)) u.1
  exact hflow.comp u.1 hpair

/-- The constructed return point lies on the same local level of the section function. -/
theorem LocalLevelTime.eventually_returnPoint_level
    {flow : E × ℝ → PhaseSpace} {sectionFn : PhaseSpace → ℝ} {u : E × ℝ}
    (T : LocalLevelTime (fun xt => sectionFn (flow xt)) u) :
    ∀ᶠ x in 𝓝 u.1,
      sectionFn (T.returnPoint flow x) = sectionFn (flow u) := by
  simpa [LocalLevelTime.returnPoint] using T.eventually_level

/-- A scalar coordinate of the return point. -/
def LocalLevelTime.returnCoordinate {F : E × ℝ → ℝ} {u : E × ℝ}
    (T : LocalLevelTime F u) (flow : E × ℝ → PhaseSpace)
    (coordinate : PhaseSpace → ℝ) : E → ℝ :=
  fun x => coordinate (T.returnPoint flow x)

theorem LocalLevelTime.contDiffAt_returnCoordinate
    {F : E × ℝ → ℝ} {u : E × ℝ} (T : LocalLevelTime F u)
    {flow : E × ℝ → PhaseSpace} {coordinate : PhaseSpace → ℝ}
    (hflow : ContDiffAt ℝ 1 flow u) (hcoordinate : ContDiffAt ℝ 1 coordinate (flow u)) :
    ContDiffAt ℝ 1 (T.returnCoordinate flow coordinate) u.1 := by
  have hreturn := T.contDiffAt_returnPoint hflow
  have hbase : T.returnPoint flow u.1 = flow u := by
    simp [LocalLevelTime.returnPoint, T.time_at]
  rw [← hbase] at hcoordinate
  change ContDiffAt ℝ 1 (coordinate ∘ T.returnPoint flow) u.1
  exact hcoordinate.comp u.1 hreturn

/-- Energy displacement when the initial-data space is `(parameter, energy)`. -/
noncomputable def LocalLevelTime.energyDisplacement
    {F : (ℝ × ℝ) × ℝ → ℝ} {u : (ℝ × ℝ) × ℝ}
    (T : LocalLevelTime F u) (flow : (ℝ × ℝ) × ℝ → PhaseSpace)
    (energy : PhaseSpace → ℝ) : ℝ × ℝ → ℝ :=
  fun muh => T.returnCoordinate flow energy muh - muh.2

theorem LocalLevelTime.contDiffAt_energyDisplacement
    {F : (ℝ × ℝ) × ℝ → ℝ} {u : (ℝ × ℝ) × ℝ}
    (T : LocalLevelTime F u) {flow : (ℝ × ℝ) × ℝ → PhaseSpace}
    {energy : PhaseSpace → ℝ} (hflow : ContDiffAt ℝ 1 flow u)
    (henergy : ContDiffAt ℝ 1 energy (flow u)) :
    ContDiffAt ℝ 1 (T.energyDisplacement flow energy) u.1 := by
  exact (T.contDiffAt_returnCoordinate hflow henergy).sub contDiffAt_snd

end Hilbert16
