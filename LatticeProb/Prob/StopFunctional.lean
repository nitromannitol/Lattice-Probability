import Mathlib
import LatticeProb.Prob.BrownianRestartPath

/-!
# Stopping times given by functionals of the path

A functional `Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞` of continuous paths is a *stopping functional* if for every
time `t` the path stopped at `t` has `Ψ ≤ t` exactly when the path has, and then `Ψ` takes the same
value on both: `{Ψ ≤ t}` is decided by the path up to time `t`.  For an adapted continuous
process `X`, `ω ↦ Ψ (pathMap X ω)` is then a stopping time of the filtration.

* `LatticeProb.IsStopFun`: the stopping-functional property.
* `LatticeProb.isStopFun_zero`: the constant `0` is a stopping functional.
* `LatticeProb.isStoppingTime_of_isStopFun`: for a measurable stopping functional `Ψ` and an
  adapted process with continuous paths, `ω ↦ Ψ (pathMap X ω)` is a stopping time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-- `Ψ` is a stopping functional: for all paths `w` and times `t`, if `Ψ w ≤ t` then stopping `w`
at `t` does not change `Ψ`, and if `Ψ (stopAt t w) ≤ t` then `Ψ w ≤ t`. -/
def IsStopFun (Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞) : Prop :=
  ∀ (w : C(ℝ≥0, ℝ)) (t : ℝ≥0),
    (Ψ w ≤ t → Ψ (stopAt (t : ℝ≥0∞) w) = Ψ w) ∧ (Ψ (stopAt (t : ℝ≥0∞) w) ≤ t → Ψ w ≤ t)

/-- The constant `0` is a stopping functional. -/
theorem isStopFun_zero : IsStopFun (fun _ => 0) := fun _ _ => ⟨fun _ => rfl, fun h => h⟩

/-- For a stopping functional `Ψ` the event `{Ψ ≤ t}` is decided by the path stopped at `t`. -/
theorem IsStopFun.le_iff {Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΨ : IsStopFun Ψ) (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    Ψ w ≤ t ↔ Ψ (stopAt (t : ℝ≥0∞) w) ≤ t :=
  ⟨fun h => ((hΨ w t).1 h).le.trans h, (hΨ w t).2⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable stopping functional of the sample path of an adapted process with continuous
paths is a stopping time. -/
theorem isStoppingTime_of_isStopFun {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hXad : StronglyAdapted 𝔽 X) (hXc : ∀ ω, Continuous fun t => X t ω)
    {Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) (hS : IsStopFun Ψ) :
    IsStoppingTime 𝔽 fun ω => Ψ (pathMap X hXc ω) := by
  intro t
  have hc : IsStoppingTime 𝔽 (fun _ : Ω => (t : ℝ≥0∞)) := isStoppingTime_const 𝔽 t
  have hY : Measurable[𝔽 t] fun ω => stopAt (t : ℝ≥0∞) (pathMap X hXc ω) := by
    have h := measurable_stopAt_pathMap hXad hXc hc
    rwa [show hc.measurableSpace = 𝔽 t from IsStoppingTime.measurableSpace_const 𝔽 t] at h
  have hset : {ω | Ψ (pathMap X hXc ω) ≤ (t : ℝ≥0∞)} =
      (fun ω => stopAt (t : ℝ≥0∞) (pathMap X hXc ω)) ⁻¹' {v | Ψ v ≤ (t : ℝ≥0∞)} := by
    ext ω
    exact hS.le_iff _ t
  show MeasurableSet[𝔽 t] {ω | Ψ (pathMap X hXc ω) ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact hY (measurableSet_le hΨ measurable_const)

end LatticeProb
