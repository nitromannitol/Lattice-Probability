/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.LocalCircleProcess at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalConfiguration
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTRestrictCircles
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R1

/-!
# Circle-average information carried by a local field restriction

For every open `V`, Mathlib's product measurable space on circle-average
processes lets us assemble the existing DG circle-average factorization at
each circle lying in `V`. This is the measurable field input of the frozen S7
excursion reconstruction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.GMS4c

attribute [local instance] Classical.propDecidable

open LQGMetric LQGMetric.Blueprint
open MatedCRTHarmonic.MatedCRT

private theorem circleFactor (V : TopologicalSpace.Opens ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ}
    (hball : closedBall w ρ ⊆ (V : Set ℂ)) :
    ∃ Ψ : DistOn V → ℝ, Measurable Ψ ∧
      ∀ h : DistC, circleAvg h ρ w = Ψ (restrictTo V h) :=
  LQGMetric.DG.r18_circ_factor V hρ
    (sphere_subset_closedBall.trans hball)

/-- A measurable version of the process of circle averages supported on
closed disks contained in `V`, read entirely from the restricted field. -/
def localCircleProcess (V : TopologicalSpace.Opens ℂ)
    (T : DistOn V) (ρ : ℝ) (w : ℂ) : ℝ :=
  if h : 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ) then
    (circleFactor V h.1 h.2).choose T
  else 0

theorem measurable_localCircleProcess (V : TopologicalSpace.Opens ℂ) :
    Measurable (localCircleProcess V) := by
  apply measurable_pi_iff.mpr
  intro ρ
  apply measurable_pi_iff.mpr
  intro w
  by_cases h : 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ)
  · simpa [localCircleProcess, h] using (circleFactor V h.1 h.2).choose_spec.1
  · simp only [localCircleProcess, h, dite_false]
    exact measurable_const

/-- The local process agrees pointwise with the frozen S7 restriction of the
whole-plane circle-average process. -/
theorem localCircleProcess_restrictTo (V : TopologicalSpace.Opens ℂ)
    (h : DistC) :
    localCircleProcess V (restrictTo V h) =
      restrictCircles V (fun ρ w => circleAvg h ρ w) := by
  funext ρ w
  by_cases hc : 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ)
  · simp only [localCircleProcess, restrictCircles, hc]
    exact ((circleFactor V hc.1 hc.2).choose_spec.2 h).symm
  · simp [localCircleProcess, restrictCircles, hc]

/-- The IG circle process with its additive constant, restricted to circles
whose closed disks lie in `V`. -/
def localIGCircleProcess (V : TopologicalSpace.Opens ℂ)
    (x : DistOn V × ℝ) (ρ : ℝ) (w : ℂ) : ℝ :=
  if 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ) then
    localCircleProcess V x.1 ρ w + x.2
  else 0

theorem measurable_localIGCircleProcess (V : TopologicalSpace.Opens ℂ) :
    Measurable (localIGCircleProcess V) := by
  apply measurable_pi_iff.mpr
  intro ρ
  apply measurable_pi_iff.mpr
  intro w
  by_cases hc : 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ)
  · simp only [localIGCircleProcess, hc]
    exact ((measurable_pi_apply w).comp
      ((measurable_pi_apply ρ).comp
        ((measurable_localCircleProcess V).comp measurable_fst))).add measurable_snd
  · simp [localIGCircleProcess, hc]

theorem localIGCircleProcess_restrictTo (V : TopologicalSpace.Opens ℂ)
    (h : DistC) (c : ℝ) :
    localIGCircleProcess V (restrictTo V h, c) =
      restrictCircles V (fun ρ w => circleAvg h ρ w + c) := by
  funext ρ w
  by_cases hc : 0 < ρ ∧ closedBall w ρ ⊆ (V : Set ℂ)
  · have h0 := congrFun (congrFun (localCircleProcess_restrictTo V h) ρ) w
    simp [restrictCircles, hc] at h0
    simp [localIGCircleProcess, restrictCircles, hc, h0]
  · simp [localIGCircleProcess, restrictCircles, hc]

end MatedCRTHarmonic.GMS4c
