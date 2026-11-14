import LatticeProb.Walk.ConstantStepContinuous
import LatticeProb.LQG.ShiftedGridWalkAnchors

/-! # Measurable continuous interpolations -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Measurable anchors and speed give a measurable continuous interpolated path. -/
theorem measurable_continuousPath_of {Ω : Type*} [MeasurableSpace Ω]
    {p : Ω → ℕ → ℂ} {m : Ω → ℝ} (hp : Measurable p) (hm : Measurable m) :
    Measurable (fun ω => continuousPath (m ω) (p ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have h : Measurable (fun ω => (p ω, m ω, t)) :=
    hp.prodMk (hm.prodMk measurable_const)
  simpa only [continuousPath_apply, Function.comp_def] using measurable_path.comp h

end LatticeProb.ConstantStepInterpolation

namespace LatticeProb

/-- Shifted-grid walk interpolations are jointly measurable as continuous paths. -/
theorem measurable_shiftedGridContinuousWalk :
    Measurable (fun q : ((C(ℝ, ℂ) × ℝ × ℝ) × (ℕ → ℤ)) × ℝ =>
      ConstantStepInterpolation.continuousPath q.2
        (fun n => shiftedGridAnchor q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.1.2 n))) := by
  apply ConstantStepInterpolation.measurable_continuousPath_of
  · exact (measurable_shiftedGridWalkAnchors (E := ℂ)).comp measurable_fst
  · exact measurable_snd

end LatticeProb
