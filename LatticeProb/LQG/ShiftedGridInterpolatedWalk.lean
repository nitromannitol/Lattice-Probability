import LatticeProb.LQG.ShiftedGridWalkAnchors
import LatticeProb.Walk.ConstantStepMeasurable

/-! # Measurable interpolation of shifted-grid walks -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- Evaluation of the interpolated shifted-grid walk is jointly measurable in the
curve, mesh, shift, integer walk, speed and time. -/
theorem measurable_shiftedGridInterpolatedWalk :
    Measurable (fun q : ((C(ℝ, ℂ) × ℝ × ℝ) × (ℕ → ℤ)) × ℝ × ℝ≥0 =>
      ConstantStepInterpolation.path q.2.1
        (fun n => shiftedGridAnchor q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.1.2 n)) q.2.2) := by
  have ha := measurable_shiftedGridWalkAnchors (E := ℂ)
  have h := ConstantStepInterpolation.measurable_path.comp
    ((ha.comp measurable_fst).prodMk measurable_snd)
  exact h

end LatticeProb
