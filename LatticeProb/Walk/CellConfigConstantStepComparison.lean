import LatticeProb.Walk.CellConfigKnotComparison
import LatticeProb.Walk.ConstantStepInterpolation

/-!
# Constant-speed time changes of cell walks

A scaled cell walk is a time change of the constant-speed interpolation of
its scaled representatives.
-/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- A scaled cell walk and its constant-speed interpolation agree after an
increasing time change which matches their respective knot times. -/
theorem exists_orderIso_interpolatedWalk_eq_constantStep
    (H : CellConfig) (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0,
      (∀ n, φ (scaledJumpTime H ω hpos ε n) = ConstantStepInterpolation.knot m n) ∧
      ∀ t, H.interpolatedWalk p ε ω t =
        ConstantStepInterpolation.path m (fun n => (ε : ℝ) • p (ω n)) (φ t) := by
  apply exists_orderIso_interpolatedWalk_eq H p ω hpos hunb hε
    (ConstantStepInterpolation.knot m)
    (ConstantStepInterpolation.knot_strictMono hm)
    (ConstantStepInterpolation.knot_zero m)
    (ConstantStepInterpolation.knot_unbounded hm)
    (ConstantStepInterpolation.path m (fun n => (ε : ℝ) • p (ω n)))
  intro n t hlo hhi
  exact ConstantStepInterpolation.path_eq_lineMap hm _ n t hlo hhi

end LatticeProb.CellConfigInterpolation

end
