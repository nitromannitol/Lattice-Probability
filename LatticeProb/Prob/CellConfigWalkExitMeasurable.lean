import LatticeProb.Prob.BrownianExitPosition
import LatticeProb.Prob.CellConfigWalkMeasurable

/-!
# Measurability of exit positions of interpolated cell walks

The exit position from an open set is measurable as a function of a continuous
path. Consequently, it is almost everywhere measurable for an interpolated
walk on a recurrent cell configuration with positive holding times. Infinite
exit times use the value at time zero.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- The totalized exit position of a continuous path from an open set is measurable. -/
theorem measurable_continuousExitPosition {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable fun γ : BrownianPath d => γ (continuousExitTime U 0 γ).toNNReal :=
  measurable_eval_random_time (measurable_continuousExitTime hU 0)

namespace CellConfigWalk

open ReflectedGMS ReflectedGMS.GMS ReflectedGMS.GMS.CellConfig

/-- The exit position of the interpolated walk is almost everywhere measurable. -/
theorem aemeasurable_interpolatedWalk_exitPosition {H : CellConfig} [Countable H.cells]
    (hrec : H.Recurrent) (hpos : ∀ K, 0 < H.holding K)
    {K₀ : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    AEMeasurable (fun ω => (H.interpolatedWalk p ε ω)
      (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal) Q :=
  (measurable_continuousExitPosition hU).comp_aemeasurable
    (aemeasurable_interpolatedWalk_of_recurrent hrec hpos hQ p ε)

end CellConfigWalk
end LatticeProb
