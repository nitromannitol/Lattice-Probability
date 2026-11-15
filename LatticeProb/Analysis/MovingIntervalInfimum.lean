import LatticeProb.Topology.MovingIntervalCurve
import LatticeProb.Topology.ContinuousMapBorel
import Mathlib.Topology.Order.Compact

/-! # Infima of continuous paths on moving intervals -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- The infimum of a continuous path over a moving unordered interval depends
continuously on the path and both endpoints. -/
theorem continuous_sInf_image_uIcc :
    Continuous (fun p : C(ℝ, ℝ) × ℝ × ℝ => sInf (p.1 '' uIcc p.2.1 p.2.2)) := by
  have h : Continuous (fun p : C(unitInterval, ℝ) => sInf (range p)) := by
    simpa only [image_univ] using
      (isCompact_univ.continuous_sInf
        (f := fun (g : C(unitInterval, ℝ)) (u : unitInterval) => g u) continuous_eval)
  have hc := h.comp (continuous_movingIntervalCurve (E := ℝ))
  simpa only [Function.comp_def, range_movingIntervalCurve] using hc

/-- The moving interval infimum is jointly Borel measurable. -/
theorem measurable_sInf_image_uIcc :
    Measurable (fun p : C(ℝ, ℝ) × ℝ × ℝ => sInf (p.1 '' uIcc p.2.1 p.2.2)) :=
  continuous_sInf_image_uIcc.measurable

end LatticeProb
