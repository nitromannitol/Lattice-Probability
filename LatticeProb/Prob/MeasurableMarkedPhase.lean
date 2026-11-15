import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-! Measurability of phase maps with a mark-dependent shift. -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- The marked coordinatewise phase map is jointly measurable in the scale,
mark and coordinates. -/
theorem measurable_markedPhase {E ι : Type*} [MeasurableSpace E]
    (θ : E → (ι → ℝ)) (hθ : Measurable θ) :
    Measurable (fun p : (ℝ × E) × (ι → ℝ) =>
      (p.1.2, fun i => Int.fract (p.1.1 * p.2 i - θ p.1.2 i))) := by
  refine (measurable_snd.comp measurable_fst).prodMk (measurable_pi_iff.mpr ?_)
  intro i
  apply Measurable.fract
  exact ((measurable_fst.comp measurable_fst).mul
    ((measurable_pi_apply i).comp measurable_snd)).sub
      ((measurable_pi_apply i).comp (hθ.comp (measurable_snd.comp measurable_fst)))

/-- For an s-finite coordinate measure, each measurable event has phase mass
measurable in the scale and mark. -/
theorem measurable_markedPhase_measure {E ι : Type*} [MeasurableSpace E]
    (θ : E → (ι → ℝ)) (hθ : Measurable θ) (μ : Measure (ι → ℝ)) [SFinite μ]
    {s : Set (E × (ι → ℝ))} (hs : MeasurableSet s) :
    Measurable (fun p : ℝ × E =>
      μ {x | (p.2, fun i => Int.fract (p.1 * x i - θ p.2 i)) ∈ s}) := by
  exact measurable_measure_prodMk_left ((measurable_markedPhase θ hθ) hs)

end LatticeProb
