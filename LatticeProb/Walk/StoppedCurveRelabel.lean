import LatticeProb.Walk.CountableStoppedCurveMeasurable

/-! # Relabelling stopped polygonal curves -/

set_option autoImplicit false

open MeasureTheory
open BouRabeeGwynne

namespace LatticeProb

/-- Relabelling the vertices preserves the stopped polygonal curve when the
stopping set is pulled back along the relabelling. -/
theorem stoppedPolygonalCurve_relabel {d : ℕ} {X Y : Type*}
    (pos : Y → Euc d) (f : X → Y) (B : Set Y) (p : ℕ → X) :
    stoppedPolygonalCurve (pos ∘ f) (f ⁻¹' B) p =
      stoppedPolygonalCurve pos B (fun n => f (p n)) := by
  rfl

/-- The law of a stopped polygonal curve commutes with measurable relabelling
of a countable vertex path, including the infinite-exit convention. -/
theorem map_stoppedPolygonalCurve_relabel {d : ℕ} {X Y : Type*}
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure (ℕ → X)) (pos : Y → Euc d) (f : X → Y) (B : Set Y) :
    μ.map (stoppedPolygonalCurve (pos ∘ f) (f ⁻¹' B)) =
      (μ.map (fun p n => f (p n))).map (stoppedPolygonalCurve pos B) := by
  have hf : Measurable (fun p : ℕ → X => fun n => f (p n)) :=
    Measurable.of_eval fun n => (measurable_of_countable f).comp (measurable_pi_apply n)
  rw [Measure.map_map (measurable_stoppedPolygonalCurve_countable pos B) hf]
  exact congrArg (fun g => μ.map g) (funext (stoppedPolygonalCurve_relabel pos f B))

end LatticeProb
