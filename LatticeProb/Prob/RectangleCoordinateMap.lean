import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Coordinatewise images of Lebesgue measure on finite rectangles. -/

open MeasureTheory Set

namespace LatticeProb

/-- A coordinatewise measurable map sends Lebesgue measure on a finite
half-open rectangle to the product of the images of its interval measures. -/
theorem map_restrict_rectangle_eq_pi {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (f : ι → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun x : ι → ℝ => fun i => f i (x i))
        (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))) =
      Measure.pi (fun i => Measure.map (f i) (volume.restrict (Ico (u i) (v i)))) := by
  have (i : ι) : IsFiniteMeasure (volume.restrict (Ico (u i) (v i))) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ico])
  have (i : ι) : IsFiniteMeasure
      (Measure.map (f i) (volume.restrict (Ico (u i) (v i)))) := by
    infer_instance
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)

end LatticeProb
