import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

/-!
# Normalization of measures under similarities

Spatially normalized measures are unchanged by applying the same similarity to the
measure and its normalizing center and scale.
-/

open MeasureTheory

namespace LatticeProb

/-- An affine similarity cancels when its image measure is normalized by the
transformed center and scale. -/
theorem map_normalize_map_similarity (μ : Measure ℂ) (c a s b : ℂ)
    (ha : a ≠ 0) (hs : s ≠ 0) :
    (μ.map (fun z : ℂ => s * z + b)).map
        (fun z : ℂ => (z - (s * c + b)) / (s * a)) =
      μ.map (fun z : ℂ => (z - c) / a) := by
  have hf : Measurable (fun z : ℂ => s * z + b) := by fun_prop
  have hg : Measurable (fun z : ℂ => (z - (s * c + b)) / (s * a)) := by fun_prop
  rw [Measure.map_map hg hf]
  congr 1
  funext z
  dsimp only [Function.comp_apply]
  field_simp
  ring

/-- The Lévy–Prokhorov edistance of normalized measures is invariant under
simultaneous affine similarity. -/
theorem levyProkhorovEDist_normalize_map_similarity (μ ν : Measure ℂ) (c a s b : ℂ)
    (ha : a ≠ 0) (hs : s ≠ 0) :
    levyProkhorovEDist
      ((μ.map (fun z : ℂ => s * z + b)).map
        (fun z : ℂ => (z - (s * c + b)) / (s * a)))
      ((ν.map (fun z : ℂ => s * z + b)).map
        (fun z : ℂ => (z - (s * c + b)) / (s * a))) =
    levyProkhorovEDist (μ.map (fun z : ℂ => (z - c) / a))
      (ν.map (fun z : ℂ => (z - c) / a)) := by
  rw [map_normalize_map_similarity μ c a s b ha hs,
    map_normalize_map_similarity ν c a s b ha hs]

end LatticeProb
