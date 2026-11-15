import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Total mass and Lévy–Prokhorov distance

The total masses of finite measures on a pseudometric measurable space differ by at most their
Lévy–Prokhorov distance.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- If `levyProkhorovEDist μ ν < δ`, the total mass of `μ` is at most that of `ν` plus `δ`. -/
theorem measure_univ_le_add_of_levyProkhorovEDist_lt {μ ν : Measure X} {δ : ℝ}
    (h : levyProkhorovEDist μ ν < ENNReal.ofReal δ) : μ univ ≤ ν univ + ENNReal.ofReal δ :=
  (left_measure_le_of_levyProkhorovEDist_lt h MeasurableSet.univ).trans
    (add_le_add (measure_mono (subset_univ _)) le_rfl)

/-- The total mass of `μ` exceeds that of `ν` by at most the Lévy–Prokhorov distance. -/
theorem measure_univ_toReal_le_add_levyProkhorovDist (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    (μ univ).toReal ≤ (ν univ).toReal + levyProkhorovDist μ ν := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set d := levyProkhorovDist μ ν with hd_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hD : levyProkhorovEDist μ ν = ENNReal.ofReal d :=
    (ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)).symm
  have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal (d + ε) := by
    rw [hD]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top ν univ, ENNReal.ofReal_ne_top⟩)
    (measure_univ_le_add_of_levyProkhorovEDist_lt hlt)
  rw [ENNReal.toReal_add (measure_ne_top ν univ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)] at h
  linarith

/-- The total masses of two finite measures differ by at most their Lévy–Prokhorov distance. -/
theorem abs_measure_univ_toReal_sub_le_levyProkhorovDist (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    |(μ univ).toReal - (ν univ).toReal| ≤ levyProkhorovDist μ ν := by
  have h1 := measure_univ_toReal_le_add_levyProkhorovDist μ ν
  have h2 := measure_univ_toReal_le_add_levyProkhorovDist ν μ
  rw [levyProkhorovDist_comm] at h2
  rw [abs_le]
  constructor <;> linarith


end LatticeProb
