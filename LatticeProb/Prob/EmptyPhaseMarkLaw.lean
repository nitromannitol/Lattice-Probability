import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.Pi

/-! Marked phase laws with no coordinates. -/

open MeasureTheory Set

namespace LatticeProb

/-- A probability measure on the space of real functions on an empty type is
concentrated on its unique element. -/
theorem probability_measure_eq_dirac_of_isEmpty {ι : Type*} [IsEmpty ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] :
    ν = Measure.dirac 0 := by
  have hunique (x : ι → ℝ) : x = 0 := by
    funext i
    exact isEmptyElim i
  ext s hs
  by_cases h : (0 : ι → ℝ) ∈ s
  · have hs' : s = univ := by
      ext x
      simp only [mem_univ, iff_true]
      simpa only [hunique x] using h
    simp [hs']
  · have hs' : s = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      simpa only [hunique x] using h
    simp [hs']

/-- With no coordinates, any marked phase map is the identity and its law is
the mark marginal times any probability law on the empty-dimensional space. -/
theorem map_markedPhase_eq_prod_of_isEmpty {E ι : Type*} [MeasurableSpace E]
    [IsEmpty ι] (μ : Measure (E × (ι → ℝ))) [SFinite μ]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (a : ℝ) (θ : E → (ι → ℝ)) :
    μ.map (fun p => (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))) =
      (μ.map Prod.fst).prod ν := by
  have hphase : (fun p : E × (ι → ℝ) =>
      (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))) = id := by
    funext p
    apply Prod.ext
    · rfl
    · funext i
      exact isEmptyElim i
  have hzero : (fun p : E × (ι → ℝ) => (p.1, (0 : ι → ℝ))) = id := by
    funext p
    apply Prod.ext
    · rfl
    · funext i
      exact isEmptyElim i
  rw [hphase, Measure.map_id, (probability_measure_eq_dirac_of_isEmpty ν),
    Measure.prod_dirac, Measure.map_map measurable_prodMk_right measurable_fst]
  simp only [Function.comp_def, hzero, Measure.map_id]

end LatticeProb
