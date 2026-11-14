import LatticeProb.Prob.NormalizedPathPrefix
import Mathlib.Analysis.Convex.Segment

/-! # Continuous curves on moving real intervals -/

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

namespace LatticeProb

/-- A real-parameter curve restricted to an interval and parametrized on `[0,1]`. -/
def movingIntervalCurve {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (a b : ℝ) : C(unitInterval, E) where
  toFun u := f ((1 - (u : ℝ)) * a + (u : ℝ) * b)
  continuous_toFun := f.continuous.comp (by fun_prop)

@[simp] theorem movingIntervalCurve_apply {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (a b : ℝ) (u : unitInterval) :
    movingIntervalCurve f a b u = f ((1 - (u : ℝ)) * a + (u : ℝ) * b) := rfl

/-- The range is the curve image of the unordered interval, also when the endpoints coincide. -/
theorem range_movingIntervalCurve {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (a b : ℝ) :
    range (movingIntervalCurve f a b) = f '' uIcc a b := by
  rw [← segment_eq_uIcc, segment_eq_image]
  ext x
  simp only [mem_range, mem_image, movingIntervalCurve_apply]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, ⟨(u : ℝ), u.property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

/-- The normalized interval restriction depends continuously on the curve and endpoints. -/
theorem continuous_movingIntervalCurve {E : Type*} [TopologicalSpace E] :
    Continuous (fun p : C(ℝ, E) × ℝ × ℝ => movingIntervalCurve p.1 p.2.1 p.2.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have ht : Continuous (fun p : (C(ℝ, E) × ℝ × ℝ) × unitInterval =>
      (1 - (p.2 : ℝ)) * p.1.2.1 + (p.2 : ℝ) * p.1.2.2) := by
    fun_prop
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk ht)

/-- The normalized interval restriction is jointly Borel measurable. -/
theorem measurable_movingIntervalCurve {E : Type*} [TopologicalSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)]
    [MeasurableSpace C(unitInterval, E)] [BorelSpace C(unitInterval, E)] :
    Measurable (fun p : C(ℝ, E) × ℝ × ℝ => movingIntervalCurve p.1 p.2.1 p.2.2) :=
  continuous_movingIntervalCurve.measurable

/-- A grid-shifted curve cell, with real mesh and shift parameters. -/
def shiftedCellCurve {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (ε θ : ℝ) (k : ℤ) : C(unitInterval, E) :=
  movingIntervalCurve f (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ))

/-- The image of a shifted cell curve is the corresponding curve segment. -/
theorem range_shiftedCellCurve {E : Type*} [TopologicalSpace E]
    (f : C(ℝ, E)) (ε θ : ℝ) (k : ℤ) :
    range (shiftedCellCurve f ε θ k) =
      f '' uIcc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ)) :=
  range_movingIntervalCurve f _ _

/-- The shifted cell curve is jointly continuous in the curve, mesh and shift. -/
theorem continuous_shiftedCellCurve {E : Type*} [TopologicalSpace E] (k : ℤ) :
    Continuous (fun p : C(ℝ, E) × ℝ × ℝ => shiftedCellCurve p.1 p.2.1 p.2.2 k) := by
  change Continuous (fun p : C(ℝ, E) × ℝ × ℝ =>
    movingIntervalCurve p.1 (p.2.1 * ((k : ℝ) - 1 + p.2.2)) (p.2.1 * ((k : ℝ) + p.2.2)))
  have hm : Continuous (fun p : C(ℝ, E) × ℝ × ℝ =>
      (p.1, p.2.1 * ((k : ℝ) - 1 + p.2.2), p.2.1 * ((k : ℝ) + p.2.2))) := by
    fun_prop
  exact continuous_movingIntervalCurve.comp hm

/-- The shifted cell curve is jointly Borel measurable in the curve, mesh and shift. -/
theorem measurable_shiftedCellCurve {E : Type*} [TopologicalSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)]
    [MeasurableSpace C(unitInterval, E)] [BorelSpace C(unitInterval, E)] (k : ℤ) :
    Measurable (fun p : C(ℝ, E) × ℝ × ℝ => shiftedCellCurve p.1 p.2.1 p.2.2 k) :=
  (continuous_shiftedCellCurve k).measurable

end LatticeProb
