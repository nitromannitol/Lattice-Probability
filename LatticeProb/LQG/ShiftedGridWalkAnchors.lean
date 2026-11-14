import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Basic.Real.Basic

/-! # Measurable representatives on shifted time grids -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- The endpoint representative of a cell in a shifted time grid. -/
def shiftedGridAnchor {E : Type*} [TopologicalSpace E]
    (η : C(ℝ, E)) (b θ : ℝ) (k : ℤ) : E :=
  η (b * ((k : ℝ) + θ))

/-- A fixed grid anchor depends continuously on the curve, mesh, and shift. -/
theorem continuous_shiftedGridAnchor {E : Type*} [TopologicalSpace E] (k : ℤ) :
    Continuous (fun p : C(ℝ, E) × ℝ × ℝ => shiftedGridAnchor p.1 p.2.1 p.2.2 k) := by
  have ht : Continuous (fun p : C(ℝ, E) × ℝ × ℝ => p.2.1 * ((k : ℝ) + p.2.2)) := by
    fun_prop
  exact continuous_eval.comp (continuous_fst.prodMk ht)

/-- All grid anchors are jointly measurable in the curve, mesh, and shift. -/
theorem measurable_shiftedGridAnchors {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)] :
    Measurable (fun p : C(ℝ, E) × ℝ × ℝ =>
      fun k : ℤ => shiftedGridAnchor p.1 p.2.1 p.2.2 k) :=
  measurable_pi_iff.mpr fun k => (continuous_shiftedGridAnchor k).measurable

/-- The representatives visited by a walk, jointly with the environment and walk. -/
theorem measurable_shiftedGridWalkAnchors {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ, E)] [BorelSpace C(ℝ, E)] :
    Measurable (fun p : (C(ℝ, E) × ℝ × ℝ) × (ℕ → ℤ) =>
      fun n : ℕ => shiftedGridAnchor p.1.1 p.1.2.1 p.1.2.2 (p.2 n)) := by
  apply measurable_pi_iff.mpr
  intro n
  have h : Measurable (fun p : (C(ℝ, E) × ℝ × ℝ) × ℤ =>
      shiftedGridAnchor p.1.1 p.1.2.1 p.1.2.2 p.2) :=
    measurable_from_prod_countable_left fun k => (continuous_shiftedGridAnchor k).measurable
  exact h.comp (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))

end LatticeProb
