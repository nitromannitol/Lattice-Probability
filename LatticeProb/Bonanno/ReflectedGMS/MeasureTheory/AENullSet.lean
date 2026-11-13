/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.MeasureTheory.AENullSet at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! Measurable null-set witnesses for almost-everywhere predicates. -/

open MeasureTheory

namespace ReflectedGMS

set_option autoImplicit false

/-- An almost-everywhere predicate admits a single measurable null exceptional set.

No measurability assumption on the predicate is needed: in the forward direction,
`toMeasurable` supplies a measurable hull of its bad set without changing its measure. -/
theorem ae_iff_exists_measurable_null_set {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → Prop) :
    (∀ᵐ x ∂μ, p x) ↔
      ∃ N : Set α, MeasurableSet N ∧ μ N = 0 ∧ ∀ x, x ∉ N → p x := by
  constructor
  · intro hp
    let bad : Set α := {x | ¬p x}
    refine ⟨toMeasurable μ bad, measurableSet_toMeasurable μ bad, ?_, ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.mp hp
    · intro x hxN
      by_contra hpx
      exact hxN (subset_toMeasurable μ bad hpx)
  · rintro ⟨N, _hNmeas, hNnull, hp⟩
    exact (measure_eq_zero_iff_ae_notMem.mp hNnull).mono hp

end ReflectedGMS
