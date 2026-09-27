import LatticeProb.Prob.InducedMap.Iterates

/-!
# The induced map: assembled statement

Collects Poincaré recurrence, invariance of the restricted measure, and ergodicity of the
first-return map into the single theorem `induced_map`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The induced map.**  Poincaré recurrence on `A`, invariance of `μ.restrict A` under the
first-return map, and ergodicity of the first-return map when `T` is ergodic. -/
theorem induced_map (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    (∀ᵐ x ∂μ, x ∈ A → 0 < retTime T A x) ∧
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) ∧
    (Ergodic T μ → Ergodic (inducedMap T A) (μ.restrict A)) :=
  ⟨ae_retTime_pos hT hA, measurePreserving_inducedMap hT hA,
    fun herg => ergodic_inducedMap_of_ergodic herg hA⟩

end LatticeProb
