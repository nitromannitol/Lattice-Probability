import Mathlib
import LatticeProb.Prob.RandomMeasureIntensity

/-!
# Extension from rectangles with cylinder sides, for a random measure on `X × (ι → ℝ)`

For a family `ν : Ω → Measure (X × (ι → ℝ))` of random measures with a finite intensity `ρ`, the property
"`ω ↦ ν ω s` is almost everywhere measurable and `∫⁻ ν ω s = ρ s`" for the rectangles `A ×ˢ T` with `A` measurable
and `T` a measurable cylinder (a condition on finitely many coordinates) extends to every measurable set of the
product, although `ι` may be uncountable: the rectangles form a `π`-system generating the product `σ`-algebra.

* `LatticeProb.aemeasurable_and_lintegral_eq_of_cylinders`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- **Extension from rectangles with a measurable cylinder side.** -/
theorem aemeasurable_and_lintegral_eq_of_cylinders {Ω X ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} (ν : Ω → Measure (X × (ι → ℝ))) (ρ : Measure (X × (ι → ℝ)))
    [IsFiniteMeasure ρ]
    (hbase : ∀ A : Set X, MeasurableSet A → ∀ T ∈ measurableCylinders (fun _ : ι => ℝ),
      AEMeasurable (fun ω => ν ω (A ×ˢ T)) P ∧ ∫⁻ ω, ν ω (A ×ˢ T) ∂P = ρ (A ×ˢ T)) :
    ∀ S, MeasurableSet S → AEMeasurable (fun ω => ν ω S) P ∧ ∫⁻ ω, ν ω S ∂P = ρ S := by
  have huniv : (Set.univ : Set (ι → ℝ)) ∈ measurableCylinders (fun _ : ι => ℝ) :=
    univ_mem_measurableCylinders _
  have hD : IsCountablySpanning (measurableCylinders (fun _ : ι => ℝ)) :=
    ⟨fun _ => Set.univ, fun _ => huniv, Set.iUnion_const _⟩
  refine aemeasurable_and_lintegral_eq_of_isPiSystem ν ρ
    (Sys := Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet s} (measurableCylinders fun _ : ι => ℝ))
    ?_ (IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet isPiSystem_measurableCylinders)
    ⟨Set.univ, MeasurableSet.univ, Set.univ, huniv, Set.univ_prod_univ⟩ ?_
  · have h := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, generateFrom_measurableCylinders] at h
    exact h
  · rintro _ ⟨A, hA, T, hT, rfl⟩
    exact hbase A hA T hT

end LatticeProb
