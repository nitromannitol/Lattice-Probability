import Mathlib

/-!
# The law of a real process is determined by finitely many coordinates

Two probability measures on the product space `ι → ℝ` (with the product σ-algebra) coincide if
the integrals of all bounded continuous functions of finitely many coordinates agree.  The
statement is given for the laws `μ₁.map X₁` and `μ₂.map X₂` of two measurable maps into `ι → ℝ`.

* `LatticeProb.map_eq_of_forall_integral_comp_fin_eq`: the statement above.
-/

open MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

namespace LatticeProb

variable {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **The law of a real process is determined by its finite-dimensional bounded continuous
functionals.**  If `X₁ : Ω₁ → ι → ℝ` and `X₂ : Ω₂ → ι → ℝ` are measurable and, for every finite
family `t` of indices and every bounded continuous `f` on `Fin n → ℝ`, the expectations of
`f (X₁ · (t i))` and `f (X₂ · (t i))` agree, then `X₁` and `X₂` have the same law. -/
theorem map_eq_of_forall_integral_comp_fin_eq {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {X₁ : Ω₁ → ι → ℝ} {X₂ : Ω₂ → ι → ℝ}
    (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (h : ∀ (n : ℕ) (t : Fin n → ι) (f : (Fin n → ℝ) →ᵇ ℝ),
      ∫ ω, f (fun i => X₁ ω (t i)) ∂μ₁ = ∫ ω, f (fun i => X₂ ω (t i)) ∂μ₂) :
    μ₁.map X₁ = μ₂.map X₂ := by
  have hp₁ : IsProbabilityMeasure (μ₁.map X₁) :=
    (Measure.isProbabilityMeasure_map_iff h₁.aemeasurable).2 inferInstance
  have hp₂ : IsProbabilityMeasure (μ₂.map X₂) :=
    (Measure.isProbabilityMeasure_map_iff h₂.aemeasurable).2 inferInstance
  refine ext_of_generate_finite _ (generateFrom_measurableCylinders (α := fun _ : ι => ℝ)).symm
    isPiSystem_measurableCylinders ?_ (by simp)
  intro A hA
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hA
  have hr : Measurable fun x : ι → ℝ => fun i : I => x i := Finset.measurable_restrict I
  have hcyl : cylinder I S = (fun x : ι → ℝ => fun i : I => x i) ⁻¹' S := rfl
  have hr₁ : Measurable fun ω => fun i : I => X₁ ω i := hr.comp h₁
  have hr₂ : Measurable fun ω => fun i : I => X₂ ω i := hr.comp h₂
  have e₁ : (μ₁.map X₁) (cylinder I S) = (μ₁.map fun ω => fun i : I => X₁ ω i) S := by
    rw [hcyl, Measure.map_apply h₁ (hr hS), Measure.map_apply hr₁ hS]
    rfl
  have e₂ : (μ₂.map X₂) (cylinder I S) = (μ₂.map fun ω => fun i : I => X₂ ω i) S := by
    rw [hcyl, Measure.map_apply h₂ (hr hS), Measure.map_apply hr₂ hS]
    rfl
  rw [e₁, e₂]
  have hp₁' : IsProbabilityMeasure (μ₁.map fun ω => fun i : I => X₁ ω i) :=
    (Measure.isProbabilityMeasure_map_iff hr₁.aemeasurable).2 inferInstance
  have hp₂' : IsProbabilityMeasure (μ₂.map fun ω => fun i : I => X₂ ω i) :=
    (Measure.isProbabilityMeasure_map_iff hr₂.aemeasurable).2 inferInstance
  congr 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hr₁.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hr₂.aemeasurable f.continuous.aestronglyMeasurable]
  let e : I ≃ Fin I.card := I.equivFin
  have := h I.card (fun j => (e.symm j : ι))
    (f.compContinuous ⟨fun g i => g (e i), continuous_pi fun i => continuous_apply _⟩)
  simpa using this

end LatticeProb
