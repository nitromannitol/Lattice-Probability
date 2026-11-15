import LatticeProb.Topology.UnboundedRayTimeChangeLaw

/-! # Coupled paths with a random change of clock -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩

/-- Coupled measurable rays related almost surely by an increasing bijective clock
have the same law on local curve classes. The clock need not be measurable. -/
theorem curveLaw_eq_of_ae_timeChange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (X Y : Ω → Path d) (hX : Measurable X) (hY : Measurable Y)
    (hXu : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (X ω)))
    (hclock : ∀ᵐ ω ∂P, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y ω t = X ω (φ t)) :
    let : IsProbabilityMeasure (P.map X) :=
      (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
    let : IsProbabilityMeasure (P.map Y) :=
      (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
    ∃ hx : ∀ᵐ (f : Path d) ∂(P.map X), ¬ Bornology.IsBounded (Set.range f),
    ∃ hy : ∀ᵐ (f : Path d) ∂(P.map Y), ¬ Bornology.IsBounded (Set.range f),
      curveLaw (P.map X) hx = curveLaw (P.map Y) hy := by
  let : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  let S : Set Ω := {ω | ¬ Bornology.IsBounded (Set.range (X ω)) ∧
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y ω t = X ω (φ t)}
  have hS : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [hXu, hclock] with ω hu hc
    exact ⟨hu, hc⟩
  have hrange (ω : S) : Set.range (Y ω) = Set.range (X ω) := by
    obtain ⟨φ, hφ⟩ := ω.2.2
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, (hφ t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨φ.symm t, by rw [hφ, φ.apply_symm_apply]⟩
  let A : S → UnboundedRay d := fun ω => ⟨X ω, ω.2.1⟩
  let B : S → UnboundedRay d := fun ω =>
    ⟨Y ω, by simpa only [hrange ω] using ω.2.1⟩
  have hA : Measurable A := by
    apply Measurable.subtype_mk
    exact hX.comp measurable_subtype_coe
  have hB : Measurable B := by
    apply Measurable.subtype_mk
    exact hY.comp measurable_subtype_coe
  have hYu : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (Y ω)) := by
    filter_upwards [hS] with ω hω
    simpa only [hrange ⟨ω, hω⟩] using hω.1
  have hx : ∀ᵐ (f : Path d) ∂(P.map X), ¬ Bornology.IsBounded (Set.range f) :=
    (ae_map_iff hX.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).2 hXu
  have hy : ∀ᵐ (f : Path d) ∂(P.map Y), ¬ Bornology.IsBounded (Set.range f) :=
    (ae_map_iff hY.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).2 hYu
  refine ⟨hx, hy, ?_⟩
  let ν := supportedLaw P S hS
  have hν : ν.map Subtype.val = P := map_supportedLaw P S hS
  have hAlift : (ν.map A).map Subtype.val = P.map X := by
    rw [Measure.map_map measurable_subtype_coe hA, ← hν,
      Measure.map_map hX measurable_subtype_coe]
    rfl
  have hBlift : (ν.map B).map Subtype.val = P.map Y := by
    rw [Measure.map_map measurable_subtype_coe hB, ← hν,
      Measure.map_map hY measurable_subtype_coe]
    rfl
  calc
    curveLaw (P.map X) hx = (ν.map A).map project :=
      (map_project_eq_curveLaw (P.map X) hx _ hAlift).symm
    _ = ν.map (project ∘ A) := Measure.map_map continuous_project.measurable hA
    _ = ν.map (project ∘ B) := by
      congr 1
      funext ω
      obtain ⟨φ, hφ⟩ := ω.2.2
      have h : B ω = timeChange (A ω) φ := by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        exact hφ t
      change project (A ω) = project (B ω)
      rw [h, project_timeChange]
    _ = (ν.map B).map project := (Measure.map_map continuous_project.measurable hB).symm
    _ = curveLaw (P.map Y) hy := map_project_eq_curveLaw (P.map Y) hy _ hBlift

end
end LatticeProb.UnboundedRayCurveSpace
