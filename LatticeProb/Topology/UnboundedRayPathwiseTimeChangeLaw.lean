import LatticeProb.Topology.UnboundedRayTimeChangeLaw

/-! # Curve laws under path-dependent time changes -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩

/-- A measurable path transformation preserves the local curve law when each
path is transformed by an increasing bijective change of clock. The clock may
depend on the path and need not be chosen measurably. -/
theorem curveLaw_map_pathwise_timeChange {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (F : Path d → Path d) (hF : Measurable F)
    (hclock : ∀ f, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, F f t = f (φ t)) :
    let : IsProbabilityMeasure (μ.map F) :=
      (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
    ∃ hFμ : ∀ᵐ (f : Path d) ∂(μ.map F), ¬ Bornology.IsBounded (Set.range f),
      curveLaw (μ.map F) hFμ = curveLaw μ hμ := by
  let : IsProbabilityMeasure (μ.map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
  have hrange (f : Path d) : Set.range (F f) = Set.range f := by
    obtain ⟨φ, hφ⟩ := hclock f
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, (hφ t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨φ.symm t, by rw [hφ, φ.apply_symm_apply]⟩
  have hFμ : ∀ᵐ (f : Path d) ∂(μ.map F), ¬ Bornology.IsBounded (Set.range f) := by
    apply (ae_map_iff hF.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).2
    filter_upwards [hμ] with f hf
    simpa only [hrange f] using hf
  refine ⟨hFμ, ?_⟩
  let G : UnboundedRay d → UnboundedRay d := fun f =>
    ⟨F f.1, by simpa only [hrange f.1] using f.2⟩
  have hG : Measurable G := by
    apply Measurable.subtype_mk
    exact hF.comp measurable_subtype_coe
  let ν := supportedLaw μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ
  have hν : ν.map Subtype.val = μ := map_supportedLaw μ _ hμ
  have hlift : (ν.map G).map Subtype.val = μ.map F := by
    rw [Measure.map_map measurable_subtype_coe hG]
    rw [← hν, Measure.map_map hF measurable_subtype_coe]
    rfl
  calc
    curveLaw (μ.map F) hFμ = (ν.map G).map project :=
      (map_project_eq_curveLaw (μ.map F) hFμ _ hlift).symm
    _ = ν.map (project ∘ G) := Measure.map_map continuous_project.measurable hG
    _ = ν.map project := by
      congr 1
      funext f
      obtain ⟨φ, hφ⟩ := hclock f.1
      have h : G f = timeChange f φ := by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        exact hφ t
      change project (G f) = project f
      rw [h, project_timeChange]
    _ = curveLaw μ hμ := map_project_eq_curveLaw μ hμ ν hν

end
end LatticeProb.UnboundedRayCurveSpace
