import LatticeProb.Topology.UnboundedRayTimeChange
import LatticeProb.Topology.UnboundedRayCurveLaw
import LatticeProb.Prob.ContinuousMapUnboundedRange

/-! # Curve laws under time changes -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩

/-- An increasing time change is measurable on unbounded rays. -/
theorem measurable_timeChange {d : ℕ} (φ : ℝ≥0 ≃o ℝ≥0) :
    Measurable (fun f : UnboundedRay d => timeChange f φ) := by
  apply Measurable.subtype_mk
  change Measurable (fun f : UnboundedRay d =>
    f.1.comp ⟨φ, φ.continuous⟩)
  exact (ContinuousMap.continuous_precomp ⟨φ, φ.continuous⟩).measurable.comp
    measurable_subtype_coe

/-- A measurable change of clock preserves the law on unbounded curve classes. -/
theorem curveLaw_map_timeChange {d : ℕ} (μ : Measure (Path d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (φ : ℝ≥0 ≃o ℝ≥0) (F : Path d → Path d) (hF : Measurable F)
    (hFval : ∀ f t, F f t = f (φ t)) :
    let : IsProbabilityMeasure (μ.map F) :=
      (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
    ∃ hFμ : ∀ᵐ (f : Path d) ∂(μ.map F), ¬ Bornology.IsBounded (Set.range f),
      curveLaw (μ.map F) hFμ = curveLaw μ hμ := by
  let : IsProbabilityMeasure (μ.map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).2 inferInstance
  have hrange (f : Path d) : Set.range (F f) = Set.range f := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, (hFval f t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨φ.symm t, by rw [hFval, φ.apply_symm_apply]⟩
  have hFμ : ∀ᵐ (f : Path d) ∂(μ.map F), ¬ Bornology.IsBounded (Set.range f) := by
    apply (ae_map_iff hF.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).2
    filter_upwards [hμ] with f hf
    simpa only [hrange f] using hf
  refine ⟨hFμ, ?_⟩
  let ν := supportedLaw μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ
  have hν : ν.map Subtype.val = μ := map_supportedLaw μ _ hμ
  have hlift : (ν.map (fun f => timeChange f φ)).map Subtype.val = μ.map F := by
    rw [Measure.map_map measurable_subtype_coe (measurable_timeChange φ)]
    rw [← hν, Measure.map_map hF measurable_subtype_coe]
    congr 1
    funext f
    apply ContinuousMap.ext
    intro t
    exact (hFval f.1 t).symm
  calc
    curveLaw (μ.map F) hFμ = (ν.map (fun f => timeChange f φ)).map project :=
      (map_project_eq_curveLaw (μ.map F) hFμ _ hlift).symm
    _ = ν.map (project ∘ fun f => timeChange f φ) :=
      Measure.map_map continuous_project.measurable (measurable_timeChange φ)
    _ = ν.map project := by
      congr 1
      funext f
      exact project_timeChange f φ
    _ = curveLaw μ hμ := map_project_eq_curveLaw μ hμ ν hν

end
end LatticeProb.UnboundedRayCurveSpace
