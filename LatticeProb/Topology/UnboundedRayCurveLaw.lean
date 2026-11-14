import LatticeProb.Topology.UnboundedRayProjectionBorel
import LatticeProb.Prob.SupportedLaw

/-! # Laws on local curve classes -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

variable {d : ℕ}

noncomputable section

local instance : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩

/-- A probability law on unbounded rays projects to a law on local curve classes. -/
noncomputable def curveLaw (μ : Measure (Path d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f)) :
    Measure (UnboundedRayCurveSpace d) :=
  (supportedLaw μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ).map project

/-- The projected law has total mass one. -/
instance curveLaw_isProbability (μ : Measure (Path d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f)) :
    IsProbabilityMeasure (curveLaw μ hμ) := by
  unfold curveLaw
  exact (Measure.isProbabilityMeasure_map_iff
    continuous_project.measurable.aemeasurable).2
      (supportedLaw_isProbability μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ)

/-- A projected Borel event is evaluated on the supported path law. -/
theorem curveLaw_apply (μ : Measure (Path d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    {A : Set (UnboundedRayCurveSpace d)} (hA : MeasurableSet A) :
    curveLaw μ hμ A =
      supportedLaw μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ (project ⁻¹' A) := by
  unfold curveLaw
  exact Measure.map_apply continuous_project.measurable hA

/-- Any unbounded-ray lift of the original law induces the same curve law. -/
theorem map_project_eq_curveLaw (μ : Measure (Path d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (ν : Measure (UnboundedRay d)) (hν : ν.map Subtype.val = μ) :
    ν.map project = curveLaw μ hμ := by
  rw [supportedLaw_unique μ {f : Path d | ¬ Bornology.IsBounded (Set.range f)} hμ ν hν]
  rfl

end

end LatticeProb.UnboundedRayCurveSpace
