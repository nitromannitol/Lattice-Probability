import LatticeProb.Topology.TranslatedCurveLawContinuity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform continuity of translated local curve laws -/

set_option autoImplicit false

open MeasureTheory Set
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩
attribute [local instance] dUnifMetricSpace

/-- The translated curve-law map is uniformly continuous on compact sets in the
Lévy–Prokhorov metric. -/
theorem uniformContinuousOn_translated_curveLaw {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    UniformContinuousOn (fun z => LevyProkhorov.ofMeasure (translatedCurveProbability μ hμ z)) K := by
  apply hK.uniformContinuousOn_of_continuous
  exact (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
    (continuous_translated_curveLaw μ hμ)).continuousOn

/-- A single starting-point tolerance controls Lévy–Prokhorov distances over a
compact set. -/
theorem translated_curveLaw_levyProkhorovDist_lt {d : ℕ} (μ : Measure (Path d))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ w ∈ K, dist z w < δ →
      levyProkhorovDist (translatedCurveProbability μ hμ z : Measure (UnboundedRayCurveSpace d))
        (translatedCurveProbability μ hμ w : Measure (UnboundedRayCurveSpace d)) < ε := by
  obtain ⟨δ, hδ, hδprop⟩ := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_translated_curveLaw μ hμ hK) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz w hw hzw
  simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hδprop z hz w hw hzw

end
end LatticeProb.UnboundedRayCurveSpace
