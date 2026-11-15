import LatticeProb.Prob.CellConfigUniformStartLimit
import LatticeProb.Topology.TranslatedCurveLawUniformContinuity

/-! # Uniform starting-cell limits for translated curve laws -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open ReflectedGMS ReflectedGMS.GMS
open LatticeProb.UnboundedRayIntervalIntegrand
open LatticeProb.UnboundedRayCurveSpace

namespace LatticeProb.CellConfigContainingCell

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩
attribute [local instance] dUnifMetricSpace

/-- Uniform convergence for selected cells extends to all containing cells
when the limiting law is a translated unbounded path law and scaled cell
diameters vanish uniformly. -/
theorem all_containing_cell_translated_curveLaw_convergence
    (H : GMSSpace) (W : ℝ → Cell → ProbabilityMeasure (UnboundedRayCurveSpace 2))
    (μ : Measure (Path 2)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f)) (R : ℝ)
    (hdiam : ∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
        ε⁻¹ • z ∈ (K.1 : Set Plane) → ε * Metric.diam (K.1 : Set Plane) < η)
    (hselected : ∀ t > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) (R + 1),
        levyProkhorovDist (W ε (containingCell (H, ε⁻¹ • z)) : Measure (UnboundedRayCurveSpace 2))
          (translatedCurveProbability μ hμ z : Measure (UnboundedRayCurveSpace 2)) < t) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
        ε⁻¹ • z ∈ (K.1 : Set Plane) →
          levyProkhorovDist (W ε K.1 : Measure (UnboundedRayCurveSpace 2))
            (translatedCurveProbability μ hμ z : Measure (UnboundedRayCurveSpace 2)) < δ := by
  have hB := uniformContinuousOn_translated_curveLaw μ hμ
    (isCompact_closedBall (0 : Plane) (R + 1))
  have hselected' : ∀ t > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) (R + 1),
        dist (LevyProkhorov.ofMeasure (W ε (containingCell (H, ε⁻¹ • z))))
          (LevyProkhorov.ofMeasure (translatedCurveProbability μ hμ z)) < t := by
    simpa only [LevyProkhorov.dist_probabilityMeasure_def] using hselected
  have h := all_containing_cell_uniform_convergence H
    (fun ε K => LevyProkhorov.ofMeasure (W ε K))
    (fun z => LevyProkhorov.ofMeasure (translatedCurveProbability μ hμ z)) R
    hB hdiam hselected'
  simpa only [LevyProkhorov.dist_probabilityMeasure_def] using h

end LatticeProb.CellConfigContainingCell
