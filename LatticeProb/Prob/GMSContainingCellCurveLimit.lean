import LatticeProb.Prob.GMSRealMeshDiameter
import LatticeProb.Prob.CellConfigTranslatedCurveLimit

/-! # Uniform containing-cell limits for cell configuration laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open ReflectedGMS ReflectedGMS.GMS
open LatticeProb.UnboundedRayIntervalIntegrand
open LatticeProb.UnboundedRayCurveSpace

namespace LatticeProb.CellConfigContainingCell

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩
attribute [local instance] dUnifMetricSpace

/-- On a common full-measure set of configurations, a uniform selected-cell
limit implies a uniform limit for every containing cell. The selected-cell
limit remains an assumption for each configuration. -/
theorem ae_all_containing_cell_translated_curveLaw_convergence
    {ν : Measure GMSSpace} [IsProbabilityMeasure ν]
    (hL : ConnectedAlongLines ν) (hMT : MassTransport ν) (hFE : FiniteExpectation ν) :
    ∀ᵐ H ∂ν, ∀ (W : ℝ → Cell → ProbabilityMeasure (UnboundedRayCurveSpace 2))
      (μ : Measure (Path 2)) [IsProbabilityMeasure μ]
      (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f)) (R : ℝ),
      (∀ t > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
        ∀ z ∈ closedBall (0 : Plane) (R + 1),
          levyProkhorovDist (W ε (containingCell (H, ε⁻¹ • z)) : Measure (UnboundedRayCurveSpace 2))
            (translatedCurveProbability μ hμ z : Measure (UnboundedRayCurveSpace 2)) < t) →
      ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
        ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
          ε⁻¹ • z ∈ (K.1 : Set Plane) →
            levyProkhorovDist (W ε K.1 : Measure (UnboundedRayCurveSpace 2))
              (translatedCurveProbability μ hμ z : Measure (UnboundedRayCurveSpace 2)) < δ := by
  filter_upwards [GMSRealMeshDiameter.ae_scaled_cell_diam_lt hL hMT hFE] with H hdiam
  intro W μ hprob hμ R hselected
  let : IsProbabilityMeasure μ := hprob
  apply all_containing_cell_translated_curveLaw_convergence H W μ hμ R ?_ hselected
  intro η hη
  obtain ⟨ε₀, hε₀, h⟩ := hdiam R η hη
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀ z hz K hzK
  exact h ε hε hε₀ z hz K.1 K.2 hzK

end LatticeProb.CellConfigContainingCell
