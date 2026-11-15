import LatticeProb.LQG.LogInsertionCircleBridge
import LatticeProb.LQG.ConeAreaSpatialAE

/-! # Identification of logarithmically inserted quantum area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric MatedCRTHarmonic

namespace LatticeProb.LQG

/-- The selected area of a logarithmically shifted whole-plane field agrees
almost surely with any dyadic LQG limit of its inserted circle averages. -/
theorem ae_lqgArea_addLogSing_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {γ α : ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α (fun ω r z => circleAvg (X ω) r z) μ) :
    ∀ᵐ ω ∂P, CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω)) = μ ω := by
  apply ae_lqgArea_eq_of_isLQGMeasure_ae hμ
  filter_upwards [ae_logInsertion_circleAvg hX α] with ω hω k
  exact hω (dyadicScale k) (by unfold dyadicScale; positivity)

end LatticeProb.LQG
