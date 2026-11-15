import LatticeProb.LQG.ShiftedGridSideStrict
import LatticeProb.Prob.CorrelatedBMFixedLagNull
import LatticeProb.Prob.CorrelatedBMLevelNull

/-! # Strict sides for shifted Brownian grids -/

set_option autoImplicit false

open MeasureTheory Filter

namespace MatedCRTHarmonic.RouteM

open MatedCRTHarmonic.MatedCRT

/-- At a fixed positive mesh, almost every correlated Brownian path has strict
sides at almost every grid phase whenever it admits a matching Peanosphere. -/
theorem ae_sideStrict_time_translate_of_correlatedBM
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ → ℂ, Peanosphere ω η →
      ∀ᵐ c : ℝ ∂volume, SideStrict ε
        ⟨fun t => ω (t + c), ω.continuous.comp (by fun_prop)⟩ := by
  filter_upwards [LatticeProb.CorrelatedBM.ae_volume_grid_increments_eq_zero hμ hε,
    LatticeProb.CorrelatedBM.ae_volume_coordinate_levels_eq_zero hμ] with ω hinc hlevel
  intro η P
  apply P.ae_sideStrict_time_translate hε hinc
  intro i t _
  exact hlevel i (lrCoord i t ω)

end MatedCRTHarmonic.RouteM
