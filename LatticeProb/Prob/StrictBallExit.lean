import LatticeProb.Prob.BallExitRadius
import LatticeProb.Prob.ContinuousPathExitConfinement

/-! # Strict separation of concentric ball exit times -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- A continuous path started in the smaller of two concentric balls exits the
smaller ball strictly before the larger one, provided the smaller exit is finite. -/
theorem openExitTime_ball_lt_of_lt {Ω E : Type*} [PseudoMetricSpace E]
    (X : ℝ≥0 → Ω → E) (ω : Ω) (z : E) {r R : ℝ} (hrR : r < R)
    (hc : Continuous fun t => X t ω) (hstart : X 0 ω ∈ ball z r)
    (hfin : openExitTime X (ball z r) ω ≠ ⊤) :
    openExitTime X (ball z r) ω < openExitTime X (ball z R) ω := by
  have hle := monotone_openExitTime_ball X ω z hrR.le
  apply lt_of_le_of_ne hle
  intro heq
  change openExitTime X (ball z r) ω = openExitTime X (ball z R) ω at heq
  have houter : openExitTime X (ball z R) ω ≠ ⊤ := by
    rw [← heq]
    exact hfin
  have ht : ((openExitTime X (ball z r) ω).toNNReal : ℝ≥0∞) ≤
      openExitTime X (ball z r) ω := by
    rw [ENNReal.coe_toNNReal hfin]
  have hclosed := mem_closed_of_le_openExitTime isOpen_ball isClosed_closedBall
    ball_subset_closedBall hc (ball_subset_closedBall hstart) ht
  have hinside : X (openExitTime X (ball z r) ω).toNNReal ω ∈ ball z R := by
    exact (mem_ball).2 (lt_of_le_of_lt (mem_closedBall.mp hclosed) hrR)
  have hout := openExitTime_not_mem (B := X) (ω := ω) (U := ball z R)
    isOpen_ball hc houter
  rw [← heq] at hout
  exact hout hinside

/-- Almost-sure finite exit from the larger ball gives strictly ordered exits
when the continuous path starts in the smaller ball almost surely. -/
theorem ae_openExitTime_ball_lt_of_lt {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : MeasureTheory.Measure Ω)
    (X : ℝ≥0 → Ω → E) (z : E) {r R : ℝ} (hrR : r < R)
    (hc : ∀ᵐ ω ∂μ, Continuous fun t => X t ω)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z r)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, openExitTime X (ball z r) ω < openExitTime X (ball z R) ω := by
  filter_upwards [hc, hstart, hfin] with ω hcω hstartω hfinω
  have hinner : openExitTime X (ball z r) ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfinω (monotone_openExitTime_ball X ω z hrR.le)
  exact openExitTime_ball_lt_of_lt X ω z hrR hcω hstartω hinner

end LatticeProb
