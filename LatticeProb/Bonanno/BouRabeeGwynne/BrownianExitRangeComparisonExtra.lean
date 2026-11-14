/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitRangeComparison at commit fdb5cad; selected declarations and adapted import. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRangeComparison

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma mem_cthickening_of_le_outerExit {d : ℕ} (U : Set (Euc d)) (δ : ℝ)
    {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ thickening δ U)
    (hfinite : continuousExitTime (thickening δ U) z ω ≠ ∞) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime (thickening δ U) z ω) :
    z + ω t ∈ cthickening δ U :=
  closure_thickening_subset_cthickening δ U
    (mem_closure_of_le_continuousExitTime isOpen_thickening hstart hfinite ht)

theorem stoppedBrownianRepresentative_dist_le_of_exit_le {d : ℕ}
    (U : Set (Euc d)) (p z : Euc d) (R : ℝ) (ω : BrownianPath d)
    (hstart : z + ω 0 ∈ ball p R)
    (hfinite : continuousExitTime (ball p R) z ω ≠ ∞)
    (hle : continuousExitTime U z ω ≤ continuousExitTime (ball p R) z ω)
    (u : unitInterval) :
    dist (stoppedBrownianRepresentative U z ω u) z ≤ R + dist z p := by
  let t : ℝ≥0 := ⟨(u : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg u.property.1 (NNReal.coe_nonneg _)⟩
  have hfi := ne_top_of_le_ne_top hfinite hle
  have ht : t ≤ (continuousExitTime U z ω).toNNReal :=
    mul_le_of_le_one_left (NNReal.coe_nonneg _) u.property.2
  have ht' : (t : ℝ≥0∞) ≤ continuousExitTime (ball p R) z ω := by
    apply le_trans _ hle
    simpa only [ENNReal.coe_toNNReal hfi] using ENNReal.coe_le_coe.mpr ht
  have hmem : z + ω t ∈ closedBall p R :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall)
      (mem_closure_of_le_continuousExitTime isOpen_ball hstart hfinite ht')
  change dist (z + ω t) z ≤ R + dist z p
  calc
    dist (z + ω t) z ≤ dist (z + ω t) p + dist p z := dist_triangle _ _ _
    _ ≤ R + dist z p := add_le_add (mem_closedBall.mp hmem)
      (le_of_eq (dist_comm p z))


end BouRabeeGwynne
