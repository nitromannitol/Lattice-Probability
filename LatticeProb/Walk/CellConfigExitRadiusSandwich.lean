import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import LatticeProb.Walk.CellConfigRepresentativeDistance

/-! # Ball exit times under bounded perturbations -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace LatticeProb

/-- Uniformly close paths have ball exit times bracketed by the exit times
of the reference path from balls with radii shifted by the error. -/
theorem openExitTime_ball_sandwich_of_dist_le {Ω E : Type*} [PseudoMetricSpace E]
    (f g : ℝ≥0 → Ω → E) (ω : Ω) (z : E) (R δ : ℝ)
    (hclose : ∀ t, dist (f t ω) (g t ω) ≤ δ) :
    openExitTime f (Metric.ball z (R - δ)) ω ≤
        openExitTime g (Metric.ball z R) ω ∧
      openExitTime g (Metric.ball z R) ω ≤
        openExitTime f (Metric.ball z (R + δ)) ω := by
  constructor
  · unfold openExitTime
    apply le_iInf
    intro t
    have hout : f t.val ω ∉ Metric.ball z (R - δ) := by
      have ht : R ≤ dist (g t.val ω) z := by
        simpa only [Metric.mem_ball, not_lt] using t.property
      simp only [Metric.mem_ball, not_lt]
      have htri := dist_triangle (g t.val ω) (f t.val ω) z
      have hc := hclose t.val
      rw [dist_comm (g t.val ω) (f t.val ω)] at htri
      linarith
    exact iInf_le (fun s : {s : ℝ≥0 // f s ω ∉ Metric.ball z (R - δ)} =>
      (s.val : ℝ≥0∞)) ⟨t.val, hout⟩
  · unfold openExitTime
    apply le_iInf
    intro t
    have hout : g t.val ω ∉ Metric.ball z R := by
      have ht : R + δ ≤ dist (f t.val ω) z := by
        simpa only [Metric.mem_ball, not_lt] using t.property
      simp only [Metric.mem_ball, not_lt]
      have htri := dist_triangle (f t.val ω) (g t.val ω) z
      linarith [hclose t.val]
    exact iInf_le (fun s : {s : ℝ≥0 // g s ω ∉ Metric.ball z R} =>
      (s.val : ℝ≥0∞)) ⟨t.val, hout⟩

end LatticeProb

namespace LatticeProb.CellConfigInterpolation

open ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne

/-- Nearby representatives bracket the interpolated walk's ball exit by
neighboring-radius exits for the reference representatives. -/
theorem continuousExitTime_interpolatedWalk_sandwich
    (H : CellConfig) (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    (ε : ℝ≥0) (z : Plane) (R : ℝ) :
    BouRabeeGwynne.continuousExitTime (Metric.ball z (R - (ε : ℝ) * r)) 0 (H.interpolatedWalk p ε ω) ≤
        BouRabeeGwynne.continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk q ε ω) ∧
      BouRabeeGwynne.continuousExitTime (Metric.ball z R) 0 (H.interpolatedWalk q ε ω) ≤
        BouRabeeGwynne.continuousExitTime (Metric.ball z (R + (ε : ℝ) * r)) 0 (H.interpolatedWalk p ε ω) := by
  have h := openExitTime_ball_sandwich_of_dist_le
    (fun t (_ : Unit) => (0 : Plane) + (H.interpolatedWalk p ε ω) t)
    (fun t (_ : Unit) => (0 : Plane) + (H.interpolatedWalk q ε ω) t) () z R ((ε : ℝ) * r)
    (fun t => by simpa only [zero_add] using
      dist_interpolatedWalk_le_of_dist_representatives_le H p q ω hpos hunb hclose ε t)
  exact h

end LatticeProb.CellConfigInterpolation
