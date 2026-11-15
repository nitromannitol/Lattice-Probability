import LatticeProb.Topology.FirstExitBallTranslate
import LatticeProb.Topology.ProperCurveFiniteExit
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window

/-! # First-hit exit traces of proper plane curves -/

set_option autoImplicit false

open Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A first-hit exit trace and its translated trace contain balls of the same radii. -/
theorem firstHit_exitTrace_ball_iff (η : ℝ → ℂ) (z : ℂ) (r R : ℝ)
    (hη : Continuous η) (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hz : z ∈ range η) :
    η (MatedCRTHarmonic.GMS4b.hitTime η z) = z ∧
    ((∃ w, ball w R ⊆ η '' Icc (MatedCRTHarmonic.GMS4b.hitTime η z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime η z ≤ t ∧ η t ∉ ball z r})) ↔
     ∃ w, ball w R ⊆ (fun s : ℝ => η (MatedCRTHarmonic.GMS4b.hitTime η z + s) - z) ''
      Icc 0 ((openExitTime (fun s (_ : Unit) =>
        η (MatedCRTHarmonic.GMS4b.hitTime η z + (s : ℝ)) - z)
        (ball 0 r) ()).toNNReal : ℝ)) := by
  refine ⟨MatedCRTHarmonic.GMS4b.hitTime_spec hη hproper hz, ?_⟩
  apply exists_ball_subset_firstExitTrace_iff_shifted η _ z r R hη
  exact (openExitTime_ball_ne_top_of_tendsto_cocompact η hproper _ z r).1

end LatticeProb
