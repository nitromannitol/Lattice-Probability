import LatticeProb.Topology.FirstHitExitLaw
import LatticeProb.Topology.FirstExitBallReversalLaw

/-! # Reversed first-exit estimates from first-hit traces -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A reversed equal-law curve inherits a reference first-hit failure bound. -/
theorem measure_backwardExitBallFailure_le_firstHit_of_identDistrib_reverse
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) (ν : Measure γ)
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (h : γ → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : γ → ℝ → ℂ)
    (hrev : ∀ ω t, g ω t = f ω (-t))
    (hlaw : IdentDistrib g h μ ν) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hpath : ∀ᵐ ω ∂ν, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, h ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) :
    μ (backwardExitBallFailure f ε k) ≤
      ν {ω | ¬ ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z (Real.exp (k : ℝ))})} := by
  rw [← forwardExitBallFailure_eq_backward_of_reverse f g hrev ε k]
  exact measure_forwardExitBallFailure_le_firstHit_of_identDistrib μ ν g h η hlaw z hε k hpath

end LatticeProb
