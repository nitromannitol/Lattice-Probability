import LatticeProb.Topology.FirstHitExitProbability

/-! # First-hit exit estimates under equality in distribution -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- An equal-law curve inherits the reference curve's first-hit failure bound. -/
theorem measure_forwardExitBallFailure_le_firstHit_of_identDistrib
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) (ν : Measure γ)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (g : γ → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : γ → ℝ → ℂ)
    (hlaw : IdentDistrib f g μ ν) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hpath : ∀ᵐ ω ∂ν, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, g ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) :
    μ (forwardExitBallFailure f ε k) ≤
      ν {ω | ¬ ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z (Real.exp (k : ℝ))})} := by
  calc
    μ (forwardExitBallFailure f ε k) = ν (forwardExitBallFailure g ε k) :=
      hlaw.measure_mem_eq (measurableSet_forwardExitBallFailure measurable_id ε k)
    _ ≤ _ := measure_forwardExitBallFailure_le_firstHit ν g η z hε k hpath

end LatticeProb
