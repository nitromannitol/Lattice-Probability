import LatticeProb.Topology.FirstHitExitEuclidean
import LatticeProb.Topology.FirstExitBallReversalLaw

/-! # First-hit exit trace probabilities -/

set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A first-hit trace and its translated forward-exit trace have equal failure probability. -/
theorem measure_forwardExitOpenBallFailure_eq_firstHit
    {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : β → ℝ → ℂ)
    (z : ℂ) (ε : ℝ) (k : ℤ)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, f ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) :
    μ (forwardExitOpenBallFailure f ε k) =
      μ {ω | ¬ ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z (Real.exp (k : ℝ))})} := by
  apply measure_congr
  filter_upwards [hpath] with ω hω
  obtain ⟨hc, hp, hz, hs⟩ := hω
  have h := (firstHit_not_mem_forwardExitOpenBallFailure_iff f ω (η ω) z ε k
    hc hp hz hs).2
  apply propext
  simpa only [mem_ofPred_eq, not_not] using not_congr h

/-- A first-hit failure estimate controls finite forward-exit closed-ball failure. -/
theorem measure_forwardExitBallFailure_le_firstHit
    {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : β → ℝ → ℂ)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, f ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) :
    μ (forwardExitBallFailure f ε k) ≤
      μ {ω | ¬ ∃ w, ball w (ε * Real.exp (k : ℝ)) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z (Real.exp (k : ℝ))})} := by
  calc
    μ (forwardExitBallFailure f ε k) ≤ μ (forwardExitOpenBallFailure f ε k) :=
      measure_mono (forwardExitBallFailure_subset_open f hε k)
    _ = _ := measure_forwardExitOpenBallFailure_eq_firstHit μ f η z ε k hpath

end LatticeProb
