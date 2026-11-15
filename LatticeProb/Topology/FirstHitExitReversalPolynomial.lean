import LatticeProb.Topology.FirstHitExitPolynomial
import LatticeProb.Topology.FirstExitBallReversalLaw

/-! # Polynomial bounds for reversed first-hit exit traces -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Under a reversed equal-law coupling, the reference first-hit estimate gives
uniform polynomial bounds for the backward closed-ball failure event. -/
theorem measure_backwardExitBallFailure_le_polynomial_of_firstHit
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) (ν : Measure γ)
    (f g : β → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (h : γ → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : γ → ℝ → ℂ)
    (hrev : ∀ ω t, g ω t = f ω (-t))
    (hlaw : IdentDistrib g h μ ν) (z : ℂ) {a₀ a₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 < a₁)
    (hpath : ∀ᵐ ω ∂ν, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, h ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z))
    (hbound : ∀ ρ : ℝ, 0 < ρ → ∀ δ ∈ Ioo (0 : ℝ) 1,
      ν {ω | ¬ ∃ w, ball w (δ * ρ) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z ρ})} ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ / δ)))
    (n : ℕ) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (k : ℤ) :
    μ (backwardExitBallFailure f δ k) ≤
      ENNReal.ofReal ((a₀ * ((n.factorial : ℝ) / a₁ ^ n)) * δ ^ (n : ℝ)) := by
  rw [measure_backwardExitBallFailure_eq_of_identDistrib_reverse μ ν f g h hrev hlaw δ k]
  exact measure_forwardExitBallFailure_le_polynomial_of_firstHit ν h η z
    ha₀ ha₁ hpath hbound n hδ k

/-- A bound uniform in the scale on a right neighborhood of zero gives the
eventual uniform bound used in small-scale limits. -/
theorem eventually_uniform_scale_bound {β : Type*} [MeasurableSpace β]
    (μ : Measure β) (E : ℝ → ℤ → Set β) (C p : ℝ)
    (h : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ k,
      μ (E δ k) ≤ ENNReal.ofReal (C * δ ^ p)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ k, μ (E δ k) ≤ ENNReal.ofReal (C * δ ^ p) := by
  filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
  exact h δ hδ

end LatticeProb
