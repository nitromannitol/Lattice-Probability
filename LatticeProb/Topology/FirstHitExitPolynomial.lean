import LatticeProb.Topology.FirstHitExitProbability
import LatticeProb.Analysis.ExponentialInversePower

/-! # Polynomial bounds for first-hit exit traces -/

set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A uniform exponential first-hit estimate yields a polynomial bound at every
integer exponential scale for the forward closed-ball failure event. -/
theorem measure_forwardExitBallFailure_le_polynomial_of_firstHit
    {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (f : β → C(ℝ, EuclideanSpace ℝ (Fin 2))) (η : β → ℝ → ℂ)
    (z : ℂ) {a₀ a₁ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 < a₁)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧ z ∈ range (η ω) ∧
      ∀ s, f ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z))
    (hbound : ∀ ρ : ℝ, 0 < ρ → ∀ δ ∈ Ioo (0 : ℝ) 1,
      μ {ω | ¬ ∃ w, ball w (δ * ρ) ⊆
        η ω '' Icc (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
            η ω t ∉ ball z ρ})} ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ / δ)))
    (n : ℕ) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (k : ℤ) :
    μ (forwardExitBallFailure f δ k) ≤
      ENNReal.ofReal ((a₀ * ((n.factorial : ℝ) / a₁ ^ n)) * δ ^ (n : ℝ)) := by
  have hexp : Real.exp (-a₁ / δ) ≤
      ((n.factorial : ℝ) / a₁ ^ n) * δ ^ (n : ℝ) := by
    simpa only [Real.rpow_neg hδ.1.le, Real.rpow_one, one_mul, div_eq_mul_inv,
      neg_mul] using (exp_neg_inv_rpow_le ha₁ hδ.1 n (a := (1 : ℝ)))
  calc
    μ (forwardExitBallFailure f δ k) ≤ _ :=
      measure_forwardExitBallFailure_le_firstHit μ f η z hδ.1 k hpath
    _ ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ / δ)) :=
      hbound (Real.exp (k : ℝ)) (Real.exp_pos _) δ hδ
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp ha₀)

end LatticeProb
