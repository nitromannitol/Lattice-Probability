import LatticeProb.LQG.InternalMetricUpperTailOneEps
import LatticeProb.Prob.PolynomialTailOfScaleFamily

/-!
# Polynomial upper tail of the internal distance of two sets

Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ > 0`, `h` a whole-plane GFF with circle averages `h_r(z)`, and `U₀` a
bounded open connected set containing two compact connected non-singletons `K₁, K₂`. For every `m > 0` there are
constants `C₀, K₀` such that for every `c ≥ C₀` and every scale `𝕣 > 0`,
`P[ c 𝕣^{ξ Q} e^{ξ h_𝕣(0)} < D(𝕣K₁, 𝕣K₂; 𝕣U₀) ] ≤ K₀ c^{-m}`,
where `Q = 2/γ + γ/2` and `D(·, ·; ·)` is the internal distance (upper bound of Proposition 3.1 of
Ding-Dubédat-Gwynne-Pfeffer-Sheffield).

The one-parameter bound `exists_measure_internalDist_gt_le` is converted into a polynomial tail by choosing `Λ`, the
circle-average parameter `q` and the exponent `M` in terms of `m`, and applying
`exists_polynomial_tail_of_scale_family`.
-/

namespace LatticeProb.LQG

open MeasureTheory Set Metric LatticeProb.Gauss LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.P31
open scoped ENNReal

/-- Choice of the circle-average parameter: for every `m, ξ, Λ > 0` there is `q > 0` with
`m (6 + 2Λ + ξ q) ≤ q² / 8 - 4`. -/
theorem exists_param_quadratic_dominates {m ξ Λ : ℝ} (hm : 0 < m) (hξ : 0 < ξ) (hΛ : 0 < Λ) :
    ∃ q : ℝ, 0 < q ∧ m * (6 + 2 * Λ + ξ * q) ≤ q ^ 2 / 8 - 4 := by
  have hB : 0 < m * (6 + 2 * Λ) := by positivity
  refine ⟨16 * m * ξ + 4 * (4 + m * (6 + 2 * Λ)) + 1, by positivity, ?_⟩
  set B : ℝ := m * (6 + 2 * Λ) with hBdef
  set q : ℝ := 16 * m * ξ + 4 * (4 + B) + 1 with hqdef
  have hmξ : 0 < m * ξ := mul_pos hm hξ
  have hq0 : 0 < q := by positivity
  have h2 : 16 * m * ξ ≤ q := by rw [hqdef]; linarith
  have h1 : 4 * (4 + B) ≤ q := by rw [hqdef]; linarith
  have h3 : 16 * m * ξ * q ≤ q * q := mul_le_mul_of_nonneg_right h2 hq0.le
  have h4 : (4 * (4 + B)) * (4 * (4 + B)) ≤ q * q := mul_self_le_mul_self (by positivity) h1
  have e : m * (6 + 2 * Λ + ξ * q) = B + m * ξ * q := by rw [hBdef]; ring
  rw [e]
  nlinarith [h3, h4, hB]

/-- **Polynomial upper tail of the internal distance of two sets.** See the module docstring. -/
theorem IsLQGMetric.exists_measure_internalDist_gt_le_poly {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) {U₀ K₁ K₂ : Set ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hU₀b : U₀ ⊆ ball (0 : ℂ) R₀) (hU₀ : IsOpen U₀) (hU₀c : IsConnected U₀) (hK₁ : IsCompact K₁)
    (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial) (hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂)
    (hK₂n : K₂.Nontrivial) (h₁U : K₁ ⊆ U₀) (h₂U : K₂ ⊆ U₀) (m : ℝ) (hm : 0 < m)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ C₀ K₀ : ℝ, 0 < C₀ ∧ ∀ c : ℝ, C₀ ≤ c → ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P {ω | ENNReal.ofReal (c * (𝕣 ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 𝕣 0))) <
          ⨅ u ∈ scaleSet 𝕣 0 K₁, ⨅ v ∈ scaleSet 𝕣 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 𝕣 0 U₀) u v} ≤ ENNReal.ofReal (K₀ * c ^ (-m)) := by
  classical
  obtain ⟨Λ, hΛ, hΛξ, hΛ2⟩ : ∃ Λ : ℝ, 1 < Λ ∧ ξ * lqgQ γ ≤ Λ ∧ 2 ≤ Λ :=
    ⟨max 2 (ξ * lqgQ γ), lt_of_lt_of_le one_lt_two (le_max_left _ _), le_max_right _ _, le_max_left _ _⟩
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨q, hq, hqm⟩ := exists_param_quadratic_dominates hm hξ hΛ0
  have ha : 0 < 6 + 2 * Λ + ξ * q := by positivity
  have hM : 0 < m * (6 + 2 * Λ + ξ * q) := mul_pos hm ha
  obtain ⟨A, K, C₄, ε₁, hA, hε₁, hP⟩ := h𝔇.exists_measure_internalDist_gt_le hξ hγ hR₀ hU₀b hU₀ hU₀c hK₁ hK₁c
    hK₁n hK₂ hK₂c hK₂n h₁U h₂U hM hq hΛ hΛξ hG hH hHC hHcirc
  exact exists_polynomial_tail_of_scale_family P
    (fun 𝕣 c => {ω | ENNReal.ofReal (c * (𝕣 ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 𝕣 0))) <
          ⨅ u ∈ scaleSet 𝕣 0 K₁, ⨅ v ∈ scaleSet 𝕣 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 𝕣 0 U₀) u v}) hA ha hε₁ le_rfl hqm
    (fun 𝕣 h𝕣 ε hε => hP 𝕣 h𝕣 ε hε)

end LatticeProb.LQG
