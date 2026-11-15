import LatticeProb.LQG.SingularApproximantUniformDyadic
import LatticeProb.LQG.NormalizedCircleAllScales
import LatticeProb.LQG.GMCOriginGrowth

/-! # Almost-sure dyadic bounds for singular approximants -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- On a common event, the selected circle process satisfies the uniform
singular approximant bound at every sufficiently small admissible dyadic ball. -/
theorem ae_exists_singular_approximant_uniform_dyadic_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, 0 < n ∧ ∃ J₀ : ℕ, ∀ J k : ℕ,
      dyadicScale J ≤ r → J₀ ≤ J / n →
      lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
          Real.exp (-(Real.log 2) * J)))
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
            (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
              (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)))))) := by
  have hcircle : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, z ∈ ball (0 : ℂ) r →
      c ω (dyadicScale k) z ≤ C + (2 + δ) * Real.log (dyadicScale k)⁻¹ :=
    ae_exists_all_dyadic_circle_le_of_normalized_gff hX hc heq hδ hρ hrρ
  filter_upwards [hcircle, hG.ae_eventually_exp_circle_mul_maximal_dilated_le hγ hγ2] with ω hcircle hZ
  obtain ⟨C, hC, hcircle⟩ := hcircle
  exact ⟨C, hC, exists_singular_approximant_uniform_dyadic_bound hγ hαQ (c ω) hcircle hZ⟩

end LatticeProb.LQG
