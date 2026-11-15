import LatticeProb.LQG.SingularApproximantVanishing

/-! # Pullback of singular approximant vanishing -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- The common dyadic vanishing event transfers from a mapped field law to the
original sample space, uniformly over sequences of regularization scales. -/
theorem ae_tendsto_singular_approximant_dyadic_ball_of_map
    {Ω Ω₁ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    {P : Measure Ω} {U : Ω → Ω₁} (hU : AEMeasurable U P)
    {X : Ω₁ → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X (P.map U))
    {hC : Ω₁ → (ℂ → ℝ) → ℝ} {c : Ω₁ → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF (P.map U) hC c)
    (hc : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ x ∂(P.map U), c x r z = LQGMetric.circleAvg (X x) r z)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ → ℕ,
      Tendsto (fun J => lqgApprox γ (fieldCircleAverage α (c (U ω)))
        (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0) := by
  have h : ∀ᵐ x ∂(P.map U), ∀ k : ℕ → ℕ,
      Tendsto (fun J => lqgApprox γ (fieldCircleAverage α (c x))
        (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0) :=
    ae_tendsto_singular_approximant_dyadic_ball hX hG hc heq hγ hγ2 hαQ
      (δ := 1) (r := 1 / 4) (ρ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ae_of_ae_map hU h

end LatticeProb.LQG
