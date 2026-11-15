import LatticeProb.LQG.SingularApproximantCommonEvent

/-! # Vanishing singular approximant masses on shrinking dyadic balls -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- The common dyadic estimate implies vanishing on shrinking balls, uniformly
in the choice of dyadic regularization scale. -/
theorem ae_tendsto_singular_approximant_dyadic_ball
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ → ℕ,
      Tendsto (fun J => lqgApprox γ (fieldCircleAverage α (c ω))
        (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0) := by
  filter_upwards [ae_exists_singular_approximant_uniform_dyadic_bound
    hX hG hc heq hγ hγ2 hαQ hδ hρ hrρ] with ω hω
  obtain ⟨C, hC, n, hn, J₀, hbound⟩ := hω
  have hdiv : Tendsto (fun J : ℕ => J / n) atTop atTop := by
    rw [Tendsto, map_div_atTop_eq_nat n hn]
  have ha : 0 < γ * (lqgQ γ - α) * Real.log 2 / 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hq0 : 0 ≤ Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) :=
    (Real.exp_pos _).le
  have hq1 : Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr ha)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hdiv
  have hfirst : Tendsto (fun J : ℕ => ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
      Real.exp (-(Real.log 2) * J))) atTop (𝓝 0) := by
    have he : Tendsto (fun J : ℕ => Real.exp (-(Real.log 2) * J)) atTop (𝓝 0) := by
      have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hl) using 1
      simp only [Function.comp_def, neg_mul]
    simpa using ENNReal.tendsto_ofReal (he.const_mul (Real.pi * Real.exp (γ * C)))
  have hsecond : Tendsto (fun J : ℕ => ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
      (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
        (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)))))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((hpow.div_const _).const_mul
      (Real.exp (γ * (|α| * Real.log 2))))
  have hmax := hfirst.max hsecond
  simp only [max_self] at hmax
  have hscale : ∀ᶠ J : ℕ in atTop, dyadicScale J ≤ r := by
    have ht : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (ht.eventually (Iio_mem_nhds hr)).mono fun _ h => h.le
  have hcut : ∀ᶠ J : ℕ in atTop, J₀ ≤ J / n := hdiv.eventually_ge_atTop J₀
  intro k
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmax
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [hscale, hcut] with J hJ hJ₀
    exact hbound J (k J) hJ hJ₀

end LatticeProb.LQG
