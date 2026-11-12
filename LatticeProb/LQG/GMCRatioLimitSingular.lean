import LatticeProb.LQG.GMCRatioLimitMeasure
import LatticeProb.LQG.LQGSingularScaledLimit

/-!
# The LQG measure with a logarithmic singularity along every ratio of the dyadic scales

Let `h` be a whole-plane Gaussian free field with circle averages `h_s(z)`, `0 < γ < 2`, and let `μ` be the γ-LQG
measure of the field `h - α₀ log |·|`: the almost sure vague limit of the approximations
`ν_s = s^{γ²/2} e^{γ (h - α₀ log |·|)_s(z)} dz` along the dyadic scales `s = 2^{-k}`.

We show that almost surely the approximations converge vaguely to `μ` along the scales `r 2^{-k}` for every ratio
`r ∈ (1/2, 1]` simultaneously, provided their mass near the origin is small along these scales, almost surely for
every ratio simultaneously:
  for every `r ∈ (1/2, 1]` and `η > 0` there are `δ > 0` and `K` with `ν_{r 2^{-k}}(B(0, δ)) ≤ η` for all `k ≥ K`.
Away from the origin the singular approximations are the approximations of `h` weighted by the continuous function
`max(s, |z|)^{-γα₀}`, and those converge along every ratio to the γ-LQG measure of `h`; the bound near the origin
controls the rest. The limit is identified with `μ` through the sequence interleaving the scales `2^{-k}` and
`r 2^{-k}`, whose even subsequence is the dyadic one.

Consequently the coordinate change rule of the γ-LQG measure of `h - α₀ log |·|` under all complex affine maps
simultaneously (Duplantier-Sheffield 2011, Proposition 2.1; Sheffield-Wang 2016, Theorems 1.1 and 1.4) reduces to
this bound near the origin.

Main results:
* `IsWholePlaneGFF.ae_isLQGLimitAlong_ratio_fieldCircleAverage_of_origin`: vague convergence along every ratio from
  the bound near the origin.
* `LQG.coordChangeLP_of_ae_origin_ratio`: the coordinate change rule from the bound near the origin.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG LatticeProb.LQG.GMCRatioLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Vague convergence along every ratio for the field with a logarithmic singularity.** For a whole-plane GFF,
`0 < γ < 2` and the γ-LQG measure `μ` of `h - α₀ log |·|`: if almost surely, for every ratio `r ∈ (1/2, 1]`, the
approximations at the scales `r 2^{-k}` have uniformly small mass near the origin, then almost surely, for every ratio
`r ∈ (1/2, 1]` simultaneously, they converge vaguely to `μ`. -/
theorem ae_isLQGLimitAlong_ratio_fieldCircleAverage_of_origin (hh : IsWholePlaneGFF P hC hcirc) {γ α₀ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hO : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (r * dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      IsLQGLimitAlong γ (fieldCircleAverage α₀ (hcirc ω)) (fun k => r * dyadicScale k) (μ ω) := by
  obtain ⟨μ₀, hμ₀⟩ := hh.exists_isLQGMeasure hγ0 hγ2
  have hμ₀' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ₀ ω) := hμ₀
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  have h2' : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by omega⟩
  filter_upwards [hμ', hμ₀', hh.ae_isLQGLimitAlong_ratio_of_isLQGMeasure hγ0 hγ2 hμ₀, hO,
    hh.ae_continuousOn_circle] with ω h1 h0 hrat hOr hcont r hr
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hmul := hrat r (Ioc_subset_Icc_self hr)
  have hO1 := hOr 1 ⟨by norm_num, le_rfl⟩
  have hOc := hOr r hr
  have hct : ∀ n : ℕ, Continuous (hcirc ω (interleavedScale r n)) := fun n =>
    continuous_slice hcont (interleavedScale_pos hr0 n)
  refine ⟨h1.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩
  have hσ : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → ∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (interleavedScale r n))) atTop (𝓝 ℓ) := by
    intro g hg hgs
    refine ⟨∫ z, g z ∂(μ₀ ω), LQGSingularScaledLimit.tendsto_of_tendsto_even_odd ?_ ?_⟩
    · simpa only [interleavedScale_two_mul] using h0.tendsto_integral g hg hgs
    · simpa only [interleavedScale_two_mul_add_one] using hmul.tendsto_integral g hg hgs
  have hσ0 : Tendsto (interleavedScale r) atTop (𝓝 0) := by
    refine LQGSingularScaledLimit.tendsto_of_tendsto_even_odd ?_ ?_
    · simpa only [interleavedScale_two_mul] using LQGSingularScaledLimit.tendsto_dyadicScale_zero
    · simpa only [interleavedScale_two_mul_add_one, mul_zero] using
        LQGSingularScaledLimit.tendsto_dyadicScale_zero.const_mul r
  have hOσ : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ n ≥ K,
      lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (interleavedScale r n) (ball 0 δ) ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δ1, hδ1, K1, hK1⟩ := hO1 η hη
    obtain ⟨δ2, hδ2, K2, hK2⟩ := hOc η hη
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, 2 * (K1 + K2), fun n hn => ?_⟩
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [interleavedScale_two_mul]
      refine (measure_mono (ball_subset_ball (min_le_left _ _))).trans ?_
      simpa only [one_mul] using hK1 k (by omega)
    · rw [interleavedScale_two_mul_add_one]
      exact (measure_mono (ball_subset_ball (min_le_right _ _))).trans (hK2 k (by omega))
  obtain ⟨ℓ, hℓ⟩ := LQGSingularScaledLimit.exists_tendsto_integral_lqgApprox_fieldCircleAverage_seq
    (interleavedScale_pos hr0) hσ0 hσ hct hOσ hf hfc
  have heven := hℓ.comp h2
  have hodd := hℓ.comp h2'
  simp only [Function.comp_def, interleavedScale_two_mul, interleavedScale_two_mul_add_one] at heven hodd
  have hl : ℓ = ∫ z, f z ∂(μ ω) := tendsto_nhds_unique heven (h1.tendsto_integral f hf hfc)
  rw [← hl]
  exact hodd

end LatticeProb.Gauss.IsWholePlaneGFF

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **Reduction of the coordinate change rule to the mass near the origin.** The coordinate change rule
`LQGMeasureCoordChangeLP` of the γ-LQG measure of `h - α₀ log |·|` under all complex affine maps simultaneously
(Duplantier-Sheffield 2011, Proposition 2.1; Sheffield-Wang 2016, Theorems 1.1 and 1.4) holds as soon as almost
surely, for every ratio `r ∈ (1/2, 1]`, the approximations at the scales `r 2^{-k}` have uniformly small mass near the
origin. -/
theorem coordChangeLP_of_ae_origin_ratio {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (H : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
        lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (r * dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η) :
    LQGMeasureCoordChangeLP P γ α₀ hC hcirc :=
  coordChangeLP_of_ratio_limit P γ α₀ hC hcirc fun hG hγ0 hγ2 hα _ hμ =>
    hG.ae_isLQGLimitAlong_ratio_fieldCircleAverage_of_origin hγ0 hγ2 hμ (H hG hγ0 hγ2 hα)

end LatticeProb.LQG
