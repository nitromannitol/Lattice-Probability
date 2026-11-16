import LatticeProb.Prob.BernsteinBoundedMoment
import LatticeProb.Prob.BernsteinFirstCrossing

/-!
# Bounded martingale moments

A moment estimate for bounded martingale differences.
-/


open MeasureTheory
namespace LatticeProb

/-- The good-λ tail estimate for bounded martingale differences. -/
theorem boundedDifference_goodLambda_tail {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (F : Filtration ℕ m)
    (ξ : ℕ → Ω → ℝ) (k : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 2 ≤ p)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) :
    ∀ t : ℝ, 8 * p * a < t →
      μ.real {ω | 2 * t < crossTermMax ξ k ω} ≤
        μ.real {ω | (1 / (8 * Real.sqrt p)) * t <
          Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)} +
        (2 * Real.exp (-2 * p)) * μ.real {ω | t < crossTermMax ξ k ω} := by
  intro t ht
  have ht' : 8 * p * a ≤ t := le_of_lt ht
  have hta : a < t := by nlinarith
  have hd : 0 < 1 / (8 * Real.sqrt p) := by positivity
  have hfirst := bernstein_firstCrossing_goodLambda_internal μ F ξ k a t
    (1 / (8 * Real.sqrt p)) ha hta hd hξ hint hmean hbound (by
      intro j hj B hB s v hs hv
      have h := measureReal_max_abs_partialSum_le (P := μ) hj hξ hint hmean ha hbound hs hv hB
      convert h using 1
      · congr 1
        ext ω
        simp [crossTermPartialSum, bernsteinClippedVariance, clippedDifferenceVariance, and_assoc]
        aesop
      · congr 2
        rw [neg_div])
  have hfirst' : μ.real ({ω | 2 * t < crossTermMax ξ k ω} ∩
      {ω | Real.sqrt (clippedDifferenceVariance μ F ξ a k ω) ≤ (1 / (8 * Real.sqrt p)) * t}) ≤
      (2 * Real.exp (-((t - a) ^ 2) /
        (2 * ((1 / (8 * Real.sqrt p)) ^ 2 * t ^ 2 + a * (t - a) / 3)))) *
          μ.real {ω | t < crossTermMax ξ k ω} := by
    simpa only [bernsteinClippedVariance, clippedDifferenceVariance] using hfirst
  have hexp : 2 * Real.exp (-((t - a) ^ 2) /
      (2 * ((1 / (8 * Real.sqrt p)) ^ 2 * t ^ 2 + a * (t - a) / 3))) ≤
      2 * Real.exp (-2 * p) := by
    gcongr
    exact bernstein_goodLambda_exponent_le hp ha ht'
  have hbound' := le_trans hfirst' (mul_le_mul_of_nonneg_right hexp measureReal_nonneg)
  have hsub : {ω | 2 * t < crossTermMax ξ k ω} ⊆
      {ω | (1 / (8 * Real.sqrt p)) * t < Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)} ∪
        ({ω | 2 * t < crossTermMax ξ k ω} ∩
          {ω | Real.sqrt (clippedDifferenceVariance μ F ξ a k ω) ≤ (1 / (8 * Real.sqrt p)) * t}) := by
    intro ω hω
    by_cases h : (1 / (8 * Real.sqrt p)) * t < Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)
    · exact Or.inl h
    · exact Or.inr ⟨hω, le_of_not_gt h⟩
  have hm := measureReal_mono hsub (measure_ne_top μ _)
  have hu := measureReal_union_le (μ := μ)
    {ω | (1 / (8 * Real.sqrt p)) * t < Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)}
    ({ω | 2 * t < crossTermMax ξ k ω} ∩
      {ω | Real.sqrt (clippedDifferenceVariance μ F ξ a k ω) ≤ (1 / (8 * Real.sqrt p)) * t})
  linarith

end LatticeProb

namespace LatticeProb

/-- The bounded-difference martingale moment estimate with constant 32. -/
theorem boundedDifference_moment32 {Ω : Type*} {m : MeasurableSpace Ω}
    (μ : @Measure Ω m) [IsProbabilityMeasure μ] (F : Filtration ℕ m)
    (ξ : ℕ → Ω → ℝ) (k : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 2 ≤ p)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) :
    (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ p ∂μ) ^ (1 / p) ≤
      32 * (Real.sqrt p *
        (∫ ω, (∑ i ∈ Finset.Icc 1 k, μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)] ω) ^ (p / 2) ∂μ) ^ (1 / p) +
          p * a) := by
  let X := crossTermMax ξ k
  let Y := fun ω => Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)
  let KX : ℝ := (k + 1 : ℕ) * a
  let KY : ℝ := Real.sqrt (((Finset.Icc 1 k).card : ℝ) * a ^ 2)
  have hp0 : 0 < p := by linarith
  have hX : Measurable X := measurable_crossTermMax F ξ hξ k
  have hY : Measurable Y := Real.continuous_sqrt.measurable.comp
    (measurable_clippedDifferenceVariance μ F ξ a k)
  have hX0 : ∀ ω, 0 ≤ X ω := crossTermMax_nonneg ξ k
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => Real.sqrt_nonneg _
  have hXbound : ∀ ω, X ω ≤ KX := crossTermMax_le_of_bounded ξ k (le_of_lt ha) hbound
  have hYbound : ∀ ω, Y ω ≤ KY := by
    intro ω
    exact Real.sqrt_le_sqrt (clippedDifferenceVariance_bounds μ F ξ a k ω).2
  have htail := boundedDifference_goodLambda_tail μ F ξ k ha hp hξ hint hmean hbound
  have hmax := goodLambda_moment_bound μ X Y hp ha hX hY hX0 hY0 hXbound hYbound htail
  have hpart : Measurable (fun ω => |crossTermPartialSum ξ k ω|) := by
    apply Measurable.abs
    unfold crossTermPartialSum
    exact Finset.measurable_sum _ (fun i _ => (hξ i).mono (F.le i) le_rfl)
  have hle : ∀ ω, |crossTermPartialSum ξ k ω| ≤ X ω := by
    intro ω
    exact Finset.le_sup' (s := Finset.range (k + 1))
      (f := fun j => |crossTermPartialSum ξ j ω|) (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hpartbound : ∀ ω, |crossTermPartialSum ξ k ω| ≤ KX :=
    fun ω => le_trans (hle ω) (hXbound ω)
  have hpartint := integrable_rpow_of_bounded_nonneg μ (fun ω => |crossTermPartialSum ξ k ω|)
    (le_of_lt hp0) hpart (fun ω => abs_nonneg _) hpartbound
  have hXint := integrable_rpow_of_bounded_nonneg μ X (le_of_lt hp0) hX hX0 hXbound
  have hpartial : (∫ ω, |crossTermPartialSum ξ k ω| ^ p ∂μ) ≤ ∫ ω, X ω ^ p ∂μ := by
    apply integral_mono hpartint hXint
    intro ω
    exact Real.rpow_le_rpow (abs_nonneg _) (hle ω) (le_of_lt hp0)
  have hnonneg : 0 ≤ ∫ ω, |crossTermPartialSum ξ k ω| ^ p ∂μ :=
    integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) p)
  have hroot := Real.rpow_le_rpow hnonneg hpartial (show 0 ≤ 1 / p by positivity)
  have hv := clippedDifferenceVariance_sqrt_moment_eq μ F ξ k hξ hbound (p := p)
  change (∫ ω, X ω ^ p ∂μ) ^ (1 / p) ≤
    32 * (Real.sqrt p * (∫ ω, (Real.sqrt (clippedDifferenceVariance μ F ξ a k ω)) ^ p ∂μ) ^ (1 / p) + p * a) at hmax
  rw [hv] at hmax
  exact le_trans hroot hmax

end LatticeProb

namespace LatticeProb

/-- Source-shaped bounded-difference moment estimate with constant 32. -/
theorem boundedDifference_moment32_source
    (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m) [IsProbabilityMeasure μ]
    (k : ℕ) (F : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ) (r a : ℝ)
    (hF : Monotone F) (hFm : ∀ i, F i ≤ m)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hr : 2 ≤ r) (ha : 0 < a) (hbound : ∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) :
    (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
      32 * (Real.sqrt r *
        (∫ ω, (∑ i ∈ Finset.Icc 1 k, μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)] ω) ^ (r / 2) ∂μ) ^ (1 / r) + r * a) := by
  let ℱ : Filtration ℕ m := ⟨F, hF, hFm⟩
  exact LatticeProb.boundedDifference_moment32 μ ℱ ξ k ha hr hξ hint hmean hbound

end LatticeProb
