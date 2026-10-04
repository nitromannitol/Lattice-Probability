/-
The high-frequency tail of the Sobolev norm and the vanishing of the weight ratio.

`sobolevNormSqHigh_le` bounds the part of `‖φ‖_{H^{s₀}}²` carried by frequencies
`‖ξ‖ > Λ` by the weight ratio `(1 + (2πΛ)²)^{s₀ - s}` times the full `H^s` norm,
for `s₀ ≤ s`.  `tendsto_weight_atTop_zero` shows that this ratio tends to `0` as
`Λ → ∞` when `s₀ < s`.  Together they are the frequency-truncation step of the
Rellich–Kondrachov compactness argument: the high-frequency part of the unit ball
of `H^s(D)` is uniformly small in `H^{s₀}(D)`, so only the low-frequency part has
to be covered by a finite net.
-/
import LatticeProb.Analysis.Sobolev.Weight

open Filter MeasureTheory
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- The high-frequency part of the `H^{s₀}` norm is at most the weight ratio
`(1 + (2πΛ)²)^{s₀ - s}` times the full `H^s` norm, for `s₀ ≤ s` and `Λ ≥ 0`.  The
pointwise comparison is `weight_le`; the integral is split at `‖ξ‖ = Λ` and the
constant is pulled out of the Lebesgue integral. -/
theorem sobolevNormSqHigh_le {d : ℕ} {s₀ s Λ : ℝ} (h : s₀ ≤ s) (hΛ : 0 ≤ Λ)
    (φ : Space d → ℝ) :
    sobolevNormSqHigh d s₀ Λ φ
      ≤ ENNReal.ofReal ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)) * sobolevNormSq d s φ := by
  have hc : (0 : ℝ) ≤ (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) :=
    le_of_lt (Real.rpow_pos_of_pos (by nlinarith [sq_nonneg (2 * Real.pi * Λ)]) _)
  unfold sobolevNormSqHigh sobolevNormSq
  rw [← MeasureTheory.lintegral_indicator
    (measurableSet_lt measurable_const continuous_norm.measurable)]
  calc ∫⁻ ξ, {ξ : Space d | Λ < ‖ξ‖}.indicator
        (fun ξ => ENNReal.ofReal
          ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)) ξ
      ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)) *
          ENNReal.ofReal
            ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        apply MeasureTheory.lintegral_mono
        intro ξ
        simp only []
        by_cases hξ : Λ < ‖ξ‖
        · rw [Set.indicator_of_mem (show ξ ∈ {ξ : Space d | Λ < ‖ξ‖} from hξ)]
          rw [← ENNReal.ofReal_mul hc]
          apply ENNReal.ofReal_le_ofReal
          have hw := weight_le h hΛ (le_of_lt hξ)
          have hz : (0 : ℝ) ≤ ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := sq_nonneg _
          calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2
              ≤ ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)
                  * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s)
                  * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hw hz
            _ = (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)
                  * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
                    * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by ring
        · rw [Set.indicator_of_notMem (by simpa using hξ)]
          exact bot_le
    _ = ENNReal.ofReal ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)) *
          ∫⁻ ξ, ENNReal.ofReal
            ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]

/-- The weight ratio `(1 + (2πΛ)²)^{s₀ - s}` tends to `0` as `Λ → ∞` when
`s₀ < s`.  The base `1 + (2πΛ)²` tends to infinity, its `(s - s₀)`-th power too,
and the ratio is the reciprocal of that power. -/
theorem tendsto_weight_atTop_zero {s₀ s : ℝ} (h : s₀ < s) :
    Filter.Tendsto (fun Λ : ℝ => (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s))
      Filter.atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < s - s₀ := by linarith
  have h2 : Filter.Tendsto (fun Λ : ℝ => 2 * Real.pi * Λ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
  have h3 : Filter.Tendsto (fun Λ : ℝ => (2 * Real.pi * Λ) ^ 2) Filter.atTop Filter.atTop :=
    (by simpa [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp h2)
  have h1 : Filter.Tendsto (fun Λ : ℝ => 1 + (2 * Real.pi * Λ) ^ 2) Filter.atTop Filter.atTop :=
    (by simpa [add_comm] using tendsto_atTop_add_const_right _ 1 h3)
  have h4 : Filter.Tendsto (fun Λ : ℝ => (1 + (2 * Real.pi * Λ) ^ 2) ^ (s - s₀))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hpos |>.comp h1
  have h5 : Filter.Tendsto (fun Λ : ℝ => ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s - s₀))⁻¹)
      Filter.atTop (𝓝 0) :=
    h4.inv_tendsto_atTop
  refine h5.congr' ?_
  filter_upwards with Λ
  have hx : (0 : ℝ) ≤ 1 + (2 * Real.pi * Λ) ^ 2 := by nlinarith [sq_nonneg (2 * Real.pi * Λ)]
  rw [show s₀ - s = -(s - s₀) by ring, Real.rpow_neg hx]

end LatticeProb.Sobolev
