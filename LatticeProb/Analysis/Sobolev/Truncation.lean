/-
The frequency splitting of the Sobolev norm and the uniform smallness of the
high-frequency part of the unit ball.

`sobolevNormSqLow` is the part of `‖φ‖_{H^s}²` carried by frequencies `‖ξ‖ ≤ Λ`,
the complement of the set defining `sobolevNormSqHigh`; the two add up to the
full norm.  `exists_sobolevNormSqHigh_le` is the frequency-truncation step of the
Rellich–Kondrachov argument: for `s₀ < s` and any `η > 0` there is a cutoff `Λ`
beyond which the high-frequency part of the `H^{s₀}` norm is at most `η²` on the
whole unit ball of `H^s`.  Only the low-frequency part of the unit ball then has
to be covered by a finite net.
-/
import LatticeProb.Analysis.Sobolev.HighFrequency

open Filter MeasureTheory
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- The low-frequency part of `‖φ‖_{H^s}²`: the integral defining the norm
restricted to frequencies `‖ξ‖ ≤ Λ`, the complement of the set defining
`sobolevNormSqHigh`. -/
noncomputable def sobolevNormSqLow (d : ℕ) (s : ℝ) (Λ : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖}ᶜ, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)

/-- The low-frequency and high-frequency parts of the `H^s` norm add up to the
full norm.  This is the additivity of the Lebesgue integral over a measurable set
and its complement, for the measurable set `{ξ | Λ < ‖ξ‖}`. -/
theorem sobolevNormSqLow_add_high (d : ℕ) (s Λ : ℝ) (φ : Space d → ℝ) :
    sobolevNormSqLow d s Λ φ + sobolevNormSqHigh d s Λ φ = sobolevNormSq d s φ := by
  unfold sobolevNormSqLow sobolevNormSqHigh sobolevNormSq
  rw [add_comm]
  exact MeasureTheory.lintegral_add_compl _
    (measurableSet_lt (measurable_const : Measurable (fun _ : Space d => Λ))
      (continuous_norm.measurable : Measurable (fun ξ : Space d => ‖ξ‖)))

/-- **Frequency truncation.**  For `s₀ < s` and `η > 0` there is a cutoff `Λ ≥ 0`
such that the high-frequency part of the `H^{s₀}` norm is at most `η²` for every
test function whose `H^s` norm is at most `1`.  The weight ratio
`(1 + (2πΛ)²)^{s₀ - s}` tends to `0` by `tendsto_weight_atTop_zero`, and
`sobolevNormSqHigh_le` bounds the tail by that ratio times the full `H^s` norm. -/
theorem exists_sobolevNormSqHigh_le_truncation {d : ℕ} {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ φ : Space d → ℝ, sobolevNormSq d s φ ≤ 1 →
      sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (η ^ 2) := by
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, ∀ Λ : ℝ, Λ₀ ≤ Λ →
      (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) ≤ η ^ 2 := by
    have hev : ∀ᶠ Λ : ℝ in Filter.atTop,
        (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) < η ^ 2 :=
      (tendsto_weight_atTop_zero h).eventually (Iio_mem_nhds hη2)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨a, ha⟩ := hev
    exact ⟨a, fun Λ hΛ => le_of_lt (ha Λ hΛ)⟩
  refine ⟨max Λ₀ 0, le_max_right _ _, fun φ hφ => ?_⟩
  have hΛ : (0 : ℝ) ≤ max Λ₀ 0 := le_max_right _ _
  have hratio : (1 + (2 * Real.pi * max Λ₀ 0) ^ 2) ^ (s₀ - s) ≤ η ^ 2 :=
    hΛ₀ _ (le_max_left _ _)
  calc sobolevNormSqHigh d s₀ (max Λ₀ 0) φ
      ≤ ENNReal.ofReal ((1 + (2 * Real.pi * max Λ₀ 0) ^ 2) ^ (s₀ - s)) *
          sobolevNormSq d s φ := sobolevNormSqHigh_le (le_of_lt h) hΛ φ
    _ ≤ ENNReal.ofReal (η ^ 2) * 1 := by
        exact mul_le_mul (ENNReal.ofReal_le_ofReal hratio) hφ
          (bot_le : (0 : ℝ≥0∞) ≤ sobolevNormSq d s φ)
          (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (η ^ 2))
    _ = ENNReal.ofReal (η ^ 2) := mul_one _

end LatticeProb.Sobolev
