/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib

/-!
# Nested conditioning

Let `μ` be a finite measure and `A ⊆ A'` measurable sets with `μ A ≠ 0`.  For a measurable
function `Φ` with values in `[0, 1]` the conditional averages `(∫_A Φ) / μ A` and
`(∫_{A'} Φ) / μ A'` differ by at most `(μ A' - μ A) / μ A'`, the total variation distance between
`μ(· | A)` and `μ(· | A')`.

## Main results

* `LatticeProb.abs_setAverage_sub_setAverage_le`: the estimate for set integrals.
* `LatticeProb.abs_integral_cond_sub_integral_cond_le`: the same estimate for the conditional
  measures `μ[|A]` and `μ[|A']`.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {α : Type*} [MeasurableSpace α]

/-- Nested conditioning: for `A ⊆ A'` and `0 ≤ Φ ≤ 1`,
`|(∫_A Φ)/μ A - (∫_{A'} Φ)/μ A'| ≤ (μ A' - μ A)/μ A'`. -/
theorem abs_setAverage_sub_setAverage_le (μ : Measure α) [IsFiniteMeasure μ] {A A' : Set α}
    (hA : MeasurableSet A) (hA' : MeasurableSet A') (hAA' : A ⊆ A') (hpos : μ A ≠ 0)
    {Φ : α → ℝ} (hΦ : Measurable Φ) (h0 : ∀ x, 0 ≤ Φ x) (h1 : ∀ x, Φ x ≤ 1) :
    |(∫ x in A, Φ x ∂μ) / μ.real A - (∫ x in A', Φ x ∂μ) / μ.real A'| ≤
      (μ.real A' - μ.real A) / μ.real A' := by
  have hint : Integrable Φ μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hΦ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
  set m := μ.real A with hm
  set m' := μ.real A' with hm'
  set a := ∫ x in A, Φ x ∂μ with ha
  set a' := ∫ x in A', Φ x ∂μ with ha'
  have hmpos : 0 < m := ENNReal.toReal_pos hpos (measure_ne_top μ A)
  have hmm' : m ≤ m' := measureReal_mono hAA'
  have hm'pos : 0 < m' := lt_of_lt_of_le hmpos hmm'
  have ha0 : 0 ≤ a := setIntegral_nonneg hA fun x _ => h0 x
  have haM : a ≤ m := by
    have : ∫ x in A, Φ x ∂μ ≤ ∫ _ in A, (1 : ℝ) ∂μ :=
      setIntegral_mono_on hint.integrableOn (integrable_const _).integrableOn hA fun x _ => h1 x
    simpa [hm] using this
  have hdiff : a' - a = ∫ x in A' \ A, Φ x ∂μ := by
    rw [setIntegral_sdiff hA hint.integrableOn hAA']
  have hb0 : 0 ≤ a' - a := by
    rw [hdiff]; exact setIntegral_nonneg (hA'.diff hA) fun x _ => h0 x
  have hbM : a' - a ≤ m' - m := by
    have h2 : ∫ x in A' \ A, Φ x ∂μ ≤ ∫ _ in A' \ A, (1 : ℝ) ∂μ :=
      setIntegral_mono_on hint.integrableOn (integrable_const _).integrableOn (hA'.diff hA)
        fun x _ => h1 x
    have h3 : μ.real (A' \ A) = m' - m := measureReal_sdiff hAA' hA
    rw [hdiff]
    simpa [h3] using h2
  have key : |a * m' - a' * m| ≤ m * (m' - m) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ha0 (sub_nonneg.2 hmm'), mul_nonneg hb0 hmpos.le,
      mul_le_mul_of_nonneg_left hbM hmpos.le, mul_le_mul_of_nonneg_right haM (sub_nonneg.2 hmm')]
  have heq : a / m - a' / m' = (a * m' - a' * m) / (m * m') := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hmpos hm'pos), div_le_div_iff₀ (mul_pos hmpos hm'pos) hm'pos]
  calc |a * m' - a' * m| * m' ≤ m * (m' - m) * m' := mul_le_mul_of_nonneg_right key hm'pos.le
    _ = (m' - m) * (m * m') / m' * m' := by field_simp
    _ ≤ (m' - m) * (m * m') := by
      rw [div_mul_cancel₀ _ hm'pos.ne']

/-- The same estimate for the conditional measures `μ[|A]` and `μ[|A']`. -/
theorem abs_integral_cond_sub_integral_cond_le (μ : Measure α) [IsFiniteMeasure μ] {A A' : Set α}
    (hA : MeasurableSet A) (hA' : MeasurableSet A') (hAA' : A ⊆ A') (hpos : μ A ≠ 0)
    {Φ : α → ℝ} (hΦ : Measurable Φ) (h0 : ∀ x, 0 ≤ Φ x) (h1 : ∀ x, Φ x ≤ 1) :
    |(∫ x, Φ x ∂μ[|A]) - ∫ x, Φ x ∂μ[|A']| ≤ (μ.real A' - μ.real A) / μ.real A' := by
  have hpos' : μ A' ≠ 0 := fun h => hpos (measure_mono_null hAA' h)
  have e : ∀ B : Set α, μ B ≠ 0 → ∫ x, Φ x ∂μ[|B] = (∫ x in B, Φ x ∂μ) / μ.real B := by
    intro B hB
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    simp [Measure.real, div_eq_inv_mul]
  rw [e A hpos, e A' hpos']
  exact abs_setAverage_sub_setAverage_le μ hA hA' hAA' hpos hΦ h0 h1

end LatticeProb
