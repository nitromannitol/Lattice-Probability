import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The Paley-Zygmund inequality in `L^p`

For a nonnegative random variable `X` on a probability space, a level `t ∈ [0, ∞]` and Hölder
conjugate exponents `p, q`, split `E X` over the event `{t < X}` and its complement. On the
complement `X ≤ t`; on the event, Hölder's inequality bounds `E[X 1_{t < X}]` by
`(E X^p)^{1/p} P(t < X)^{1/q}`. Hence
  `E X ≤ t + (E X^p)^{1/p} P(t < X)^{1/q}`,
and, solving for the probability,
  `P(t < X) ≥ ((E X - t) / (E X^p)^{1/p})^q`.

This is the `L^p` form of the second moment method: with `p = 2` it is the classical
Paley-Zygmund inequality (see `LatticeProb/Prob/PaleyZygmund.lean` for the Bochner-integral
version), while exponents `p` close to `1` give lower bounds `P(t < X) ≳ (E X / ‖X‖_p)^q` with
large `q`, the form used to turn a lower bound for an expected exit time and an upper bound for
its higher moments into a lower bound for the probability that the exit time is large.

Everything is stated with lower Lebesgue integrals in `ℝ≥0∞`, so there are no integrability
side conditions.

## Main results

* `LatticeProb.lintegral_le_add_mul_measure_lt_rpow`: `E X ≤ t + (E X^p)^{1/p} P(t < X)^{1/q}`.
* `LatticeProb.lintegral_tsub_le_mul_measure_lt_rpow`: `E X - t ≤ (E X^p)^{1/p} P(t < X)^{1/q}`.
* `LatticeProb.rpow_div_le_measure_lt`: `((E X - t) / (E X^p)^{1/p})^q ≤ P(t < X)`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Paley-Zygmund inequality in `L^p`, additive form.** For a measurable `X : α → ℝ≥0∞` on a
probability space, a level `t` and Hölder conjugate exponents `p, q`:
`E X ≤ t + (E X^p)^{1/p} P(t < X)^{1/q}`. -/
theorem lintegral_le_add_mul_measure_lt_rpow [IsProbabilityMeasure μ] {X : α → ℝ≥0∞}
    (hX : Measurable X) {p q : ℝ} (hpq : p.HolderConjugate q) (t : ℝ≥0∞) :
    ∫⁻ a, X a ∂μ ≤ t + (∫⁻ a, X a ^ p ∂μ) ^ (1 / p) * μ {a | t < X a} ^ (1 / q) := by
  set A : Set α := {a | t < X a} with hAdef
  have hA : MeasurableSet A := measurableSet_lt measurable_const hX
  rw [← lintegral_add_compl X hA, add_comm]
  refine add_le_add ?_ ?_
  · calc ∫⁻ a in Aᶜ, X a ∂μ ≤ ∫⁻ _ in Aᶜ, t ∂μ :=
          setLIntegral_mono' hA.compl fun a ha => not_lt.1 ha
      _ = t * μ Aᶜ := setLIntegral_const _ _
      _ ≤ t * 1 := mul_le_mul' le_rfl prob_le_one
      _ = t := mul_one t
  · have hind : X * A.indicator (1 : α → ℝ≥0∞) = A.indicator X := by
      funext a
      by_cases ha : a ∈ A <;> simp [ha]
    have hg : ∫⁻ a, A.indicator (1 : α → ℝ≥0∞) a ^ q ∂μ = μ A := by
      have hq : 0 < q := hpq.symm.pos
      have hpow : (fun a => A.indicator (1 : α → ℝ≥0∞) a ^ q) = A.indicator 1 := by
        funext a
        by_cases ha : a ∈ A <;> simp [ha, ENNReal.zero_rpow_of_pos hq]
      rw [hpow, lintegral_indicator_one hA]
    calc ∫⁻ a in A, X a ∂μ = ∫⁻ a, (X * A.indicator (1 : α → ℝ≥0∞)) a ∂μ := by
          rw [hind, lintegral_indicator hA]
      _ ≤ (∫⁻ a, X a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, A.indicator (1 : α → ℝ≥0∞) a ^ q ∂μ) ^ (1 / q) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hX.aemeasurable
            ((measurable_one.indicator hA).aemeasurable)
      _ = (∫⁻ a, X a ^ p ∂μ) ^ (1 / p) * μ A ^ (1 / q) := by rw [hg]

/-- **Paley-Zygmund inequality in `L^p`, truncated form.**
`E X - t ≤ (E X^p)^{1/p} P(t < X)^{1/q}` (truncated subtraction in `ℝ≥0∞`). -/
theorem lintegral_tsub_le_mul_measure_lt_rpow [IsProbabilityMeasure μ] {X : α → ℝ≥0∞}
    (hX : Measurable X) {p q : ℝ} (hpq : p.HolderConjugate q) (t : ℝ≥0∞) :
    ∫⁻ a, X a ∂μ - t ≤ (∫⁻ a, X a ^ p ∂μ) ^ (1 / p) * μ {a | t < X a} ^ (1 / q) :=
  tsub_le_iff_left.2 (lintegral_le_add_mul_measure_lt_rpow hX hpq t)

/-- **Paley-Zygmund inequality in `L^p`.** For a measurable `X : α → ℝ≥0∞` on a probability
space, a level `t` and Hölder conjugate exponents `p, q`:
`((E X - t) / (E X^p)^{1/p})^q ≤ P(t < X)`. -/
theorem rpow_div_le_measure_lt [IsProbabilityMeasure μ] {X : α → ℝ≥0∞}
    (hX : Measurable X) {p q : ℝ} (hpq : p.HolderConjugate q) (t : ℝ≥0∞) :
    ((∫⁻ a, X a ∂μ - t) / (∫⁻ a, X a ^ p ∂μ) ^ (1 / p)) ^ q ≤ μ {a | t < X a} := by
  have hq : 0 < q := hpq.symm.pos
  have h1 : (∫⁻ a, X a ∂μ - t) / (∫⁻ a, X a ^ p ∂μ) ^ (1 / p) ≤ μ {a | t < X a} ^ (1 / q) :=
    ENNReal.div_le_of_le_mul (by
      rw [mul_comm]; exact lintegral_tsub_le_mul_measure_lt_rpow hX hpq t)
  calc ((∫⁻ a, X a ∂μ - t) / (∫⁻ a, X a ^ p ∂μ) ^ (1 / p)) ^ q
      ≤ (μ {a | t < X a} ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow h1 hq.le
    _ = μ {a | t < X a} := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

end LatticeProb
