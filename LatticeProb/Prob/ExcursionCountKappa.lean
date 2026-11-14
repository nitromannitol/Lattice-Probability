import LatticeProb.Prob.ExcursionCountLaplaceMean
import LatticeProb.Prob.ExcursionCountVariance
import LatticeProb.Prob.BrownianFirstPassageLaplace
import LatticeProb.Prob.ForwardLadderSetNull
import LatticeProb.Analysis.ExcursionCountLaplace
import LatticeProb.Analysis.LadderSetOfStraddlingPairs

/-!
# The mean excursion count of Brownian motion: `E J_1(1) = √(2/π)`

Let `B` be a standard real Brownian motion with continuous paths. For `b, ε > 0` let `J_ε(b)` be the number of
excursions of `B` above its running infimum (the complementary intervals of the forward ladder set) of length larger
than `ε`, completed before the first passage time `τ_b` of `B` below `B 0 - b` (`pathExcursionCount`). We prove

  `E J_1(1) = √(2/π)`,

so that, by Brownian scaling (`lintegral_pathExcursionCount_eq_div_sqrt`), `E J_ε(b) = (b / √ε) √(2/π)`.

The proof compares the expectations of the deterministic Laplace-functional bounds of `Analysis.ExcursionCountLaplace`,
with `H_b = ∫_{x>0} e^{-x} J_x(b) dx` and `κ = E J_1(1)`:
* `1 - e^{-τ_b} ≤ H_b` almost surely (the forward ladder set is closed and Lebesgue-null), and
  `E[1 - e^{-τ_b}] = 1 - e^{-√2 b}` (Laplace transform of the first passage time);
* `H_b ≤ 1 - e^{-τ_b} + ∫_{(0,δ]} J_x(b) dx + J_δ(b) (J_δ(b) - 1)` pointwise, with `E[J (J - 1)] ≤ (E J)²` (variance
  bound for the excursion count);
* `E H_b = b √π κ`, `E ∫_{(0,δ]} J_x(b) dx = 2 b √δ κ` and `E J_δ(b) = b κ / √δ`.
Hence `√2 b - 2 b² ≤ b √π κ ≤ √2 b + 2 b √δ κ + b² κ² / δ`. Taking `b → 0` in the lower bound, and `δ = η²`,
`b = η³`, `η → 0` in the upper bound, gives `√π κ = √2`.

## Main results

* `sqrt_pi_mul_toReal_lintegral_pathExcursionCount`: `√π · E J_1(1) = √2`.
* `toReal_lintegral_pathExcursionCount_one_one`: `E J_1(1) = √(2/π)`.
* `lintegral_pathExcursionCount_eq_sqrt_two_div_pi`: `E J_ε(b) = (b / √ε) √(2/π)` for `b, ε > 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- The first passage time below `f 0 - b` of the extension of a path on `ℝ≥0` is nonnegative. -/
theorem firstPassageBelow_nnExtend_nonneg (f : ℝ≥0 → ℝ) (b : ℝ) : 0 ≤ firstPassageBelow (nnExtend f) 0 b :=
  Real.sInf_nonneg fun _ ht => ht.1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Laplace transform `ω ↦ e^{-τ_b}` of the first passage time below `B 0 - b` is integrable. -/
theorem integrable_exp_neg_firstPassageBelow [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    Integrable (fun ω => Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b)) P := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_firstPassageBelow hB hm hcont hb]
  exact (Real.exp_pos _).ne'

/-- `E[1 - e^{-τ_b}] = 1 - e^{-√2 b}`. -/
theorem lintegral_one_sub_exp_neg_firstPassageBelow [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b)) ∂P =
      ENNReal.ofReal (1 - Real.exp (-(√2 * b))) := by
  have hint := integrable_exp_neg_firstPassageBelow hB hm hcont hb
  have hle : ∀ ω, Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b) ≤ 1 := fun ω =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (firstPassageBelow_nnExtend_nonneg _ b))
  have h1 : Integrable (fun ω => 1 - Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b)) P :=
    (integrable_const 1).sub hint
  have h2 := ofReal_integral_eq_lintegral_ofReal h1 (Eventually.of_forall fun ω => sub_nonneg.2 (hle ω))
  rw [← h2, integral_sub (integrable_const 1) hint, integral_exp_neg_firstPassageBelow hB hm hcont hb]
  simp

/-- **Lower bound for the Laplace functional.** `1 - e^{-√2 b} ≤ E H_b = b √π κ`, `κ = E J_1(1)`. -/
theorem ofReal_one_sub_exp_neg_le_laplace [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) :
    ENNReal.ofReal (1 - Real.exp (-(√2 * b))) ≤
      ENNReal.ofReal (b * √Real.pi) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P := by
  rw [← lintegral_one_sub_exp_neg_firstPassageBelow hB hm hcont hb,
    ← lintegral_laplace_pathExcursionCount hB hm hcont hb]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_volume_forwardLadderSet_eq_zero hB hm hcont] with ω hω
  have h := ofReal_one_sub_exp_le_lintegral_excursionCount
    (isClosed_forwardLadderSet (v := 0) (continuous_nnExtend (hcont ω)))
    (firstPassageBelow_nnExtend_nonneg (fun t => B t ω) b) (measure_mono_null inter_subset_left hω)
  rw [sub_zero] at h
  exact h

/-- **Second factorial moment of the excursion count.** `E[J (J - 1)] ≤ (E J)²` for `J = J_ε(b)`. -/
theorem lintegral_pathExcursionCount_mul_pred_le_sq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 ≤ b) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ ω, ((pathExcursionCount (fun t => B t ω) b ε * (pathExcursionCount (fun t => B t ω) b ε - 1) : ℕ) :
        ℝ≥0∞) ∂P ≤
      (∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) ^ 2 := by
  have hpt : ∀ x : ℕ, (x : ℝ≥0∞) ^ 2 = x + ((x * (x - 1) : ℕ) : ℝ≥0∞) := by
    intro x
    rcases x with _ | k
    · simp
    · rw [Nat.add_sub_cancel]
      push_cast
      ring
  have hmeas : Measurable fun ω => (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) :=
    measurable_from_nat.comp (measurable_pathExcursionCount hm hcont b hε)
  have hsq := lintegral_pathExcursionCount_sq_le hB hm hcont hb hε
  simp_rw [hpt] at hsq
  rw [lintegral_add_left hmeas] at hsq
  exact (ENNReal.add_le_add_iff_left (lintegral_pathExcursionCount_lt_top hB hm hcont hb hε).ne).1 hsq

/-- **Upper bound for the Laplace functional.** For `b, δ > 0`, with `κ = E J_1(1)`:
`b √π κ ≤ (1 - e^{-√2 b}) + 2 b √δ κ + (b κ / √δ)²`. -/
theorem laplace_le_of_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {b : ℝ} (hb : 0 < b) {δ : ℝ}
    (hδ : 0 < δ) :
    ENNReal.ofReal (b * √Real.pi) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (1 - Real.exp (-(√2 * b))) +
        ENNReal.ofReal (2 * b * √δ) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P +
        (ENNReal.ofReal (b / √δ) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P) ^ 2 := by
  rw [← lintegral_laplace_pathExcursionCount hB hm hcont hb,
    ← lintegral_one_sub_exp_neg_firstPassageBelow hB hm hcont hb,
    ← lintegral_Ioc_pathExcursionCount hB hm hcont hb hδ.le,
    ← lintegral_pathExcursionCount_eq_div_sqrt hB hm hcont hδ hb]
  have hpt : ∀ ω, (∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-x)) *
      (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 - Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b)) +
        (∫⁻ x in Ioc 0 δ, (pathExcursionCount (fun t => B t ω) b x : ℝ≥0∞)) +
        ((pathExcursionCount (fun t => B t ω) b δ * (pathExcursionCount (fun t => B t ω) b δ - 1) : ℕ) :
          ℝ≥0∞) := by
    intro ω
    have h := lintegral_excursionCount_le (K := forwardLadderSet (nnExtend fun t => B t ω) 0)
      (firstPassageBelow_nnExtend_nonneg (fun t => B t ω) b) hδ
    rw [sub_zero] at h
    exact h
  have hA : AEMeasurable
      (fun ω => ENNReal.ofReal (1 - Real.exp (-firstPassageBelow (nnExtend fun t => B t ω) 0 b))) P :=
    ((integrable_exp_neg_firstPassageBelow hB hm hcont hb).aemeasurable.const_sub 1).ennreal_ofReal
  have hD : Measurable fun ω =>
      ((pathExcursionCount (fun t => B t ω) b δ * (pathExcursionCount (fun t => B t ω) b δ - 1) : ℕ) : ℝ≥0∞) :=
    (measurable_from_nat (f := fun n : ℕ => ((n * (n - 1) : ℕ) : ℝ≥0∞))).comp
      (measurable_pathExcursionCount hm hcont b hδ)
  refine (lintegral_mono fun ω => hpt ω).trans ?_
  rw [lintegral_add_right' _ hD.aemeasurable, lintegral_add_left' hA]
  gcongr
  exact lintegral_pathExcursionCount_mul_pred_le_sq hB hm hcont hb.le hδ

/-- **The mean excursion count.** `√π · E J_1(1) = √2`. -/
theorem sqrt_pi_mul_toReal_lintegral_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    √Real.pi * (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal = √2 := by
  have hκ_top : ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P ≠ ⊤ :=
    (lintegral_pathExcursionCount_lt_top hB hm hcont zero_le_one one_pos).ne
  have hκK : ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P =
      ENNReal.ofReal (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal :=
    (ENNReal.ofReal_toReal hκ_top).symm
  have hK0 : 0 ≤ (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal := ENNReal.toReal_nonneg
  generalize (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal = K at hκK hK0 ⊢
  have hA : ∀ b : ℝ, 0 < b → 0 ≤ 1 - Real.exp (-(√2 * b)) := fun b hb =>
    sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity)))
  -- the lower bound `1 - e^{-√2 b} ≤ b √π K`
  have hlow : ∀ b : ℝ, 0 < b → 1 - Real.exp (-(√2 * b)) ≤ b * √Real.pi * K := by
    intro b hb
    have h := ofReal_one_sub_exp_neg_le_laplace hB hm hcont hb
    rw [hκK, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ b * √Real.pi)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hK0)).1 h
  -- the upper bound `b √π K ≤ (1 - e^{-√2 b}) + 2 b √δ K + (b K / √δ)²`
  have hup : ∀ b δ : ℝ, 0 < b → 0 < δ →
      b * √Real.pi * K ≤ (1 - Real.exp (-(√2 * b))) + 2 * b * √δ * K + (b / √δ * K) ^ 2 := by
    intro b δ hb hδ
    have h := laplace_le_of_pathExcursionCount hB hm hcont hb hδ
    have h5 : 0 ≤ 2 * b * √δ * K := mul_nonneg (by positivity) hK0
    have h6 : 0 ≤ (b / √δ * K) ^ 2 := sq_nonneg _
    rw [hκK, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ b * √Real.pi),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * b * √δ),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ b / √δ),
      ← ENNReal.ofReal_pow (mul_nonneg (by positivity) hK0), ← ENNReal.ofReal_add (hA b hb) h5,
      ← ENNReal.ofReal_add (add_nonneg (hA b hb) h5) h6] at h
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg (hA b hb) h5) h6)).1 h
  -- `√π K ≤ √2 + η (2 K + K²)` for every `η > 0` (take `δ = η²`, `b = η³`)
  have hupη : ∀ η : ℝ, 0 < η → √Real.pi * K ≤ √2 + η * (2 * K + K ^ 2) := by
    intro η hη
    have h := hup (η ^ 3) (η ^ 2) (by positivity) (by positivity)
    rw [Real.sqrt_sq hη.le] at h
    have hexp : 1 - Real.exp (-(√2 * η ^ 3)) ≤ √2 * η ^ 3 := by
      have := Real.add_one_le_exp (-(√2 * η ^ 3))
      linarith
    have e2 : (η ^ 3 / η * K) ^ 2 = η ^ 3 * (η * K ^ 2) := by
      field_simp
    rw [e2] at h
    have h3 : η ^ 3 * (√Real.pi * K) ≤ η ^ 3 * (√2 + η * (2 * K + K ^ 2)) := by
      linear_combination h + hexp
    exact le_of_mul_le_mul_left h3 (by positivity)
  -- `√2 ≤ √π K + 2 b` for every `b ∈ (0, 1/2]`
  have hlowb : ∀ b : ℝ, 0 < b → b ≤ 1 / 2 → √2 ≤ √Real.pi * K + 2 * b := by
    intro b hb hb2
    have h := hlow b hb
    have h2 : √2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hy : |-(√2 * b)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      nlinarith
    have h4 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hy)).2
    have hsq : (-(√2 * b)) ^ 2 = 2 * b ^ 2 := by
      rw [neg_sq, mul_pow, Real.sq_sqrt zero_le_two]
    rw [hsq] at h4
    have h5 : b * √2 ≤ b * (√Real.pi * K + 2 * b) := by
      linear_combination h4 + h
    exact le_of_mul_le_mul_left h5 hb
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hC : 0 ≤ 2 * K + K ^ 2 := add_nonneg (mul_nonneg zero_le_two hK0) (sq_nonneg K)
    have h := hupη (ε / (2 * K + K ^ 2 + 1)) (div_pos hε (by linarith))
    have hle : ε / (2 * K + K ^ 2 + 1) * (2 * K + K ^ 2) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := hlowb (min (ε / 2) (1 / 2)) (lt_min (by positivity) (by norm_num)) (min_le_right _ _)
    have := min_le_left (ε / 2) (1 / 2)
    linarith

/-- **The mean excursion count.** `E J_1(1) = √(2/π)`. -/
theorem toReal_lintegral_pathExcursionCount_one_one [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    (∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 1 : ℝ≥0∞) ∂P).toReal = √(2 / Real.pi) := by
  have h := sqrt_pi_mul_toReal_lintegral_pathExcursionCount hB hm hcont
  have hπ : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [Real.sqrt_div' 2 Real.pi_pos.le, eq_div_iff hπ.ne', mul_comm]
  exact h

/-- **The mean excursion count, scaled.** For `b, ε > 0`: `E J_ε(b) = (b / √ε) √(2/π)`. -/
theorem lintegral_pathExcursionCount_eq_sqrt_two_div_pi [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) {b : ℝ}
    (hb : 0 < b) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P = ENNReal.ofReal (b / √ε * √(2 / Real.pi)) := by
  rw [lintegral_pathExcursionCount_eq_div_sqrt hB hm hcont hε hb,
    ← ENNReal.ofReal_toReal (lintegral_pathExcursionCount_lt_top hB hm hcont zero_le_one one_pos).ne,
    toReal_lintegral_pathExcursionCount_one_one hB hm hcont, ← ENNReal.ofReal_mul (by positivity)]

end LatticeProb.LadderSet
