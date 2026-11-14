import LatticeProb.Prob.CorrelatedBMConeGridSurvival

/-! # Uniform separated-grid bounds from joint window survival -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A lower bound on the gap bounds the Gaussian middle-window factor. -/
theorem cone_gaussian_factor_le_of_separation (q a b h d : ℝ)
    (hq : 0 ≤ q) (hd : 2 * h < d) (hsep : d < b - a) :
    ENNReal.ofReal (2 * q / √(2 * Real.pi * (b - h - (a + h)))) ≤
      ENNReal.ofReal (2 * q / √(2 * Real.pi * (d - 2 * h))) := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_left (by positivity) ?_ ?_
  · apply Real.sqrt_pos.2
    exact mul_pos (by positivity) (by linarith)
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi)
    linarith

/-- The forward grid event has a uniform bound from a joint backward-window estimate. -/
theorem measure_factorialConeGridEvent_one_le_uniform {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (C α : ℝ) (k n : ℕ) (h d : ℝ)
    (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ)) (hd : 2 * h < d)
    (hq : 0 ≤ C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
    (J : ℝ≥0∞)
    (hJ : ∀ b : ℝ,
      μ ({ω | ∀ t ∈ Icc (b - h) b,
        -(C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) ≤
          coneIncr 0 t (b - h) ω - coneIncr 0 b (b - h) ω} ∩
        {ω | ∀ t ∈ Icc (b - h) b,
        -(C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) ≤
          coneIncr 1 t (b - h) ω - coneIncr 1 b (b - h) ω}) ≤ J)
    (i j : Fin (n.factorial ^ 6))
    (hsep : d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
      (i.val : ℝ) / (n.factorial ^ 6 : ℕ)) :
    μ (factorialConeGridEvent 1 C α k n i j) ≤
      (ENNReal.ofReal (3 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) / √h) * J +
       ENNReal.ofReal (3 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) / √h) * J) *
       ENNReal.ofReal (2 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) /
         √(2 * Real.pi * (d - 2 * h))) := by
  have hg : (i.val : ℝ) / (n.factorial ^ 6 : ℕ) + h <
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ) - h := by linarith
  refine (measure_factorialConeGridEvent_one_le_survival hμ C α k n i j h hh hH hg hq).trans ?_
  apply mul_le_mul'
  · apply add_le_add
    · exact mul_le_mul' le_rfl (hJ _)
    · exact mul_le_mul' le_rfl (by simpa only [inter_comm] using (hJ
        ((j.val : ℝ) / (n.factorial ^ 6 : ℕ))))
  · exact cone_gaussian_factor_le_of_separation _ _ _ _ _ hq hd hsep

/-- The reflected grid event has a uniform bound from a joint forward-window estimate. -/
theorem measure_factorialConeGridEvent_neg_one_le_uniform {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (C α : ℝ) (k n : ℕ) (h d : ℝ)
    (hh : 0 < h) (hH : h ≤ 1 / (k + 1 : ℝ)) (hd : 2 * h < d)
    (hq : 0 ≤ C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α)
    (J : ℝ≥0∞)
    (hJ : ∀ b : ℝ,
      μ ({ω | ∀ t ∈ Icc b (b + h),
        -(C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) ≤ coneIncr 0 t b ω} ∩
        {ω | ∀ t ∈ Icc b (b + h),
        -(C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) ≤ coneIncr 1 t b ω}) ≤ J)
    (i j : Fin (n.factorial ^ 6))
    (hsep : d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
      (i.val : ℝ) / (n.factorial ^ 6 : ℕ)) :
    μ (factorialConeGridEvent (-1) C α k n i j) ≤
      (ENNReal.ofReal (3 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) / √h) * J +
       ENNReal.ofReal (3 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) / √h) * J) *
       ENNReal.ofReal (2 * (C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α) /
         √(2 * Real.pi * (d - 2 * h))) := by
  have hg : (i.val : ℝ) / (n.factorial ^ 6 : ℕ) + h <
      (j.val : ℝ) / (n.factorial ^ 6 : ℕ) - h := by linarith
  refine (measure_factorialConeGridEvent_neg_one_le_survival hμ C α k n i j h hh hH hg hq).trans ?_
  apply mul_le_mul'
  · apply add_le_add
    · exact mul_le_mul' le_rfl (hJ _)
    · exact mul_le_mul' le_rfl (by simpa only [inter_comm] using (hJ
        (-((j.val : ℝ) / (n.factorial ^ 6 : ℕ)))))
  · exact cone_gaussian_factor_le_of_separation _ _ _ _ _ hq hd hsep

end LatticeProb.CorrelatedBM
