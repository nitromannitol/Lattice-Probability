/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.CouplingErrorBudget at commit fdb5cad; the source is copied unchanged. -/
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Numerical choices for the finite coupling and the three stopped-law
comparisons in Theorem A. -/

open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma coupling_step_error_budget {η : ℝ} (hη : 0 < η) (K : ℕ) :
    0 < (η / 100) / (K + 1 : ℝ) ∧
      (K + 1 : ℝ≥0∞) * ENNReal.ofReal ((η / 100) / (K + 1 : ℝ)) =
        ENNReal.ofReal (η / 100) := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  refine ⟨by positivity, ?_⟩
  have hcast : ENNReal.ofReal (K + 1 : ℝ) = (K + 1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg K) zero_le_one]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [← hcast, ← ENNReal.ofReal_mul hK.le]
  congr 1
  field_simp

lemma exists_coupling_stopped_error_budget {η r : ℝ} (hη : 0 < η)
    (hr : 0 < r) (hrη : r ≤ η / 100) :
    ∃ q : ℝ≥0, 0 < q ∧
      ENNReal.ofReal (η / 100) + ENNReal.ofReal (η / 100) ≤ (q : ℝ≥0∞) ∧
      ENNReal.ofReal (η / 100) ≤ (q : ℝ≥0∞) ∧
      ENNReal.ofReal (η / 100) + ENNReal.ofReal (η / 100) +
        (ENNReal.ofReal (η / 100) + ENNReal.ofReal (η / 100)) ≤ (q : ℝ≥0∞) ∧
      ENNReal.ofReal (6 * r + η / 10) < (q : ℝ≥0∞) ∧
      ((q + q + q : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal η := by
  have hτ : 0 ≤ η / 100 := by positivity
  have hτ₂ : 0 ≤ η / 100 + η / 100 := add_nonneg hτ hτ
  let q : ℝ≥0 := ⟨η / 3, by positivity⟩
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < η / 3
    positivity
  · rw [← ENNReal.ofReal_add hτ hτ]
    exact ENNReal.ofReal_le_coe.mpr (by change η / 100 + η / 100 ≤ η / 3; linarith)
  · exact ENNReal.ofReal_le_coe.mpr (by change η / 100 ≤ η / 3; linarith)
  · rw [← ENNReal.ofReal_add hτ hτ, ← ENNReal.ofReal_add hτ₂ hτ₂]
    exact ENNReal.ofReal_le_coe.mpr
      (by change η / 100 + η / 100 + (η / 100 + η / 100) ≤ η / 3; linarith)
  · exact (ENNReal.ofReal_lt_coe_iff (by positivity)).mpr
      (by change 6 * r + η / 10 < η / 3; linarith)
  · have hsum : q + q + q = (⟨η, hη.le⟩ : ℝ≥0) := by
      apply Subtype.ext
      change η / 3 + η / 3 + η / 3 = η
      ring
    rw [hsum]
    exact le_of_eq ENNReal.ofReal_coe_nnreal.symm

end BouRabeeGwynne
