/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianNormCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistProbTransfer

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_point_norm_compare_of_median_ratio
    (lam δ C : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hC : 0 < C)
    (hLow : C⁻¹ * lam ≤ δ) (hHigh : δ ≤ C * lam)
    (D : ℝ≥0∞) :
    ENNReal.ofReal δ⁻¹ * D ≤
        ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * D) ∧
      ENNReal.ofReal lam⁻¹ * D ≤
        ENNReal.ofReal C * (ENNReal.ofReal δ⁻¹ * D) := by
  have hinvLow : δ⁻¹ ≤ C * lam⁻¹ := by
    have h := (inv_le_inv₀ hδ (mul_pos (inv_pos.mpr hC) hlam)).2 hLow
    calc δ⁻¹ ≤ (C⁻¹ * lam)⁻¹ := h
      _ = C * lam⁻¹ := by field_simp
  have hinvHigh : lam⁻¹ ≤ C * δ⁻¹ := by
    have h := (inv_le_inv₀ (mul_pos hC hlam) hδ).2 hHigh
    have h' : C * (C * lam)⁻¹ ≤ C * δ⁻¹ :=
      mul_le_mul_of_nonneg_left h hC.le
    calc lam⁻¹ = C * (C * lam)⁻¹ := by field_simp
      _ ≤ C * δ⁻¹ := h'
  constructor
  · calc
      ENNReal.ofReal δ⁻¹ * D ≤ ENNReal.ofReal (C * lam⁻¹) * D := by
        gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * D) := by
        rw [ENNReal.ofReal_mul hC.le]
        ac_rfl
  · calc
      ENNReal.ofReal lam⁻¹ * D ≤ ENNReal.ofReal (C * δ⁻¹) * D := by
        gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal δ⁻¹ * D) := by
        rw [ENNReal.ofReal_mul hC.le]
        ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
