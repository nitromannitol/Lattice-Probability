/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NormalizedCostArithmetic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointSquareCoupling

 

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_normalized_cost_compare
    (C F m lam D E : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hm : C⁻¹ * lam ≤ m ∧ m ≤ C * lam)
    (hcost : D ≤ F * E ∧ E ≤ F * D) :
    m⁻¹ * D ≤ (C * F) * (lam⁻¹ * E) ∧
      lam⁻¹ * E ≤ (C * F) * (m⁻¹ * D) := by
  have hCinv0 : C⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hCtop
  have hCinvtop : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC0
  have hmInv : m⁻¹ ≤ C * lam⁻¹ := by
    have h := ENNReal.inv_le_inv.mpr hm.1
    rw [ENNReal.mul_inv (Or.inl hCinv0) (Or.inl hCinvtop), inv_inv] at h
    simpa only [mul_comm] using h
  have hLamInv : lam⁻¹ ≤ C * m⁻¹ := by
    have h := ENNReal.inv_le_inv.mpr hm.2
    rw [ENNReal.mul_inv (Or.inl hC0) (Or.inl hCtop)] at h
    have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞) ≤ C from bot_le)
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul] using h'
  constructor
  · calc
      m⁻¹ * D ≤ m⁻¹ * (F * E) := mul_le_mul_of_nonneg_left hcost.1 bot_le
      _ ≤ (C * lam⁻¹) * (F * E) := mul_le_mul_of_nonneg_right hmInv bot_le
      _ = (C * F) * (lam⁻¹ * E) := by ac_rfl
  · calc
      lam⁻¹ * E ≤ lam⁻¹ * (F * D) := mul_le_mul_of_nonneg_left hcost.2 bot_le
      _ ≤ (C * m⁻¹) * (F * D) := mul_le_mul_of_nonneg_right hLamInv bot_le
      _ = (C * F) * (m⁻¹ * D) := by ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Pt
