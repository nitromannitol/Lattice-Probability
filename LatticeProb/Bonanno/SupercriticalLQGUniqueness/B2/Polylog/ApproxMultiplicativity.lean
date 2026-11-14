/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.ApproxMultiplicativity at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.Polylog

 


theorem approx_mul_of_three_comparisons
    (K cr cs crs a b : ℝ) (hK : 0 < K)
    (hcr : 0 ≤ cr) (hcs : 0 ≤ cs)
    (ha : K⁻¹ * cr ≤ a ∧ a ≤ K * cr)
    (hb : K⁻¹ * cs ≤ b ∧ b ≤ K * cs)
    (hab : K⁻¹ * crs ≤ a * b ∧ a * b ≤ K * crs) :
    (K⁻¹) ^ 3 * (cr * cs) ≤ crs ∧ crs ≤ K ^ 3 * (cr * cs) := by
  have hKi : 0 ≤ K⁻¹ := (inv_pos.mpr hK).le
  have ha0 : 0 ≤ a := (mul_nonneg hKi hcr).trans ha.1
  have hb0 : 0 ≤ b := (mul_nonneg hKi hcs).trans hb.1
  have hProdLo : (K⁻¹ * cr) * (K⁻¹ * cs) ≤ a * b :=
    mul_le_mul ha.1 hb.1 (mul_nonneg hKi hcs) ha0
  have hProdHi : a * b ≤ (K * cr) * (K * cs) :=
    mul_le_mul ha.2 hb.2 hb0 (mul_nonneg hK.le hcr)
  have hLo : (K⁻¹) ^ 2 * (cr * cs) ≤ a * b := by
    calc
      (K⁻¹) ^ 2 * (cr * cs) = (K⁻¹ * cr) * (K⁻¹ * cs) := by ring
      _ ≤ a * b := hProdLo
  have hHi : a * b ≤ K ^ 2 * (cr * cs) := by
    calc
      a * b ≤ (K * cr) * (K * cs) := hProdHi
      _ = K ^ 2 * (cr * cs) := by ring
  constructor
  · calc
      (K⁻¹) ^ 3 * (cr * cs) = K⁻¹ * ((K⁻¹) ^ 2 * (cr * cs)) := by ring
      _ ≤ K⁻¹ * (a * b) := mul_le_mul_of_nonneg_left hLo hKi
      _ ≤ K⁻¹ * (K * crs) := mul_le_mul_of_nonneg_left hab.2 hKi
      _ = crs := by field_simp [hK.ne']
  · calc
      crs = K * (K⁻¹ * crs) := by field_simp [hK.ne']
      _ ≤ K * (a * b) := mul_le_mul_of_nonneg_left hab.1 hK.le
      _ ≤ K * (K ^ 2 * (cr * cs)) := mul_le_mul_of_nonneg_left hHi hK.le
      _ = K ^ 3 * (cr * cs) := by ring

end SupercriticalLQGUniqueness.B2.Polylog
