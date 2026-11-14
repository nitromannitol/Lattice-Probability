/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowThreshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Threshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_low_threshold {E Q B T S ell ratio : ℝ}
    (hE : 0 < E) (hQ : 0 < Q) (hB : 1 ≤ B)
    (hS : 0 < S) (hSsq : S^2 = T)
    (hS8 : 8 * E ≤ S) (hSQ : Q⁻¹ ≤ S)
    (hell0 : 0 ≤ ell) (hellE : ell ≤ E) (hQle : Q ≤ ratio * ell) :
    (B^4 * T)⁻¹ * ell ≤ (1/8) * S⁻¹ ∧
      (3/8) * S ≤ T * ratio * ell := by
  have hT : 0 < T := by rw [← hSsq]; positivity
  have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
  have hBT : 0 < B^4 * T := mul_pos (by linarith) hT
  have hden : T ≤ B^4 * T := by nlinarith
  have hinv : (B^4 * T)⁻¹ ≤ T⁻¹ :=
    (inv_le_inv₀ hBT hT).2 hden
  have hES : S⁻¹ * E ≤ (1/8 : ℝ) := by
    have h : E / S ≤ (1/8 : ℝ) :=
      (div_le_iff₀ hS).2 (by linarith)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hlast : T⁻¹ * E ≤ (1/8) * S⁻¹ := by
    rw [← hSsq]
    have hh := mul_le_mul_of_nonneg_left hES (inv_nonneg.mpr hS.le)
    rw [← inv_pow]
    calc
      (S⁻¹)^2 * E = S⁻¹ * (S⁻¹ * E) := by ring
      _ ≤ S⁻¹ * (1/8) := hh
      _ = (1/8) * S⁻¹ := by ring
  have hneg : (B^4 * T)⁻¹ * ell ≤ (1/8) * S⁻¹ := by
    calc
      _ ≤ T⁻¹ * ell := mul_le_mul_of_nonneg_right hinv hell0
      _ ≤ T⁻¹ * E := mul_le_mul_of_nonneg_left hellE (inv_nonneg.mpr hT.le)
      _ ≤ _ := hlast
  have hSQ' : 1 ≤ S * Q := by
    have hh := mul_le_mul_of_nonneg_left hSQ hQ.le
    nlinarith [mul_inv_cancel₀ hQ.ne']
  have hup0 : (3/8) * S ≤ T * Q := by
    rw [← hSsq]
    have hh := mul_le_mul_of_nonneg_left hSQ' hS.le
    nlinarith
  have hup : (3/8) * S ≤ T * ratio * ell := by
    calc
      _ ≤ T * Q := hup0
      _ ≤ T * (ratio * ell) := mul_le_mul_of_nonneg_left hQle hT.le
      _ = _ := by ring
  exact ⟨hneg, hup⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
