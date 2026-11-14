import LatticeProb.Prob.CorrelatedBMJointWindowTransfer

/-! # Scaling of joint barriers on continuous paths -/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A joint increment barrier on a positive time interval becomes a unit-time
barrier after Brownian scaling. -/
theorem jointZeroBarrier_scaled_iff (ω : Path2) (q h : ℝ) (hh : 0 < h) :
    (⟨fun t => (Real.sqrt h)⁻¹ • ω (h * t), by fun_prop⟩ : Path2) ∈
        jointZeroBarrier (q / Real.sqrt h) 1 ↔ ω ∈ jointZeroBarrier q h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hc (i : Fin 2) (t : ℝ) :
      coneIncr i t 0 (⟨fun t => (Real.sqrt h)⁻¹ • ω (h * t), by fun_prop⟩ : Path2) =
        (Real.sqrt h)⁻¹ * coneIncr i (h * t) 0 ω := by
    fin_cases i <;> simp [coneIncr, lrCoord, mul_sub]
  simp only [jointZeroBarrier, mem_inter_iff, mem_ofPred_eq, hc]
  have hi (i : Fin 2) :
      (∀ t ∈ Icc (0 : ℝ) 1, -(q / Real.sqrt h) ≤
        (Real.sqrt h)⁻¹ * coneIncr i (h * t) 0 ω) ↔
      (∀ t ∈ Icc (0 : ℝ) h, -q ≤ coneIncr i t 0 ω) := by
    constructor
    · intro H t ht
      have ht' : t / h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg ht.1 hh.le
        · exact (div_le_one hh).2 ht.2
      have H' := H (t / h) ht'
      have heq : h * (t / h) = t := by field_simp
      rw [heq] at H'
      have H'' : (-q) / Real.sqrt h ≤ coneIncr i t 0 ω / Real.sqrt h := by
        simpa [div_eq_mul_inv, mul_comm, neg_mul] using H'
      exact (div_le_div_iff_of_pos_right hs).1 H''
    · intro H t ht
      have ht' : h * t ∈ Icc (0 : ℝ) h := by
        constructor
        · exact mul_nonneg hh.le ht.1
        · nlinarith [ht.2]
      have H' := H (h * t) ht'
      have H'' := (div_le_div_iff_of_pos_right hs).2 H'
      simpa [div_eq_mul_inv, mul_comm] using H''
  exact and_congr (hi 0) (hi 1)

end LatticeProb.CorrelatedBM
