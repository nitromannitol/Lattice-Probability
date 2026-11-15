import LatticeProb.Prob.CorrelatedBMUnitPowerDimension

/-! # Sharp direct-excursion dimension from a joint barrier estimate -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- The angle-dependent unit-time joint barrier estimate gives the corresponding
Hausdorff-dimension bound for pairs of distinct direct-excursion partners. -/
theorem ae_dimH_direct_excursion_pairs_le_sharp_of_unit_power
    {γ : ℝ} (hγ : Real.sqrt 2 < γ) {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hJ : ∀ (q : ℝ), 0 < q → ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
      ν (jointZeroBarrier q 1) ≤ ENNReal.ofReal (B * q ^ (4 / γ ^ 2))) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ ENNReal.ofReal (1 - 2 / γ ^ 2) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsq : 2 < γ ^ 2 := by nlinarith
  have hnonneg : 0 ≤ 1 - 2 / γ ^ 2 := by
    have : 2 / γ ^ 2 ≤ 1 := (div_le_one (by linarith : 0 < γ ^ 2)).2 (by linarith)
    linarith
  let d : ℝ≥0 := ⟨1 - 2 / γ ^ 2, hnonneg⟩
  have hd : 1 - (4 / γ ^ 2) / 2 ≤ (d : ℝ) := by
    dsimp [d]
    have heq : 1 - (4 / γ ^ 2) / 2 = 1 - 2 / γ ^ 2 := by ring
    exact le_of_eq heq
  have h := ae_dimH_direct_excursion_pairs_le_of_unit_power hμ d B (4 / γ ^ 2) hB hd hJ
  have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal (1 - 2 / γ ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  simpa only [hd_eq] using h

end LatticeProb.CorrelatedBM
