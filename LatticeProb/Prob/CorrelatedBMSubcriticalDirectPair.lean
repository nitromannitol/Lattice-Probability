import LatticeProb.Prob.CorrelatedBMForwardAngleBound
import LatticeProb.Prob.CorrelatedBMSubcriticalPairDimension

/-! # Subcritical barriers and direct-excursion pairs -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- Unit-time joint barriers have a uniform power bound at every positive
subcritical exponent. The constant is independent of the law and barrier. -/
theorem jointZeroBarrier_unit_le_subcritical_power {γ r : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hr : 0 < r) (hrγ : r < 4 / γ ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℝ), 0 < q →
      ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
        μ (jointZeroBarrier q 1) ≤ ENNReal.ofReal (B * q ^ r) := by
  obtain ⟨K, hK, hbound⟩ := jointZeroBarrier_le_subcritical hγ0 hγ2 hr hrγ
  let a : ℝ := 2 / (Real.sin ((Real.pi * γ ^ 2 / 4) / 2) * Real.sqrt 2)
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hangle0 : 0 < (Real.pi * γ ^ 2 / 4) / 2 := by positivity
  have hangleπ : (Real.pi * γ ^ 2 / 4) / 2 < Real.pi := by
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_left hγsq Real.pi_pos]
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by norm_num) (mul_pos (Real.sin_pos_of_pos_of_lt_pi hangle0 hangleπ)
      (Real.sqrt_pos.2 (by norm_num)))
  refine ⟨K * a ^ r, (mul_pos hK (Real.rpow_pos_of_pos ha _)).le, ?_⟩
  intro q hq μ hμ
  have h := hbound hμ q 1 hq (by norm_num)
  norm_num only [NNReal.coe_one, Real.sqrt_one, div_one] at h
  have heq : (2 * q) / (Real.sin ((Real.pi * γ ^ 2 / 4) / 2) * Real.sqrt 2) = a * q := by
    dsimp [a]
    ring
  rw [heq, Real.mul_rpow ha.le hq.le] at h
  convert h using 1; ring

/-- The Hausdorff dimension of pairs of distinct direct-excursion partners is
bounded by every nonnegative number at least one minus two over gamma squared. -/
theorem ae_dimH_direct_excursion_pairs_le_subcritical
    {γ : ℝ} {μ : Measure Path2} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsCorrelatedBM2 γ μ) (d : ℝ≥0) (hd : 1 - 2 / γ ^ 2 ≤ (d : ℝ)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ d := by
  apply ae_dimH_direct_excursion_pairs_le_of_subcritical_unit_power hμ d (4 / γ ^ 2)
    (by positivity)
  · have heq : 1 - (4 / γ ^ 2) / 2 = 1 - 2 / γ ^ 2 := by ring
    simpa only [heq] using hd
  · intro r hr hrγ
    exact jointZeroBarrier_unit_le_subcritical_power hγ0 hγ2 hr hrγ

end LatticeProb.CorrelatedBM
