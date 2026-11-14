import LatticeProb.Prob.CorrelatedBMJointBarrierProbabilityScaling
import LatticeProb.Prob.CorrelatedBMDirectPairOptimalDimension

/-! # Joint barrier estimates and direct-excursion dimension -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A unit-time power bound, uniform in the law and barrier, transfers to
any positive time horizon with an explicit rescaled constant. -/
theorem measure_jointZeroBarrier_le_of_unit_power {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (B p q h : ℝ) (hq : 0 < q) (hh : 0 < h)
    (hJ : ∀ (r : ℝ), 0 < r → ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
      ν (jointZeroBarrier r 1) ≤ ENNReal.ofReal (B * r ^ p)) :
    μ (jointZeroBarrier q h) ≤ ENNReal.ofReal ((B / (Real.sqrt h) ^ p) * q ^ p) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hb := measure_jointZeroBarrier_le_of_unit hμ q h hh
    (ENNReal.ofReal (B * (q / Real.sqrt h) ^ p)) (hJ _ (div_pos hq hs))
  convert hb using 1
  congr 1
  rw [Real.div_rpow hq.le hs.le]
  ring

/-- A uniform unit-time joint barrier power bound yields a dimension bound
for the pairs of distinct direct-excursion partners. -/
theorem ae_dimH_direct_excursion_pairs_le_of_unit_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (d : ℝ≥0) (B p : ℝ) (hB : 0 ≤ B) (hd : 1 - p / 2 ≤ (d : ℝ))
    (hJ : ∀ (q : ℝ), 0 < q → ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
      ν (jointZeroBarrier q 1) ≤ ENNReal.ofReal (B * q ^ p)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ d := by
  apply ae_dimH_direct_excursion_pairs_le_of_all_mesh_exponents hμ d 1 p (by norm_num) hd
  intro α hα h hh
  refine ⟨B / (Real.sqrt h) ^ p, div_nonneg hB (Real.rpow_nonneg (Real.sqrt_nonneg h) _), ?_⟩
  intro n ν hν
  have hm : 0 < factorialGridMesh n := by
    unfold factorialGridMesh
    positivity
  have hq : 0 < 1 * factorialGridMesh n ^ (α : ℝ) := by
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hm _)
  exact measure_jointZeroBarrier_le_of_unit_power hν B p _ h hq hh hJ

end LatticeProb.CorrelatedBM
