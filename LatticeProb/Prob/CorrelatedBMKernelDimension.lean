import LatticeProb.Prob.CorrelatedBMWedgeKilledHeat
import LatticeProb.Prob.CorrelatedBMNoCommonContour
import LatticeProb.Prob.CorrelatedBMUnitPowerDimension

/-! # Wedge killed heat and direct-excursion dimension -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- A power bound for the wedge killed-heat mass gives the corresponding
almost-sure dimension bound for pairs of distinct direct-excursion partners. -/
theorem ae_dimH_direct_excursion_pairs_le_of_wedge_killedHeat_bound
    {γ : ℝ} {μ : Measure Path2} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsCorrelatedBM2 γ μ) (d : ℝ≥0) (B p : ℝ)
    (hB : 0 ≤ B) (hd : 1 - p / 2 ≤ (d : ℝ))
    (hK : ∀ r : ℝ, 0 < r →
      (∫⁻ w, ENNReal.ofReal (killedHeat
        (complexSymmetricWedge (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
          (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2)) 1
        (r / (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) : ℝ) w)) ≤
        ENNReal.ofReal (B * r ^ p)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ d := by
  have ha : 0 < Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 :=
    div_pos (Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])) (by norm_num)
  apply ae_dimH_direct_excursion_pairs_le_of_unit_power hμ d (B * 2 ^ p) p
    (mul_nonneg hB (Real.rpow_nonneg (by norm_num) _)) hd
  intro q hq ν hν
  apply measure_jointZeroBarrier_le_of_open_wedge_power hγ0 hγ2 q 1 B p hq
  have hk := measure_openSymmetricWedgeBarrier_whitened_eq_lintegral_killedHeat
    hγ0 hγ2 hν 0 (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
    (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2) (2 * q) ha.ne' 1 (by norm_num)
  simpa only [NNReal.coe_one] using hk.le.trans (hK (2 * q) (by positivity))

end LatticeProb.CorrelatedBM
