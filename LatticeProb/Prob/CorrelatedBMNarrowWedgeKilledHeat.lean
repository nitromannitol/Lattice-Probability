import LatticeProb.Prob.CorrelatedBMKernelDimension
import LatticeProb.Prob.CorrelatedBMNarrowWedgeSurvival

/-! # Killed heat mass for narrow Brownian wedges -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- For nonpositive correlation, the killed-heat mass of the associated wedge
is at most quadratic in the starting distance. -/
theorem lintegral_killedHeat_wedge_le_quadratic {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ : lrCov γ 0 1 ≤ 0)
    (hμ : IsCorrelatedBM2 γ μ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w, ENNReal.ofReal (killedHeat
      (complexSymmetricWedge (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
        (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2)) 1
      (r / (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) : ℝ) w)) ≤
      ENNReal.ofReal ((3 / ((Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) *
        Real.sqrt 2)) ^ 2 * r ^ 2) := by
  let a := Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2
  let b := Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2
  have ha : 0 < a := div_pos (Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])) (by norm_num)
  have hk := measure_openSymmetricWedgeBarrier_whitened_eq_lintegral_killedHeat
    hγ0 hγ2 hμ 0 a b r ha.ne' 1 (by norm_num)
  have hsub : openSymmetricWedgeBarrier a b r 1 ⊆ symmetricWedgeBarrier a b r 1 := by
    intro ω hω t ht
    exact le_of_lt (hω t ht)
  have hj := measure_jointZeroBarrier_le_of_nonpos_cov hγ0 hγ2 hρ hμ hr.le (by norm_num : (0 : ℝ) < 1)
  have hm := measure_jointZeroBarrier_eq_symmetricWedge (μ := μ) hγ0 hγ2 r 1
  have he : (3 * (r / (a * Real.sqrt 2)) / Real.sqrt 1) ^ 2 =
      (3 / (a * Real.sqrt 2)) ^ 2 * r ^ 2 := by
    rw [Real.sqrt_one]
    ring
  calc
    _ = (μ.map (whitenAt γ 0)) (openSymmetricWedgeBarrier a b r 1) := hk.symm
    _ ≤ (μ.map (whitenAt γ 0)) (symmetricWedgeBarrier a b r 1) := measure_mono hsub
    _ = μ (jointZeroBarrier r 1) := hm.symm
    _ ≤ ENNReal.ofReal (3 * (r / (a * Real.sqrt 2)) / Real.sqrt 1) ^ 2 := hj
    _ = _ := by rw [← ENNReal.ofReal_pow (by positivity), he]

/-- For nonpositive correlation the direct-excursion pair set has dimension zero. -/
theorem ae_dimH_direct_excursion_pairs_eq_zero_of_nonpos_cov
    {γ : ℝ} {μ : Measure Path2} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hρ : lrCov γ 0 1 ≤ 0) (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} = 0 := by
  let B : ℝ := (3 / ((Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) * Real.sqrt 2)) ^ 2
  have hK := ae_dimH_direct_excursion_pairs_le_of_wedge_killedHeat_bound
    hγ0 hγ2 hμ 0 B 2 (sq_nonneg _) (by norm_num) (by
      intro r hr
      simpa [B, Real.rpow_two] using lintegral_killedHeat_wedge_le_quadratic hγ0 hγ2 hρ hμ hr)
  filter_upwards [hK] with ω hω
  exact le_antisymm hω bot_le

end LatticeProb.CorrelatedBM
