import LatticeProb.Prob.CorrelatedBMSymmetricWedge
import LatticeProb.Prob.CorrelatedBMUncorrelatedSurvival
import LatticeProb.Prob.CorrelatedBMNoCommonContour

/-! # Brownian survival in a narrow wedge -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A symmetric wedge with smaller transverse coefficient contains the original wedge. -/
theorem symmetricWedgeBarrier_mono_transverse {a b q h : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    symmetricWedgeBarrier a b q h ⊆ symmetricWedgeBarrier a a q h := by
  intro ω hω t ht
  have hb : 0 ≤ b := ha.trans hab
  have hm : |a * coneIncr 1 t 0 ω| ≤ |b * coneIncr 1 t 0 ω| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)
  exact hm.trans (hω t ht)

/-- Nonpositive correlation yields a quadratic joint barrier bound. -/
theorem measure_jointZeroBarrier_le_of_nonpos_cov {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ : lrCov γ 0 1 ≤ 0)
    (hμ : IsCorrelatedBM2 γ μ) {q h : ℝ} (hq : 0 ≤ q) (hh : 0 < h) :
    μ (jointZeroBarrier q h) ≤
      ENNReal.ofReal (3 * (q / (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 * Real.sqrt 2)) /
        Real.sqrt h) ^ 2 := by
  let a := Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2
  let b := Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2
  let ν := μ.map (whitenAt γ 0)
  let ξ := ν.map (whitenAt (Real.sqrt 2) 0)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])) (by norm_num)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
  have hν : IsCorrelatedBM2 (Real.sqrt 2) ν := isCorrelatedBM2_map_whitenAt hγ0 hγ2 0 hμ
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hξ : IsCorrelatedBM2 (Real.sqrt 2) ξ := isCorrelatedBM2_map_whitenAt hs0 hs2 0 hν
  have hq' : 0 ≤ q / (a * Real.sqrt 2) := div_nonneg hq (mul_nonneg ha.le hs0.le)
  have hbound := measure_jointZeroBarrier_sqrt_two_le hξ hq' hh
  have hsubset : symmetricWedgeBarrier a a q h ⊆
      (whitenAt (Real.sqrt 2) 0) ⁻¹' jointZeroBarrier (q / (a * Real.sqrt 2)) h := by
    intro ω hω
    have hc : lrCov (Real.sqrt 2) 0 1 = 0 := lrCov_sqrt_two_of_ne (by decide)
    have hi (t : ℝ) :
        coneIncr 0 t 0 (whitenAt (Real.sqrt 2) 0 ω) =
          (coneIncr 0 t 0 ω + coneIncr 1 t 0 ω) / Real.sqrt 2 ∧
        coneIncr 1 t 0 (whitenAt (Real.sqrt 2) 0 ω) =
          (coneIncr 0 t 0 ω - coneIncr 1 t 0 ω) / Real.sqrt 2 := by
      simp only [coneIncr, lrCoord_zero_whitenAt, lrCoord_one_whitenAt, hc,
        add_zero, sub_zero, mul_one, zero_add]
      constructor <;> ring
    change (whitenAt (Real.sqrt 2) 0 ω) ∈ jointZeroBarrier _ _
    simp only [jointZeroBarrier, mem_inter_iff, mem_ofPred_eq]
    constructor <;> intro t ht
    · have he := (abs_le.mp (hω t ht)).1
      have he' := (hi t).1
      rw [he']
      apply (le_div_iff₀ hs0).2
      have hdeneq : q / (a * Real.sqrt 2) * Real.sqrt 2 = q / a := by field_simp
      rw [neg_mul, hdeneq]
      have hx : -q / a ≤ coneIncr 0 t 0 ω + coneIncr 1 t 0 ω :=
        (div_le_iff₀ ha).2 (by nlinarith)
      simpa only [neg_div] using hx
    · have he := (abs_le.mp (hω t ht)).2
      have he' := (hi t).2
      rw [he']
      apply (le_div_iff₀ hs0).2
      have hdeneq : q / (a * Real.sqrt 2) * Real.sqrt 2 = q / a := by field_simp
      rw [neg_mul, hdeneq]
      have hx : -q / a ≤ coneIncr 0 t 0 ω - coneIncr 1 t 0 ω :=
        (div_le_iff₀ ha).2 (by nlinarith)
      simpa only [neg_div] using hx
  calc
    μ (jointZeroBarrier q h) = ν (symmetricWedgeBarrier a b q h) :=
      measure_jointZeroBarrier_eq_symmetricWedge hγ0 hγ2 q h
    _ ≤ ν (symmetricWedgeBarrier a a q h) :=
      measure_mono (symmetricWedgeBarrier_mono_transverse ha.le hab)
    _ ≤ ξ (jointZeroBarrier (q / (a * Real.sqrt 2)) h) := by
      rw [show ξ (jointZeroBarrier (q / (a * Real.sqrt 2)) h) =
          ν ((whitenAt (Real.sqrt 2) 0) ⁻¹' jointZeroBarrier (q / (a * Real.sqrt 2)) h) from
        Measure.map_apply (continuous_whitenAt _ _).measurable
          (measurableSet_jointZeroBarrier _ _ hh.le)]
      exact measure_mono hsubset
    _ ≤ _ := hbound

end LatticeProb.CorrelatedBM
