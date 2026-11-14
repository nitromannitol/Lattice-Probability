/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BandTailLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.OpenBandLaw

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 
private theorem ennreal_mul_lt_mul_iff {r a b : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrtop : r ≠ ⊤) : r * a < r * b ↔ a < b := by
  constructor
  · intro h
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    have hmul : r * b ≤ r * a := by gcongr
    exact (not_lt_of_ge hmul) h
  · exact ENNReal.mul_lt_mul_right hr0 hrtop

 


theorem measure_band_crossing_open_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n) (a : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let F : ℂ → ℂ := fun z => (r : ℂ) * z
    P {ω | crossLenIn ξ (fun z => phiMN W P k n z ω)
          (F '' U) (F '' A) (F '' B) < ENNReal.ofReal r * a} =
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω)
          U A B < a} := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  have h := measure_band_crossing_open_dilate P W hW ξ U A B hkn
    (S := Iio (ENNReal.ofReal r * a)) measurableSet_Iio
  simp only [Set.mem_Iio] at h
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  simpa only [r, F, (ennreal_mul_lt_mul_iff hr0 hrtop)] using h

 


theorem measure_band_crossing_open_gt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n) (a : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let F : ℂ → ℂ := fun z => (r : ℂ) * z
    P {ω | ENNReal.ofReal r * a <
          crossLenIn ξ (fun z => phiMN W P k n z ω)
            (F '' U) (F '' A) (F '' B)} =
      P {ω | a < crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω)
          U A B} := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  have h := measure_band_crossing_open_dilate P W hW ξ U A B hkn
    (S := Ioi (ENNReal.ofReal r * a)) measurableSet_Ioi
  simp only [Set.mem_Ioi] at h
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  simpa only [r, F, (ennreal_mul_lt_mul_iff hr0 hrtop)] using h

end SupercriticalLQGUniqueness.B2.DG20Pt
