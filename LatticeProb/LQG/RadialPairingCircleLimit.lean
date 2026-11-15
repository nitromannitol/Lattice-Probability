import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea

/-! # Recovering a radial path from circle-bump pairings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.GMCFacts
  MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Mean-zero circle-bump pairings recover the centered value of a continuous
radial path whose associated radial function is locally integrable. -/
theorem tendsto_pairW_circleDiff (w : C(ℝ, ℝ))
    (hw : LocallyIntegrable (radialW w) volume) (t : ℝ) :
    Tendsto (fun n : ℕ => pairW (symmTest (circDiff n 0 (Real.exp (-t)) n 0 1).1) w)
      atTop (𝓝 (w t - w 0)) := by
  have hcircle (r : ℝ) (hr : 0 < r) :
      Real.circleAverage (radialW w) 0 r = w (-Real.log r) := by
    apply Real.circleAverage_const_on_circle
    intro z hz
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm] at hz
    simp only [radialW, hz]
  have hlim (r : ℝ) (hr : 0 < r) :
      Tendsto (fun n : ℕ => mollAvg (ofFunC (radialW w)) n 0 r) atTop
        (𝓝 (w (-Real.log r))) := by
    rw [← hcircle r hr]
    apply ConeArea3.tendsto_mollAvg_ofFunC hw isOpen_ne (continuousOn_radialW w) hr
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    exact norm_ne_zero_iff.1 (by rw [hz]; exact hr.ne')
  have h := (hlim (Real.exp (-t)) (Real.exp_pos _)).sub (hlim 1 one_pos)
  simp only [Real.log_exp, neg_neg, Real.log_one, neg_zero] at h
  convert h using 1
  funext n
  rw [pairW_symmTest, pairW, ← mollAvg_sub_eq]
