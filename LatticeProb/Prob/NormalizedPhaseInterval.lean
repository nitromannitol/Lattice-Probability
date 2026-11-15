import LatticeProb.Prob.UniformPhaseIntervalLimit
import LatticeProb.Prob.TVScalar

/-! Normalized interval phase measures. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Normalizing Lebesgue measure on a nonempty bounded interval gives a
probability measure. -/
theorem isProbabilityMeasure_normalized_restrict_Ico {u v : ℝ} (huv : u < v) :
    IsProbabilityMeasure ((ENNReal.ofReal (v - u))⁻¹ •
      volume.restrict (Ico u v)) := by
  constructor
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Ico]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)))
    ENNReal.ofReal_ne_top

/-- The phase of a normalized interval measure converges in total variation
to uniform measure, for arbitrary shifts and growing real scales. -/
theorem tendsto_tvDist_normalized_map_fract_mul_restrict_Ico
    {ι : Type*} {l : Filter ι} {u v : ℝ} (huv : u < v)
    (a c : ι → ℝ) (ha : Tendsto a l atTop) :
    Tendsto (fun i => QuantumZipper.TV.tvDist
      ((ENNReal.ofReal (v - u))⁻¹ •
        Measure.map (fun x : ℝ => Int.fract (a i * x - c i))
          (volume.restrict (Ico u v)))
      (volume.restrict (Ico 0 1))) l (𝓝 0) := by
  let L : ℝ≥0∞ := ENNReal.ofReal (v - u)
  have hL0 : L ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))
  have hLt : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : L⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hL0
  have hlim := tendsto_tvDist_map_fract_mul_restrict_Ico huv.le a c ha
  change Tendsto (fun i => QuantumZipper.TV.tvDist
      (Measure.map (fun x : ℝ => Int.fract (a i * x - c i))
        (volume.restrict (Ico u v)))
      (L • volume.restrict (Ico 0 1))) l (𝓝 0) at hlim
  have hscale : Tendsto (fun i => L⁻¹ * QuantumZipper.TV.tvDist
      (Measure.map (fun x : ℝ => Int.fract (a i * x - c i))
        (volume.restrict (Ico u v)))
      (L • volume.restrict (Ico 0 1))) l (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul hlim (a := L⁻¹) (Or.inr hinv)
    simpa only [mul_zero] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards with i
    have h := tvDist_smul_le L⁻¹
      (Measure.map (fun x : ℝ => Int.fract (a i * x - c i))
        (volume.restrict (Ico u v))) (L • volume.restrict (Ico 0 1))
    simpa only [smul_smul, ENNReal.inv_mul_cancel hL0 hLt, one_smul] using h

end LatticeProb
