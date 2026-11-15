import LatticeProb.Prob.UniformPhaseInterval

/-! Convergence of interval phase measures at arbitrary growing scales. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- The phase law of interval Lebesgue measure converges in total variation to
uniform measure of the same mass, uniformly in the choice of phase shift. -/
theorem tendsto_tvDist_map_fract_mul_restrict_Ico {ι : Type*} {l : Filter ι}
    {u v : ℝ} (huv : u ≤ v) (a c : ι → ℝ) (ha : Tendsto a l atTop) :
    Tendsto (fun i => QuantumZipper.TV.tvDist
      (Measure.map (fun x : ℝ => Int.fract (a i * x - c i))
        (volume.restrict (Ico u v)))
      (ENNReal.ofReal (v - u) • volume.restrict (Ico 0 1))) l (𝓝 0) := by
  have hbound : Tendsto (fun i => ENNReal.ofReal ((a i)⁻¹)) l (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (tendsto_inv_atTop_zero.comp ha)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [ha.eventually_gt_atTop 0] with i hi
    exact tvDist_map_fract_mul_restrict_Ico_le hi huv (c i)

end LatticeProb
