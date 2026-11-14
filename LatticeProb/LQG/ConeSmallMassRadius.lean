import LatticeProb.Analysis.LastLevelSmallScale
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath
import LatticeProb.Prob.ContinuousPathLaw

/-! # Small-mass scales of quantum cones -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.CellScaling
open scoped NNReal

namespace LatticeProb

/-- The cone scale tends to zero as its mass parameter tends to zero.
The two Brownian motions need not be independent. -/
theorem ae_tendsto_coneScale_small_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α : ℝ} (hγ : 0 < γ) (hα : α < lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, Tendsto (coneScale γ α (fun t => B t ω) (fun t => B' t ω))
      (𝓝[>] 0) (𝓝 0) := by
  have hμ : 0 < lqgQ γ - α := sub_pos.mpr hα
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, hB'.cont,
    hB'.eval_zero_ae_eq_zero, ae_goodDrift hB' hμ,
    QuantumZipper.BMLLN.ae_tendsto_div_atTop hB] with ω hc hzero hc' hzero' hgood hlln
  let f := coneLogRadial γ α (fun t => B t ω) (fun t => B' t ω)
  have hcont : Continuous f := by
    have hrad := MatedCRTHarmonic.ConeScaling.continuous_coneRadial_of hc hzero hc' hzero'
      hgood.bddAbove_zeroSet
    exact (hrad.comp continuous_neg).add (continuous_const.mul continuous_id)
  have hright : Tendsto f atTop atTop := by
    have h := hgood.tendsto_atTop.comp
      ((tendsto_const_nhds (x := lastZeroR (coneDrift γ α (fun t => B' t ω)))).add_atTop tendsto_id)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (coneLogRadial_of_pos γ α _ _ hs).symm
  have hsub : Tendsto (fun t : ℝ => (-B t.toNNReal ω) / t) atTop (𝓝 0) := by
    have h := hlln.comp tendsto_real_toNNReal_atTop
    have hneg := h.neg
    simp only [neg_zero] at hneg
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [Real.coe_toNNReal _ ht.le, div_eq_mul_inv, mul_comm]
  have hleft : Tendsto f atBot atBot := by
    have h := (ContinuousPathLaw.tendsto_add_pos_drift_of_sublinear
      (fun t : ℝ => -B t.toNNReal ω) (lqgQ γ - α) hμ hsub).comp tendsto_neg_atBot_atTop
    have hneg := tendsto_neg_atTop_atBot.comp h
    apply hneg.congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with s hs
    dsimp [f]
    rw [coneLogRadial_of_nonpos γ α _ _ hs]
    ring
  have hy : Tendsto (fun b : ℝ => γ⁻¹ * Real.log b) (𝓝[>] 0) atBot :=
    (tendsto_const_mul_atBot_of_pos (inv_pos.mpr hγ)).2 Real.tendsto_log_nhdsGT_zero
  have h := (tendsto_exp_sSup_level_atBot hcont hleft hright).comp hy
  exact h

end LatticeProb
