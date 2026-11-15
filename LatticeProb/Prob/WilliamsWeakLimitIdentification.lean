import LatticeProb.Prob.WilliamsUpcrossIdentification
import LatticeProb.Prob.StayWeakLimitStart

/-! # A conditioned Brownian weak limit and the Williams law -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

open QuantumZipper QuantumZipper.Williams

/-- The drifted weak limit of Brownian motion conditioned to stay above a
vanishing negative level has the law of the Williams post-last-zero path. -/
theorem driftMap_weakLimit_eq_williamsPostLastPath_law
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b b' : ℝ≥0 → Ω → ℝ} (hb : GoodBM b P) (hb' : GoodBM b' P)
    {d : ℝ} (hd : 0 < d) (hind : IndepFun (pathOf b) (pathOf b') P)
    (ν : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto (fun δ : ℝ =>
      ∫ w, f w ∂((P.map (pathMap b hb.cont))[|driftMap d ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ν.map (driftMap d) = P.map (williamsPostLastPath hb' 1 d) := by
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have : IsProbabilityMeasure (ν.map (driftMap d)) :=
    isProb_map (measurable_driftMap d).aemeasurable
  have hB : IsBrownianReal b P := ⟨hb.pre, Eventually.of_forall hb.cont⟩
  have hzero : ∀ᵐ z ∂(ν.map (driftMap d)), z 0 = 0 := by
    rw [ae_map_iff (measurable_driftMap d).aemeasurable
      (isClosed_eq (continuous_eval_const (0 : ℝ≥0)) continuous_const).measurableSet]
    filter_upwards [ae_eval_zero_of_weakLimit hB hb.meas hb.cont hd hν] with z hz
    simpa only [driftMap_apply, NNReal.coe_zero, mul_zero, add_zero] using hz
  exact eq_williamsPostLastPath_law_of_upcross_pieces hb hb' hd hind _ hzero
    (ae_map_piece_eq hB hb.meas hb.cont hd hν)

end LatticeProb
