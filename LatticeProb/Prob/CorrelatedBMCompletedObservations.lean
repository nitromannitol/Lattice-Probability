import LatticeProb.Prob.CorrelatedBMIncrementConditioning
import LatticeProb.Prob.ConditionalIntersectionDetermination

/-! # Almost-sure observations of correlated Brownian increments -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MeasurableSpace Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Conditional independence persists for sigma-algebras whose events are almost surely equal
    to events of the respective centered past and future. -/
theorem condIndepEv_increment_observations {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {a b : ℝ} (hab : a ≤ b)
    {A B : MeasurableSpace Path2}
    (hA : AELeSigma A (incrementSigma lrCoord (Iic b) b) μ)
    (hB : AELeSigma B (incrementSigma lrCoord (Ici a) a) μ) :
    CondIndepEv (incrementSigma lrCoord (Icc a b) a) A B μ :=
  (condIndepEv_increment_past_future hμ hab).of_aeLe hA hB

/-- The almost-sure closures of the centered past and future remain conditionally independent
    given the centered increments on the intervening segment. -/
theorem condIndepEv_increment_aeClosures {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {a b : ℝ} (hab : a ≤ b) :
    CondIndepEv (incrementSigma lrCoord (Icc a b) a)
      (aeClosure (incrementSigma lrCoord (Iic b) b) μ)
      (aeClosure (incrementSigma lrCoord (Ici a) a) μ) μ :=
  condIndepEv_increment_observations hμ hab (fun _ h => h) (fun _ h => h)

/-- An observation determined almost surely by each centered half-path is determined almost
    surely by the centered increments on the intervening segment. -/
theorem aeLeSigma_increment_segment_of_two_sides {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {a b : ℝ} (hab : a ≤ b)
    {C : MeasurableSpace Path2}
    (hCpast : AELeSigma C (incrementSigma lrCoord (Iic b) b) μ)
    (hCfuture : AELeSigma C (incrementSigma lrCoord (Ici a) a) μ) :
    AELeSigma C (incrementSigma lrCoord (Icc a b) a) μ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hmeas (T : Set ℝ) (c : ℝ) :
      incrementSigma lrCoord T c ≤ (ContinuousMap.measurableSpace : MeasurableSpace Path2) := by
    refine iSup_le fun i => iSup_le fun t => iSup_le fun _ => ?_
    exact measurable_iff_comap_le.mp (measurable_coneIncr i t c)
  exact AELeSigma.of_condIndepEv_two_sides (incrementSigma_segment_le_past lrCoord hab)
    (hmeas _ _) (hmeas _ _) (condIndepEv_increment_past_future hμ hab) hCpast hCfuture

end LatticeProb.CorrelatedBM
