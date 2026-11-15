import LatticeProb.Prob.FirstHitRandomRoot
import LatticeProb.Prob.RandomRootExitSegment

/-! # Nested exit segments rooted at a first hit -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- Centering a random continuous complex curve at a random point is measurable. -/
theorem measurable_centeredEuclideanCurve {Ω : Type*} [MeasurableSpace Ω]
    {c : Ω → C(ℝ, ℂ)} {z : Ω → ℂ} (hc : Measurable c) (hz : Measurable z) :
    Measurable (fun ω => centeredEuclideanCurve (c ω) (z ω)) := by
  have hcenter : Continuous (fun p : C(ℝ, ℂ) × ℂ => centeredEuclideanCurve p.1 p.2) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact Complex.orthonormalBasisOneI.repr.continuous.comp
      ((continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
        (continuous_snd.comp continuous_fst))
  change Measurable ((fun p : C(ℝ, ℂ) × ℂ => centeredEuclideanCurve p.1 p.2) ∘
    (fun ω => (c ω, z ω)))
  exact hcenter.measurable.comp (hc.prodMk hz)

/-- A first-hit rooted complex curve has a stopped-measurable representative for its nested
exit segment ball event, in the natural filtration of the rooted curve. -/
theorem exists_measurableSet_ball_subset_firstHit_exit_segment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c : Ω → C(ℝ, ℂ)} {z : Ω → ℂ}
    (hc : Measurable c) (hz : Measurable z)
    (hproper : ∀ᵐ ω ∂μ, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    {r R a : ℝ} (hr : r ≤ R) (ha : 0 < a) :
    let f : Ω → C(ℝ, EuclideanSpace ℝ (Fin 2)) :=
      fun ω => centeredEuclideanCurve (c ω) (z ω)
    let T : Ω → ℝ := fun ω => MatedCRTHarmonic.GMS4b.hitTime (c ω) (z ω)
    ∃ s : Set Ω,
      MeasurableSet[(isStoppingTime_openExitTime
        (show ∀ t, StronglyMeasurable (randomRootProcess f T t) from by
          intro t
          exact ((continuous_eval : Continuous (fun p : C(ℝ, EuclideanSpace ℝ (Fin 2)) × ℝ => p.1 p.2)).measurable.comp
            ((measurable_centeredEuclideanCurve hc hz).prodMk
              ((measurable_firstHitTime hc hz).add measurable_const))).stronglyMeasurable)
        (fun ω => (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe))
        (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin 2)) R))).measurableSpace] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆
        (fun t : ℝ => randomRootProcess f T t.toNNReal ω) '' Icc
        ((openExitTime (randomRootProcess f T) (ball 0 r) ω).toNNReal : ℝ)
        ((openExitTime (randomRootProcess f T) (ball 0 R) ω).toNNReal : ℝ)) := by
  dsimp only
  have hf := measurable_centeredEuclideanCurve hc hz
  have hp : ∀ᵐ ω ∂μ, Tendsto (centeredEuclideanCurve (c ω) (z ω))
      (cocompact ℝ) (cocompact (EuclideanSpace ℝ (Fin 2))) := by
    filter_upwards [hproper] with ω hω
    have htrans : Tendsto (fun w : ℂ => w - z ω) (cocompact ℂ) (cocompact ℂ) := by
      simpa [sub_eq_add_neg] using (Homeomorph.addRight (-z ω)).isClosedEmbedding.tendsto_cocompact
    have hrepr := Complex.orthonormalBasisOneI.repr.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    exact hrepr.comp (htrans.comp hω)
  exact exists_measurableSet_ball_subset_randomRoot_exit_segment hf
    (measurable_firstHitTime hc hz) hp 0 hr ha

end LatticeProb
