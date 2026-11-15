import LatticeProb.Prob.BallExitSegmentBallAE
import LatticeProb.Topology.ProperCurveFiniteExit

/-! # Exit segments after a measurable random time -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The nonnegative-time process obtained by shifting a two-sided curve. -/
def randomRootProcess {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (T : Ω → ℝ) :
    ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d) :=
  fun t ω => f ω (T ω + (t : ℝ))

/-- After a measurable random time, segment ball containment has a representative measurable
    at the outer ball exit, when the original curves almost surely escape compact sets. -/
theorem exists_measurableSet_ball_subset_randomRoot_exit_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))} {T : Ω → ℝ}
    (hf : Measurable f) (hT : Measurable T)
    (hproper : ∀ᵐ ω ∂μ, Tendsto (f ω) (cocompact ℝ) (cocompact _))
    (z : EuclideanSpace ℝ (Fin d)) {r R a : ℝ} (hr : r ≤ R) (ha : 0 < a) :
    ∃ s : Set Ω,
      MeasurableSet[(isStoppingTime_openExitTime
        (show ∀ t, StronglyMeasurable (randomRootProcess f T t) from by
          intro t
          exact ((continuous_eval : Continuous (fun p : C(ℝ, EuclideanSpace ℝ (Fin d)) × ℝ => p.1 p.2)).measurable.comp
            (hf.prodMk (hT.add measurable_const))).stronglyMeasurable)
        (fun ω => (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe))
        (isOpen_ball : IsOpen (ball z R))).measurableSpace] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆
        (fun t : ℝ => randomRootProcess f T t.toNNReal ω) '' Icc
        ((openExitTime (randomRootProcess f T) (ball z r) ω).toNNReal : ℝ)
        ((openExitTime (randomRootProcess f T) (ball z R) ω).toNNReal : ℝ)) := by
  have hm : ∀ t, StronglyMeasurable (randomRootProcess f T t) := by
    intro t
    exact ((continuous_eval : Continuous (fun p : C(ℝ, EuclideanSpace ℝ (Fin d)) × ℝ => p.1 p.2)).measurable.comp
      (hf.prodMk (hT.add measurable_const))).stronglyMeasurable
  have hc : ∀ ω, Continuous fun t => randomRootProcess f T t ω := fun ω =>
    (f ω).continuous.comp (continuous_const.add NNReal.continuous_coe)
  have hfin : ∀ᵐ ω ∂μ, openExitTime (randomRootProcess f T) (ball z R) ω ≠ ⊤ := by
    filter_upwards [hproper] with ω hω
    exact (openExitTime_ball_ne_top_of_tendsto_cocompact (f ω) hω (T ω) z R).1
  exact exists_measurableSet_ball_subset_nested_exit_segment_ae hm hc z hr ha hfin

end LatticeProb
