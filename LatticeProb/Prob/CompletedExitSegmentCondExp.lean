import LatticeProb.Prob.CompletedConditionalExpectation
import LatticeProb.Prob.CanonicalOpenExitHistory
import LatticeProb.Prob.RealExitSegmentMeasurable

/-! # Completed conditional expectations of exit segments -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric.GM
open scoped ENNReal NNReal

namespace LatticeProb

/-- Completing the path law and the stopped-path observation preserves the
conditional probability that a segment between two ball exits contains a ball. -/
theorem condExp_exitSegment_completion_ae_eq {d : ℕ}
    (ν : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (R S a : ℝ) :
    let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
      ∃ y, ball y a ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 R})
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 S})}
    let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
      (openExitTime (fun t (_ : Unit) => w t) (ball 0 R) ()) w
    let F := MeasurableSpace.comap O inferInstance
    (MeasureTheory.condExp (α := C(ℝ≥0, EuclideanSpace ℝ (Fin d)))
      (eventuallyMeasurableSpace F (ae ν))
      (@Measure.completion _ continuousMapMeasurableSpace ν)
      ((A.indicator (fun _ => (1 : ℝ))) ∘
        (@gm_ofNull _ continuousMapMeasurableSpace ν)) :
        C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → ℝ) =ᵐ[ν]
        ν[A.indicator (fun _ => (1 : ℝ)) | F] := by
  dsimp only
  apply condExp_completion_ae_eq
  · let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
      fun t w => w t
    let hm : ∀ t, StronglyMeasurable (X t) :=
      fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
    let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
    let hτ := isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin d)) R))
    have heq := canonical_openExit_stopped_history (d := d)
      (U := ball 0 R) isOpen_ball
    change hτ.measurableSpace = _ at heq
    change MeasurableSpace.comap (fun w => stoppedPath
      (openExitTime X (ball 0 R) w) w) inferInstance ≤ _
    rw [← heq]
    exact hτ.measurableSpace_le
  · exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_real_exit_segment_contains_ball measurable_id _ _ isOpen_ball isOpen_ball _)

end LatticeProb
