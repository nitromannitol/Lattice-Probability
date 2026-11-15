import LatticeProb.Prob.ConditionalEventLaw
import LatticeProb.Prob.RealNormalizedExitObservations

/-! # Conditional exit-segment bounds under normalized path laws -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A conditional exit-segment bound on a reference path law transfers to a
path whose deterministic spatial and temporal normalization has that law. -/
theorem condExp_unit_exit_segment_of_normalized_path_law
    {d : ℕ} (μ ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d))))
    [IsFiniteMeasure μ] (z : EuclideanSpace ℝ (Fin d))
    (s : ℝ≥0) (hs : 0 < s) (q η p : ℝ) :
    let N := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) =>
      ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
    let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
      ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
    let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
      (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
    μ.map N = ν →
    (∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap O inferInstance] w) →
    ∀ᵐ w ∂μ, p ≤ μ[(N ⁻¹' A).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (O ∘ N) inferInstance] w := by
  dsimp only
  intro hlaw hp
  let N := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) =>
    ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
      C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp w).comp
        ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
  let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
    ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
  let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
    (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
  have hN : Measurable N := by
    exact ((ContinuousMap.continuous_precomp ⟨areaTimeScale s hs,
      (areaTimeScale s hs).continuous⟩).comp
      (ContinuousMap.continuous_postcomp
        (⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
          C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))))).measurable
  have hA : MeasurableSet A :=
    measurableSet_real_exit_segment_contains_ball measurable_id _ _ isOpen_ball isOpen_ball _
  have hO : Measurable O := measurable_stoppedPath_openExitTime measurable_id isOpen_ball
  have h := condExp_indicator_const_le_of_map_eq μ ν N hN hlaw hO.comap_le A hA hp
  simpa only [MeasurableSpace.comap_comp] using h

end LatticeProb
