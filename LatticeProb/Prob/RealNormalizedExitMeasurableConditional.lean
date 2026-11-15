import LatticeProb.Prob.RealNormalizedExitConditional
import LatticeProb.Prob.RealExitSegmentMeasurable

/-! # Measurable normalized exit-segment conditional expectations -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- For a measurable Euclidean-valued path, deterministic normalization
preserves the conditional probability of the exit-segment ball event. -/
theorem condExp_real_ballExit_segment_normalize_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hw : Measurable w)
    (z : EuclideanSpace ℝ (Fin d)) (s : ℝ≥0) (hs : 0 < s) (R S r : ℝ)
    (hR : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hS : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * S)) () ≠ ⊤) :
    let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
      C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
        ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
    let A := {ω | ∃ y, ball y ((s : ℝ) * r) ⊆ (fun t : ℝ => w ω t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ ball z ((s : ℝ) * R)})
      (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ ball z ((s : ℝ) * S)})}
    let B := {ω | ∃ y, ball y r ⊆ (fun t : ℝ => v ω t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 R})
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 S})}
    let X := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (ball z ((s : ℝ) * R)) ()) (w ω)
    let Y := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
        (ball 0 R) ()) (v ω)
    Measurable X → Measurable Y →
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Y inferInstance] := by
  dsimp only
  intro hX hY
  exact condExp_real_ballExit_segment_normalize μ w z s hs R S r hR hS
    (measurableSet_real_exit_segment_contains_ball hw _ _ isOpen_ball isOpen_ball _) hX hY

end LatticeProb
