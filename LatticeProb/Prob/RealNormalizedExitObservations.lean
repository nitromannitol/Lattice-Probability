import LatticeProb.Prob.RealNormalizedExitMeasurableConditional

/-! # Measurable stopped observations for normalized exit segments -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Stopping a measurable continuous Euclidean path at an open-set exit gives
    a measurable path, including when the exit time is infinite. -/
theorem measurable_stoppedPath_openExitTime
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {w : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))} (hw : Measurable w)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    Measurable (fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) U ()) (w ω)) := by
  have hτ : Measurable (fun ω => openExitTime (fun t (_ : Unit) => w ω t) U ()) := by
    have h := measurable_openExitTime (B := fun t ω => w ω t)
      (fun t => ((ContinuousMapBorel.ContinuousMap.measurable_eval t).comp hw).stronglyMeasurable)
      (fun ω => (w ω).continuous) hU
    exact h
  exact continuous_stoppedPath.measurable.comp (hτ.prodMk hw)

/-- Deterministic normalization preserves the conditional probability of a
    real-time exit-segment ball event for measurable Euclidean paths. -/
theorem condExp_real_ballExit_segment_normalize_of_path_measurable
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
    μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Y inferInstance] := by
  let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
      ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
  have hv : Measurable v := by
    exact ((ContinuousMap.continuous_precomp ⟨areaTimeScale s hs,
      (areaTimeScale s hs).continuous⟩).comp
      (ContinuousMap.continuous_postcomp
        (⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
          C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))))).measurable.comp hw
  exact condExp_real_ballExit_segment_normalize_of_measurable μ w hw z s hs R S r hR hS
    (measurable_stoppedPath_openExitTime hw isOpen_ball)
    (measurable_stoppedPath_openExitTime hv isOpen_ball)

end LatticeProb
