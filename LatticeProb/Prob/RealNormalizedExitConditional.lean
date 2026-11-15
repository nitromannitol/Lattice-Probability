import LatticeProb.Prob.RealNormalizedExitSegment
import LatticeProb.Prob.NormalizedExitCondExp

/-! # Conditional bounds for normalized real-time exit segments -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- The conditional success probabilities for corresponding real-time exit
segments agree under deterministic positive spatial and area-time normalization. -/
theorem condExp_real_ballExit_segment_normalize
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → C(ℝ≥0, E))
    (z : E) (s : ℝ≥0) (hs : 0 < s) (R S r : ℝ)
    (hR : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hS : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * S)) () ≠ ⊤) :
    let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
      (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
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
    MeasurableSet A → Measurable X → Measurable Y →
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Y inferInstance] := by
  dsimp only
  intro hA hX hY
  have hEq : (fun ω => ({ω | ∃ y, ball y ((s : ℝ) * r) ⊆
      (fun t : ℝ => w ω t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ ball z ((s : ℝ) * R)})
        (sInf {t : ℝ | 0 ≤ t ∧ w ω t.toNNReal ∉ ball z ((s : ℝ) * S)})}).indicator
          (fun _ => (1 : ℝ)) ω) =ᵐ[μ]
      (fun ω => ({ω | ∃ y, ball y r ⊆
        (fun t : ℝ => (((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
          (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ (((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
          (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) t.toNNReal ∉ ball 0 R})
        (sInf {t : ℝ | 0 ≤ t ∧ (((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
          (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) t.toNNReal ∉ ball 0 S})}).indicator
          (fun _ => (1 : ℝ)) ω) := by
    filter_upwards [hR, hS] with ω hRω hSω
    have h := real_ballExit_segment_contains_ball_normalize (w ω) z s hs R S r hRω hSω
    dsimp only at h
    classical
    change (if _ then (1 : ℝ) else 0) = (if _ then (1 : ℝ) else 0)
    simp only [mem_ofPred_eq]
    simp only [h]
  have hf := (integrable_const (μ := μ) (1 : ℝ)).indicator hA
  exact (condExp_stoppedPath_ballNormalize_areaTimeScale μ w z s hs R hR hX hY hf).trans
    (condExp_congr_ae hEq)

end LatticeProb
