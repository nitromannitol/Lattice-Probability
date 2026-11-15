import LatticeProb.Prob.ExitObservationCondExp
import LatticeProb.Prob.NormalizedExitTransform

/-! # Conditional expectations for normalized ball-exit observations -/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Positive spatial normalization and its squared-time change preserve the
conditional expectation given the corresponding stopped ball-exit observation. -/
theorem condExp_stoppedPath_ballNormalize_areaTimeScale
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → C(ℝ≥0, E))
    (z : E) (s : ℝ≥0) (hs : 0 < s) (R : ℝ)
    (hfin : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hA : Measurable fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (ball z ((s : ℝ) * R)) ()) (w ω))
    (hB : Measurable fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
        (ball 0 R) ())
      (((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
        (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩))
    {f : Ω → ℝ} (hf : Integrable f μ) :
    let A := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t) (ball z ((s : ℝ) * R)) ()) (w ω)
    let B := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
        (ball 0 R) ())
      (((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp
        (w ω)).comp ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩)
    μ[f | MeasurableSpace.comap A inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap B inferInstance] := by
  have hfin' : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ballNormalize z s hs ⁻¹' ball 0 R) () ≠ ⊤ := by
    simpa only [ballNormalize_preimage_ball] using hfin
  have hA' : Measurable fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => w ω t)
        (ballNormalize z s hs ⁻¹' ball 0 R) ()) (w ω) := by
    simpa only [ballNormalize_preimage_ball] using hA
  have h := condExp_stoppedPath_openExit_comp_spatial_orderIso μ w
    (ballNormalize z s hs) (areaTimeScale s hs) (ball 0 R) isOpen_ball hfin' hA' hB hf
  simpa only [ballNormalize_preimage_ball] using h

end LatticeProb
