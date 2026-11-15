import LatticeProb.Prob.RealNormalizedExitObservations
import LatticeProb.Prob.BallExitRadius

/-! # Conditional bounds for normalized nested exits -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A conditional lower bound for a normalized exit segment transfers to the
original segment when the outer exit is almost surely finite. -/
theorem ae_le_condExp_real_ballExit_segment_of_normalize
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hw : Measurable w)
    (z : EuclideanSpace ℝ (Fin d)) (s : ℝ≥0) (hs : 0 < s) (R S r p : ℝ)
    (hRS : R ≤ S)
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
    (∀ᵐ ω ∂μ, p ≤ μ[B.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap Y inferInstance] ω) →
    ∀ᵐ ω ∂μ, p ≤ μ[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] ω := by
  dsimp only
  intro hp
  have hR : ∀ᵐ ω ∂μ, openExitTime (fun t (_ : Unit) => w ω t)
      (ball z ((s : ℝ) * R)) () ≠ ⊤ := by
    filter_upwards [hS] with ω hω
    exact ne_top_of_le_ne_top hω (monotone_openExitTime_ball
      (fun t (_ : Unit) => w ω t) () z (mul_le_mul_of_nonneg_left hRS s.coe_nonneg))
  have heq := condExp_real_ballExit_segment_normalize_of_path_measurable
    μ w hw z s hs R S r hR hS
  filter_upwards [hp, heq] with ω hpω heqω
  rw [heqω]
  exact hpω

end LatticeProb
