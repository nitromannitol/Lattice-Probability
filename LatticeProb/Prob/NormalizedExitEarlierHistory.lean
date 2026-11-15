import LatticeProb.Prob.NormalizedNestedExitBound
import LatticeProb.Prob.StoppedPathExitHistoryCondExp

/-! # Normalized exit segments and earlier exit histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A normalized exit-segment conditional bound transfers to the raw history
at a strictly earlier concentric ball exit. -/
theorem ballExitHistory_condExp_le_of_normalized_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (k : ℕ) (s : ℝ≥0) (hs : 0 < s) (R S a p : ℝ)
    (hRS : R ≤ S) (hrR : r k < (s : ℝ) * R)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z (r k))
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z ((s : ℝ) * S)) ω ≠ ⊤) :
    let w := pathMap X hc
    let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
      C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
        ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
    let A := {ω | ∃ y, ball y ((s : ℝ) * a) ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z ((s : ℝ) * R)})
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z ((s : ℝ) * S)})}
    let B := {ω | ∃ y, ball y a ⊆ (fun t : ℝ => v ω t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 R})
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 S})}
    let Y := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
        (ball 0 R) ()) (v ω)
    (∀ᵐ ω ∂μ, p ≤ μ[B.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap Y inferInstance] ω) →
    ∀ᵐ ω ∂μ, p ≤ μ[A.indicator (fun _ => (1 : ℝ)) |
      ballExitHistory X hm hc z r hr k] ω := by
  dsimp only
  intro hp
  have hw : Measurable (pathMap X hc) := measurable_pathMap X (fun t => (hm t).measurable) hc
  let A : Set Ω := {ω | ∃ y, ball y ((s : ℝ) * a) ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
    (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z ((s : ℝ) * R)})
    (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z ((s : ℝ) * S)})}
  have hA : MeasurableSet A :=
    measurableSet_real_exit_segment_contains_ball hw _ _ isOpen_ball isOpen_ball _
  have hmid : ∀ᵐ ω ∂μ, openExitTime X (ball z ((s : ℝ) * R)) ω ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    exact ne_top_of_le_ne_top hω (monotone_openExitTime_ball X ω z
      (mul_le_mul_of_nonneg_left hRS s.coe_nonneg))
  have hbound := ae_le_condExp_real_ballExit_segment_of_normalize
    μ (pathMap X hc) hw z s hs R S a p hRS hfin hp
  exact ballExitHistory_condExp_const_le_of_outer_stoppedPath hm hc μ z r hr k hrR hstart
    hmid ((integrable_const (1 : ℝ)).indicator hA) hbound

end LatticeProb
