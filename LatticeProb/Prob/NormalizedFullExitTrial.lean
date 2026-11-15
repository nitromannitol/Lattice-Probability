import LatticeProb.Prob.NormalizedExitEarlierHistory
import LatticeProb.Topology.RestartedNestedExitBall

/-! # Normalized exit segments and full exit trials -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A conditional bound for a normalized intermediate segment yields the same
bound for a larger consecutive ball-exit segment. -/
theorem ballExitHistory_condExp_full_segment_of_normalized
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (k : ℕ) (s : ℝ≥0) (hs : 0 < s) (R S a b p : ℝ)
    (hRS : R ≤ S) (hrR : r k < (s : ℝ) * R)
    (hSr : (s : ℝ) * S ≤ r (k + 1)) (hab : a ≤ (s : ℝ) * b)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z (r k))
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z (r (k + 1))) ω ≠ ⊤) :
    let w := pathMap X hc
    let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
      C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
        ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
    let B := {ω | ∃ y, ball y b ⊆ (fun t : ℝ => v ω t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 R})
      (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 S})}
    let Y := fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
        (ball 0 R) ()) (v ω)
    (∀ᵐ ω ∂μ, p ≤ μ[B.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap Y inferInstance] ω) →
    ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ y, ball y a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r k)})
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r (k + 1))})}).indicator
        (fun _ => (1 : ℝ)) | ballExitHistory X hm hc z r hr k] ω := by
  dsimp only
  intro hp
  have hw : Measurable (pathMap X hc) := measurable_pathMap X (fun t => (hm t).measurable) hc
  have hfinS : ∀ᵐ ω ∂μ, openExitTime X (ball z ((s : ℝ) * S)) ω ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    exact ne_top_of_le_ne_top hω (monotone_openExitTime_ball X ω z hSr)
  have hbound := ballExitHistory_condExp_le_of_normalized_segment hm hc μ z r hr k s hs
    R S b p hRS hrR hstart hfinS hp
  apply condExp_ball_event_mono_ae (ballExitHistory X hm hc z r hr k) _ _ hab
  · filter_upwards [hfin] with ω hω
    have hf : openExitTime (fun t (_ : Unit) =>
        (fun u : ℝ => X u.toNNReal ω) (0 + (t : ℝ))) (ball z (r (k + 1))) () ≠ ⊤ := by
      have heq : (fun (t : ℝ≥0) (_ : Unit) => (fun u : ℝ => X u.toNNReal ω)
          (0 + (t : ℝ))) = (fun (t : ℝ≥0) (_ : Unit) => X t ω) := by
        funext t u
        simp
      rw [heq]
      exact hω
    have hleft := firstExitEndpoint_le_of_radius_le (fun t : ℝ => X t.toNNReal ω) 0 z
      hrR.le ((hc ω).comp continuous_real_toNNReal)
      (ne_top_of_le_ne_top hf (monotone_openExitTime_ball _ () z
        ((mul_le_mul_of_nonneg_left hRS s.coe_nonneg).trans hSr)))
    have hright := firstExitEndpoint_le_of_radius_le (fun t : ℝ => X t.toNNReal ω) 0 z
      hSr ((hc ω).comp continuous_real_toNNReal) hf
    exact image_mono (Icc_subset_Icc hleft.2 hright.2)
  · exact measurableSet_real_exit_segment_contains_ball hw _ _ isOpen_ball isOpen_ball _
  · exact measurableSet_real_exit_segment_contains_ball hw _ _ isOpen_ball isOpen_ball _
  · exact hbound

end LatticeProb
