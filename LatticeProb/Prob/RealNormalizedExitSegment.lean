import LatticeProb.Prob.RealExitSegmentTrace
import LatticeProb.Prob.NormalizedExitSegmentBall

/-! # Real-time normalized exit segments -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite ball exit remains finite after positive spatial normalization and
its associated area-time change. -/
theorem openExitTime_ballNormalize_areaTimeScale_ne_top
    (w : C(ℝ≥0, E)) (z : E) (s : ℝ≥0) (hs : 0 < s) (R : ℝ)
    (hfin : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) () ≠ ⊤) :
    openExitTime (fun t (_ : Unit) =>
      ballNormalize z s hs (w (areaTimeScale s hs t))) (ball 0 R) () ≠ ⊤ := by
  let τ := openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) ()
  have hout : w τ.toNNReal ∉ ball z ((s : ℝ) * R) :=
    openExitTime_not_mem isOpen_ball w.continuous hfin
  have hout' : ballNormalize z s hs (w τ.toNNReal) ∉ ball 0 R := by
    simpa only [← Set.mem_preimage, ballNormalize_preimage_ball] using hout
  have hle : openExitTime (fun t (_ : Unit) =>
      ballNormalize z s hs (w (areaTimeScale s hs t))) (ball 0 R) () ≤
      ((areaTimeScale s hs).symm τ.toNNReal : ℝ≥0∞) := by
    apply openExitTime_le_of_not_mem
    simpa only [OrderIso.apply_symm_apply] using hout'
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle

/-- Positive spatial normalization and area-time scaling preserve the event
that a finite exit segment contains a ball of the corresponding radius,
expressed using real infima of exit times. -/
theorem real_ballExit_segment_contains_ball_normalize
    (w : C(ℝ≥0, E)) (z : E) (s : ℝ≥0) (hs : 0 < s) (R S r : ℝ)
    (hR : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hS : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * S)) () ≠ ⊤) :
    let v := ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp w).comp
      ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
    (∃ y, ball y ((s : ℝ) * r) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball z ((s : ℝ) * R)})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball z ((s : ℝ) * S)})) ↔
    (∃ y, ball y r ⊆ (fun t : ℝ => v t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 R})
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 S})) := by
  let v : C(ℝ≥0, E) := ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E)).comp w).comp
    ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
  have hvR : openExitTime (fun t (_ : Unit) => v t) (ball 0 R) () ≠ ⊤ :=
    openExitTime_ballNormalize_areaTimeScale_ne_top w z s hs R hR
  have hvS : openExitTime (fun t (_ : Unit) => v t) (ball 0 S) () ≠ ⊤ :=
    openExitTime_ballNormalize_areaTimeScale_ne_top w z s hs S hS
  change (∃ y, ball y ((s : ℝ) * r) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball z ((s : ℝ) * R)})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball z ((s : ℝ) * S)})) ↔
    (∃ y, ball y r ⊆ (fun t : ℝ => v t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 R})
      (sInf {t : ℝ | 0 ≤ t ∧ v t.toNNReal ∉ ball 0 S}))
  rw [real_exit_segment_contains_ball_iff w _ _ isOpen_ball isOpen_ball hR hS,
    real_exit_segment_contains_ball_iff v _ _ isOpen_ball isOpen_ball hvR hvS]
  exact ballExit_segment_contains_ball_normalize w z s hs R S r hR hS

end LatticeProb
