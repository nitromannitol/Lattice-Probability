import LatticeProb.Prob.NormalizedExitTransform

/-! # Ball containment in normalized exit segments -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive normalization takes each ball to a ball of the corresponding radius. -/
theorem ballNormalize_preimage_ball_center (z y : E) (s : ℝ≥0) (hs : 0 < s) (r : ℝ) :
    ballNormalize z s hs ⁻¹' ball (ballNormalize z s hs y) r =
      ball y ((s : ℝ) * r) := by
  ext x
  simp only [Set.mem_preimage, mem_ball, ballNormalize_apply, dist_eq_norm,
    ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (show (0 : ℝ) < s by exact_mod_cast hs)]
  rw [inv_mul_lt_iff₀ (show (0 : ℝ) < s by exact_mod_cast hs)]

/-- A set contains a ball precisely when its normalized image contains the
correspondingly scaled ball. -/
theorem exists_ball_subset_ballNormalize_image (z : E) (s : ℝ≥0) (hs : 0 < s)
    (r : ℝ) (T : Set E) :
    (∃ y, ball y ((s : ℝ) * r) ⊆ T) ↔
      ∃ y, ball y r ⊆ ballNormalize z s hs '' T := by
  let e := ballNormalize z s hs
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply hy
    rw [← ballNormalize_preimage_ball_center z y s hs r]
    change e (e.symm x) ∈ ball (e y) r
    simpa only [e.apply_symm_apply] using hx
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    intro x hx
    have hx' : e x ∈ ball y r := by
      have := hx
      rw [← ballNormalize_preimage_ball_center z (e.symm y) s hs r] at this
      change e x ∈ ball (e (e.symm y)) r at this
      simpa only [e.apply_symm_apply] using this
    obtain ⟨a, ha, hea⟩ := hy hx'
    exact e.injective hea ▸ ha

/-- The ball-in-segment event is invariant under normalization, with its
radius scaled by the spatial normalization factor. -/
theorem ballExit_segment_contains_ball_normalize
    (w : C(ℝ≥0, E)) (z : E) (s : ℝ≥0) (hs : 0 < s) (R S r : ℝ)
    (hR : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hS : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * S)) () ≠ ⊤) :
    (∃ y, ball y ((s : ℝ) * r) ⊆ w '' Icc
      (openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * S)) ()).toNNReal) ↔
    (∃ y, ball y r ⊆ (fun t => ballNormalize z s hs (w (areaTimeScale s hs t))) '' Icc
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w (areaTimeScale s hs t)))
        (ball 0 R) ()).toNNReal
      (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w (areaTimeScale s hs t)))
        (ball 0 S) ()).toNNReal) := by
  rw [ballExit_segment_ballNormalize_areaTimeScale w z s hs R S hR hS]
  exact exists_ball_subset_ballNormalize_image z s hs r _

end LatticeProb
