import LatticeProb.Prob.CombinedExitTransform
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Normalization of ball-exit observations -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation by the center followed by positive inverse dilation. -/
noncomputable def ballNormalize (z : E) (s : ℝ≥0) (hs : 0 < s) : E ≃ₜ E :=
  (Homeomorph.addLeft (-z)).trans
    (Homeomorph.smulOfNeZero (s : ℝ)⁻¹ (inv_ne_zero (by exact_mod_cast hs.ne')))

@[simp] theorem ballNormalize_apply (z x : E) (s : ℝ≥0) (hs : 0 < s) :
    ballNormalize z s hs x = (s : ℝ)⁻¹ • (x - z) := by
  simp [ballNormalize, sub_eq_add_neg, add_comm]

/-- The inverse image of a centered ball under positive normalization. -/
theorem ballNormalize_preimage_ball (z : E) (s : ℝ≥0) (hs : 0 < s) (R : ℝ) :
    ballNormalize z s hs ⁻¹' ball 0 R = ball z ((s : ℝ) * R) := by
  ext x
  simp only [Set.mem_preimage, mem_ball, ballNormalize_apply, dist_eq_norm, sub_zero,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (show (0 : ℝ) < s by exact_mod_cast hs)]
  rw [inv_mul_lt_iff₀ (show (0 : ℝ) < s by exact_mod_cast hs)]

/-- The area-time change associated with a positive spatial dilation. -/
noncomputable def areaTimeScale (s : ℝ≥0) (hs : 0 < s) : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)

/-- A normalized path stopped at a ball exit is the normalized stopped path. -/
theorem stoppedPath_ballNormalize_areaTimeScale
    (w : C(ℝ≥0, E)) (z : E) (s : ℝ≥0) (hs : 0 < s) (R : ℝ)
    (hfin : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) () ≠ ⊤) :
    let e := ballNormalize z s hs
    let φ := areaTimeScale s hs
    let v := ((⟨e, e.continuous⟩ : C(E, E)).comp w).comp ⟨φ, φ.continuous⟩
    stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 R) ()) v =
      ((⟨e, e.continuous⟩ : C(E, E)).comp
        (stoppedPath (openExitTime (fun t (_ : Unit) => w t)
          (ball z ((s : ℝ) * R)) ()) w)).comp ⟨φ, φ.continuous⟩ := by
  have h := stoppedPath_openExit_comp_spatial_orderIso w
    (⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E))
    (areaTimeScale s hs) (ball 0 R) isOpen_ball
  have hfin' : openExitTime (fun t (_ : Unit) => w t)
      (ballNormalize z s hs ⁻¹' ball 0 R) () ≠ ⊤ := by
    simpa only [ballNormalize_preimage_ball] using hfin
  simpa only [ContinuousMap.coe_mk, ballNormalize_preimage_ball] using h hfin'

/-- Normalization maps the trace between two finite ball exits to the trace
between the corresponding normalized exits. -/
theorem ballExit_segment_ballNormalize_areaTimeScale
    (w : C(ℝ≥0, E)) (z : E) (s : ℝ≥0) (hs : 0 < s) (R S : ℝ)
    (hR : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) () ≠ ⊤)
    (hS : openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * S)) () ≠ ⊤) :
    let e := ballNormalize z s hs
    let φ := areaTimeScale s hs
    (fun t => e (w (φ t))) '' Icc
      (openExitTime (fun t (_ : Unit) => e (w (φ t))) (ball 0 R) ()).toNNReal
      (openExitTime (fun t (_ : Unit) => e (w (φ t))) (ball 0 S) ()).toNNReal =
      e '' (w '' Icc
        (openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * R)) ()).toNNReal
        (openExitTime (fun t (_ : Unit) => w t) (ball z ((s : ℝ) * S)) ()).toNNReal) := by
  have h := openExit_segment_comp_spatial_orderIso w
    (⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ : C(E, E))
    (areaTimeScale s hs) (ball 0 R) (ball 0 S) isOpen_ball isOpen_ball
  have hR' : openExitTime (fun t (_ : Unit) => w t)
      (ballNormalize z s hs ⁻¹' ball 0 R) () ≠ ⊤ := by
    simpa only [ballNormalize_preimage_ball] using hR
  have hS' : openExitTime (fun t (_ : Unit) => w t)
      (ballNormalize z s hs ⁻¹' ball 0 S) () ≠ ⊤ := by
    simpa only [ballNormalize_preimage_ball] using hS
  simpa only [ContinuousMap.coe_mk, ballNormalize_preimage_ball] using h hR' hS'

end LatticeProb
