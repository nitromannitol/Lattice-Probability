/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214FinalArc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L214FinalReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14: one arc

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 862–877, statement (2.13): each boundary arc `I = φ(circArc θ ℓ)` with
`ℓ ≤ 1/10` is disconnected from `0` in `U` by a set of diameter `≤ 2R · dist(φ(w_I), ∂U)`,
`R` universal.

* `l214_arc_normalized`: arc centred at `i` (`u_I = i`). The two connected pieces `W⁻, W⁺` of
  `l214_reach` (from `l214_minorant` and its mirror `l214_minorant_plus`, C:863–867) both contain
  `w_I`; their union `W` reaches the caps of `J⁻` and `J⁺` (C:868), and `l214_pull` (R4, the
  separation C:869–870) shows that `Φ(closure W)` disconnects `Φ(I)` from `0` in `U`.
  `Φ(closure W) ⊆ closedBall (Φ w) (R d)` gives the diameter bound (CONF writes `4R d` for the
  concatenated path, C:868; the closed ball gives `2R d`).
* `l214_arc`: general arc, by the rotation `z ↦ e^{i(θ + ℓ/2 − π/2)} z` taking `i` to the
  arc centre `u_I`.
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex
open scoped Topology Real ComplexConjugate ENNReal

theorem l214_ediam_le_of_subset_closedBall {X : Set ℂ} {x : ℂ} {r : ℝ}
    (h : X ⊆ closedBall x r) : Metric.ediam X ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le fun y hy z hz => ?_
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := mem_closedBall.1 (h hy)
  have h2 := mem_closedBall.1 (h hz)
  linarith [dist_triangle_right y z x]

/-- Rotation of the disc: `e^{iα}` times `circArc β ℓ` is `circArc (β + α) ℓ`. -/
theorem l214_rot_circArc (α β ℓ : ℝ) :
    (fun z => exp ((α : ℂ) * I) * z) '' circArc β ℓ = circArc (β + α) ℓ := by
  rw [circArc, circArc, image_image]
  have e : (fun t : ℝ => exp ((α : ℂ) * I) * exp ((t : ℂ) * I)) =
      (fun t : ℝ => exp ((t : ℂ) * I)) ∘ (fun t => t + α) := by
    funext t; simp only [Function.comp_apply, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, image_comp, image_add_const_Icc]
  congr 2; ring

theorem l214_rot_ball {r : ℂ} (hr : ‖r‖ = 1) :
    (fun z => r * z) '' ball 0 1 = ball 0 1 := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff, norm_mul, hr, one_mul]; exact mem_ball_zero_iff.1 hy
  · intro hz
    refine ⟨r⁻¹ * z, ?_, by field_simp⟩
    rw [mem_ball_zero_iff, norm_mul, norm_inv, hr, inv_one, one_mul]; exact mem_ball_zero_iff.1 hz

end CONF
end LQGMetric
