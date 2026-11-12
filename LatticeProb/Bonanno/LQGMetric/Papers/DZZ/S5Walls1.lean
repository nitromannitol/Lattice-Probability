/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Walls1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls0

/-!
# The endpoints `u, v` lie in `𝕍̃_{u,v}^ξ` for `2ξ ≤ |u − v|` (P-317K-ADAPT)

DEC-123 §2: the tilde-box consumers of the walled DZZ Proposition 3.17 (DZZ arXiv:1807.00422,
Remark 5.2, l. 2281–2284) use it at the pair `({u}, {v})`, which lies in `kXi (tildeBox u v) ξ`
when `ξ ≤ |u − v|/2` (`u` and `v` are at distance `|u − v|/2` from `∂𝕍̃_{u,v}`).
Own elementary proof (the ball `B(u, |u−v|/2)` lies in `B((u+v)/2, |u−v|) ⊆ 𝕍̃_{u,v}`,
`ball_mid_subset_tildeBox`, S5Geom).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

lemma compl_tildeBox_nonempty {u v : ℂ} (huv : u ≠ v) : (tildeBox u v)ᶜ.Nonempty := by
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
  refine ⟨(u + v) / 2 + 2 * (v - u), fun h => ?_⟩
  have h1 := h.1
  have he : ((u + v) / 2 + 2 * (v - u) - (u + v) / 2) * starRingEnd ℂ (v - u) =
      ((2 * ‖v - u‖ ^ 2 : ℝ) : ℂ) := by
    rw [add_sub_cancel_left, mul_assoc, Complex.mul_conj']
    push_cast; ring
  rw [he, Complex.ofReal_re, abs_of_pos (by positivity)] at h1
  nlinarith

lemma mem_kXi_tildeBox_left {u v : ℂ} (huv : u ≠ v) {ξ : ℝ} (hξ : 2 * ξ ≤ dist u v) :
    u ∈ kXi (tildeBox u v) ξ := by
  have hb : Metric.ball u (‖v - u‖ / 2) ⊆ tildeBox u v := by
    refine Subset.trans (fun z hz => ?_) (ball_mid_subset_tildeBox u v)
    rw [Metric.mem_ball] at hz ⊢
    have hum : dist u ((u + v) / 2) = ‖v - u‖ / 2 := by
      rw [dist_eq_norm, show u - (u + v) / 2 = -((v - u) / 2) by ring, norm_neg, norm_div]
      simp
    linarith [dist_triangle z u ((u + v) / 2)]
  have h := mem_kXi_of_ball_subset (compl_tildeBox_nonempty huv) hb
  have hd : dist u v = ‖v - u‖ := by rw [dist_eq_norm, norm_sub_rev]
  exact le_trans (show ξ ≤ ‖v - u‖ / 2 by linarith) h

lemma mem_kXi_tildeBox_right {u v : ℂ} (huv : u ≠ v) {ξ : ℝ} (hξ : 2 * ξ ≤ dist u v) :
    v ∈ kXi (tildeBox u v) ξ := by
  have hb : Metric.ball v (‖v - u‖ / 2) ⊆ tildeBox u v := by
    refine Subset.trans (fun z hz => ?_) (ball_mid_subset_tildeBox u v)
    rw [Metric.mem_ball] at hz ⊢
    have hvm : dist v ((u + v) / 2) = ‖v - u‖ / 2 := by
      rw [dist_eq_norm, show v - (u + v) / 2 = (v - u) / 2 by ring, norm_div]
      simp
    linarith [dist_triangle z v ((u + v) / 2)]
  have h := mem_kXi_of_ball_subset (compl_tildeBox_nonempty huv) hb
  have hd : dist u v = ‖v - u‖ := by rw [dist_eq_norm, norm_sub_rev]
  exact le_trans (show ξ ≤ ‖v - u‖ / 2 by linarith) h

end DZZ
end LQGMetric
