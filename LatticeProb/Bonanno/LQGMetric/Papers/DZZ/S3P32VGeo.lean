/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32VGeo at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UClip
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UEnd

/-!
# DZZ P3.2 upper bound at the walled measure: geometry of the clipped boxes (D101, P-4a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2, upper bound
(l. 1088–1153, crossing of Lemma 3.5 l. 1054–1079), with the clipped rings of decision D101
(decisions/DEC-101.md §3): the covered curve of a ring box `B'` is `∂(B' ∩ 𝕍_{−r})`.

* `frontier_clip_eq`: for a box of side `> 2r`, `B ∩ 𝕍_{−r}` is the closed rectangle
  `[max a r, min a' (1−r)] × [max b r, min b' (1−r)]` and its boundary is the `rectBd` of it;
* `isPathConnected_frontier_clip`;
* `clampV_mem_frontier_clip`: the coordinatewise clamp `ℂ → 𝕍_{−r}` maps `∂B` into
  `∂(B ∩ 𝕍_{−r})`; hence meeting box boundaries give meeting clipped boundaries
  (`frontier_clip_meet`), and the chain of clipped boundaries of an enclosure is path-connected;
* `exists_cover_of_phiLeC`; `ball_endC` (the end argument `ball_end` with paths in `𝕍_{−r}`).

Own elementary arguments (DZZ do not clip; DV-D101).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma isClosed_dzzVIn (r : ℝ) : IsClosed (dzzVIn r) := by
  have h1 : IsClosed {z : ℂ | r ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ 1 - r} := isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | r ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ 1 - r} := isClosed_le Complex.continuous_im continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- The coordinates of a box of side `> r` are compatible with `𝕍_{−r}`. -/
lemma box_coord_clip (B : DyBox) {r : ℝ} (hr : 2 * r < B.side) :
    (B.j : ℝ) * B.side ≤ 1 - r ∧ r ≤ ((B.j : ℝ) + 1) * B.side ∧
      (B.k : ℝ) * B.side ≤ 1 - r ∧ r ≤ ((B.k : ℝ) + 1) * B.side ∧ r ≤ 1 - r := by
  have hs := side_pos' B
  have h1 : ((B.j : ℝ) + 1) * B.side ≤ 1 := by
    have : ((B.j + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hj
    push_cast at this
    have e : (2 : ℝ) ^ B.n * B.side = 1 := by
      unfold DyBox.side; rw [← mul_pow]; norm_num
    nlinarith
  have h2 : ((B.k : ℝ) + 1) * B.side ≤ 1 := by
    have : ((B.k + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hk
    push_cast at this
    have e : (2 : ℝ) ^ B.n * B.side = 1 := by
      unfold DyBox.side; rw [← mul_pow]; norm_num
    nlinarith
  have hj0 : (0 : ℝ) ≤ B.j := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ B.k := Nat.cast_nonneg _
  have hs1 : B.side ≤ 1 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by linarith⟩

end DZZ
end LQGMetric
