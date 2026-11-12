/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P2

/-!
# DZZ Lemma 5.3, node 3: sides of dyadic boxes

Geometric inputs of `l53_cell_desirable_prob` (S5L53J6) for the dyadic sub-boxes of a cell
(DZZ l. 2425: "partition `𝖢_i` into `K²` many dyadic squares with side length `s_i/K`"):
* `l53J_vline_eq`, `l53J_hline_eq`: `μH¹` of an axis-parallel segment is its length (the
  computation of `l53_vline_ne_top`, S5L53F3, carried to the value);
* `l53_frontier_closedBox_le`: `μH¹(∂𝖡̄) ≤ 4 s_𝖡` (the frontier lies on the four sides,
  `Complex.frontier_reProdIm`);
* `l53_adj_iface`: for `4`-adjacent boxes of one level (indices as in `PercAdj4`), the common
  side `𝖡̄ ∩ 𝖡̄'` lies on both frontiers and has `μH¹ ≥ s_𝖡` (interfaces `I x y` with `c = s_𝖡`);
* `l53_frontier_closedBox_ge`: `μH¹(∂𝖡̄) ≥ s_𝖡`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

/-- `μH¹` of a vertical segment. -/
lemma l53J_vline_eq (a b c : ℝ) :
    μH[1] {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} = ENNReal.ofReal (c - b) := by
  have : {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} = (fun t : ℝ => (⟨a, t⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.im, ⟨h2, h3⟩, Complex.ext (by simp [h1]) (by simp)⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_vline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]

/-- `μH¹` of a horizontal segment. -/
lemma l53J_hline_eq (a b c : ℝ) :
    μH[1] {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} = ENNReal.ofReal (c - b) := by
  have : {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} = (fun t : ℝ => (⟨t, a⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.re, ⟨h2, h3⟩, Complex.ext (by simp) (by simp [h1])⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_hline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]

/-- **`μH¹(∂𝖡̄) ≤ 4 s_𝖡`.** -/
lemma l53_frontier_closedBox_le (b : DyBox) :
    μH[1] (frontier b.closedBox) ≤ 4 * ENNReal.ofReal b.side := by
  have s0 := side_pos' b
  have hj : (b.j : ℝ) * b.side ≤ (b.j + 1) * b.side := by nlinarith
  have hk : (b.k : ℝ) * b.side ≤ (b.k + 1) * b.side := by nlinarith
  set x₀ : ℝ := b.j * b.side
  set y₀ : ℝ := b.k * b.side
  have hsub : frontier b.closedBox ⊆
      ({z : ℂ | z.re = x₀ ∧ y₀ ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side} ∪
        {z : ℂ | z.re = (b.j + 1) * b.side ∧ y₀ ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side}) ∪
      ({z : ℂ | z.im = y₀ ∧ x₀ ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side} ∪
        {z : ℂ | z.im = (b.k + 1) * b.side ∧ x₀ ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side}) := by
    rw [closedBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
      frontier_Icc hj, frontier_Icc hk]
    rintro z (hz | hz) <;> rw [Complex.mem_reProdIm] at hz
    · obtain ⟨⟨h1, h2⟩, h3⟩ := hz
      rcases h3 with h3 | h3
      · exact Or.inr (Or.inl ⟨h3, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨h3, h1, h2⟩)
    · obtain ⟨h1, ⟨h2, h3⟩⟩ := hz
      rcases h1 with h1 | h1
      · exact Or.inl (Or.inl ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inr ⟨h1, h2, h3⟩)
  have e1 : (b.k + 1) * b.side - y₀ = b.side := by ring
  have e2 : (b.j + 1) * b.side - x₀ = b.side := by ring
  calc μH[1] (frontier b.closedBox) ≤ (ENNReal.ofReal b.side + ENNReal.ofReal b.side) +
        (ENNReal.ofReal b.side + ENNReal.ofReal b.side) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
        gcongr <;> refine (measure_union_le _ _).trans (le_of_eq ?_) <;>
          simp only [l53J_vline_eq, l53J_hline_eq, e1, e2]
    _ = 4 * ENNReal.ofReal b.side := by ring

/-- The common side of a box and the box just below it. -/
lemma l53_adj_iface_k {b b' : DyBox} (hn : b.n = b'.n) (hj : b.j = b'.j) (hk : b.k = b'.k + 1) :
    b.closedBox ∩ b'.closedBox ⊆ frontier b.closedBox ∩ frontier b'.closedBox ∧
      ENNReal.ofReal b.side ≤ μH[1] (b.closedBox ∩ b'.closedBox) := by
  have hs : b'.side = b.side := by simp only [DyBox.side, hn]
  have s0 := side_pos' b
  have hJ : (b'.j : ℝ) * b.side = b.j * b.side := by rw [hj]
  have hK : ((b'.k : ℝ) + 1) * b.side = b.k * b.side := by rw [hk]; push_cast; ring
  constructor
  · intro z ⟨hz, hz'⟩
    have hz1 := hz; have hz1' := hz'
    obtain ⟨a1, a2, a3, a4⟩ := hz
    obtain ⟨c1, c2, c3, c4⟩ := hz'
    rw [hs] at c1 c2 c3 c4
    have e : z.im = b.k * b.side := by linarith
    exact ⟨mem_frontier_closedBox hz1 (Or.inr (Or.inr (Or.inl e))),
      mem_frontier_closedBox hz1' (Or.inr (Or.inr (Or.inr (by rw [hs]; linarith))))⟩
  · refine le_trans (le_of_eq ?_) (measure_mono (s := {z : ℂ | z.im = b.k * b.side ∧
      b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side}) ?_)
    · rw [l53J_hline_eq]; ring_nf
    · rintro z ⟨h1, h2, h3⟩
      have hJ1 : ((b'.j : ℝ) + 1) * b.side = (b.j + 1) * b.side := by rw [hj]
      refine ⟨⟨h2, h3, by rw [h1], by rw [h1]; nlinarith⟩, ?_, ?_, ?_, ?_⟩ <;> rw [hs]
      · linarith
      · linarith
      · rw [h1]; nlinarith
      · rw [h1]; linarith

/-- The common side of a box and the box just to its left. -/
lemma l53_adj_iface_j {b b' : DyBox} (hn : b.n = b'.n) (hk : b.k = b'.k) (hj : b.j = b'.j + 1) :
    b.closedBox ∩ b'.closedBox ⊆ frontier b.closedBox ∩ frontier b'.closedBox ∧
      ENNReal.ofReal b.side ≤ μH[1] (b.closedBox ∩ b'.closedBox) := by
  have hs : b'.side = b.side := by simp only [DyBox.side, hn]
  have s0 := side_pos' b
  have hK : (b'.k : ℝ) * b.side = b.k * b.side := by rw [hk]
  have hJ : ((b'.j : ℝ) + 1) * b.side = b.j * b.side := by rw [hj]; push_cast; ring
  constructor
  · intro z ⟨hz, hz'⟩
    have hz1 := hz; have hz1' := hz'
    obtain ⟨a1, a2, a3, a4⟩ := hz
    obtain ⟨c1, c2, c3, c4⟩ := hz'
    rw [hs] at c1 c2 c3 c4
    have e : z.re = b.j * b.side := by linarith
    exact ⟨mem_frontier_closedBox hz1 (Or.inl e),
      mem_frontier_closedBox hz1' (Or.inr (Or.inl (by rw [hs]; linarith)))⟩
  · refine le_trans (le_of_eq ?_) (measure_mono (s := {z : ℂ | z.re = b.j * b.side ∧
      b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side}) ?_)
    · rw [l53J_vline_eq]; ring_nf
    · rintro z ⟨h1, h2, h3⟩
      have hK1 : ((b'.k : ℝ) + 1) * b.side = (b.k + 1) * b.side := by rw [hk]
      refine ⟨⟨by rw [h1], by rw [h1]; nlinarith, h2, h3⟩, ?_, ?_, ?_, ?_⟩ <;> rw [hs]
      · rw [h1]; nlinarith
      · rw [h1]; linarith
      · linarith
      · linarith

/-- **Common sides of adjacent boxes.** For two boxes of one level whose indices are
`4`-adjacent, `𝖡̄ ∩ 𝖡̄'` lies on both frontiers and has `μH¹ ≥ s_𝖡`. -/
lemma l53_adj_iface {b b' : DyBox} (hn : b.n = b'.n)
    (hadj : (b.j = b'.j ∧ (b.k = b'.k + 1 ∨ b'.k = b.k + 1)) ∨
      (b.k = b'.k ∧ (b.j = b'.j + 1 ∨ b'.j = b.j + 1))) :
    b.closedBox ∩ b'.closedBox ⊆ frontier b.closedBox ∩ frontier b'.closedBox ∧
      ENNReal.ofReal b.side ≤ μH[1] (b.closedBox ∩ b'.closedBox) := by
  have hs : b'.side = b.side := by simp only [DyBox.side, hn]
  rcases hadj with ⟨hj, hk | hk⟩ | ⟨hk, hj | hj⟩
  · exact l53_adj_iface_k hn hj hk
  · have h := l53_adj_iface_k hn.symm hj.symm hk
    rw [inter_comm, inter_comm (frontier _), hs] at h
    exact h
  · exact l53_adj_iface_j hn hk hj
  · have h := l53_adj_iface_j hn.symm hk.symm hj
    rw [inter_comm, inter_comm (frontier _), hs] at h
    exact h

/-- **`μH¹(∂𝖡̄) ≥ s_𝖡`** (the bottom side lies on the frontier). -/
lemma l53_frontier_closedBox_ge (b : DyBox) :
    ENNReal.ofReal b.side ≤ μH[1] (frontier b.closedBox) := by
  have s0 := side_pos' b
  refine le_trans (le_of_eq ?_) (measure_mono (s := {z : ℂ | z.im = b.k * b.side ∧
    b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side}) ?_)
  · rw [l53J_hline_eq]; ring_nf
  · rintro z ⟨h1, h2, h3⟩
    exact mem_frontier_closedBox ⟨h2, h3, by rw [h1], by rw [h1]; nlinarith⟩
      (Or.inr (Or.inr (Or.inl h1)))

end LQGMetric.DZZ
