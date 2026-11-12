/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D123 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54F3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317E

/-!
# D123: the leg walls of DZZ Lemma 5.4 as axis-parallel squares (decision DEC-123)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2553–2578, and
DEC-117 §2(a)(ii). The leg from `u` to a segment `L` on the `j`-th side of `∂𝕍_{u,λ}` is measured
with the wall `legWall u λ L = legSq u λ j = 𝕍_{u,2λ} ∩ 𝕍̃_{u, u + λ e_j}` (S5D117, D123), an
axis-parallel closed square of side `2λ`: the `D̄^{u,2λ}`-chains of DZZ that are also
`D̃(u, v)`-chains for the point `v = u + λ e_j` of the contradiction. This file:

* `lgdMinSet_dzzWall_anti`: a larger wall gives a smaller walled minimal LGD;
* `legWallC_subset_legWall`: DEC-117's stadium wall `𝕍_{u,λ} ∪ N_{λ/2}(L)` lies in the D123 wall
  (for `L ⊆ ∂𝕍_{u,λ}`), because the Euclidean `λ/2`-ball about a point of the `j`-th side lies in
  `legSq u λ j`, and about any point of `𝕍_{u,λ}` in `𝕍_{u,2λ}`;
* **`dzzLegTrunc_of_mem`**: the truncation `DZZLegTrunc u` (S5L54F1) for the D123 walls, from
  `dzzLegTruncC_of_mem` (S5L54F3) by monotonicity;
* `legWall_eq_or`, `legWalls`: `legWall u l L` is one of five squares of side `2l`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- A larger wall gives a smaller walled minimal LGD. -/
lemma lgdMinSet_dzzWall_anti {K K' : Set ℂ} (h : K ⊆ K') (ν : Measure ℂ) (δ : ℝ)
    (A B : Set ℂ) : lgdMinSet (dzzWall K' ν) δ A B ≤ lgdMinSet (dzzWall K ν) δ A B :=
  iInf₂_mono fun x _ => iInf₂_mono fun y _ => lgdDZZ_mono_measure (dzzWall_anti h ν) δ x y

lemma re_im_le_of_mem_closedBall {z w : ℂ} {r : ℝ} (hz : z ∈ closedBall w r) :
    |z.re - w.re| ≤ r ∧ |z.im - w.im| ≤ r := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  have e1 : |z.re - w.re| ≤ ‖z - w‖ := by simpa using Complex.abs_re_le_norm (z - w)
  have e2 : |z.im - w.im| ≤ ‖z - w‖ := by simpa using Complex.abs_im_le_norm (z - w)
  exact ⟨e1.trans hz, e2.trans hz⟩

/-- The closed Euclidean `r`-ball about a point of `𝕍_{c,l}` lies in `𝕍_{c,l+2r}`. -/
lemma closedBall_subset_sqBox_of_mem {c w : ℂ} {l r : ℝ} (hw : w ∈ sqBox c l) :
    closedBall w r ⊆ sqBox c (l + 2 * r) := by
  intro z hz
  obtain ⟨h1, h2⟩ := re_im_le_of_mem_closedBall hz
  obtain ⟨h3, h4⟩ := hw
  rw [abs_le] at h1 h2 h3 h4
  constructor <;> rw [abs_le] <;> constructor <;> linarith

lemma sqBox_subset_sqBox_two (u : ℂ) {l : ℝ} (hl : 0 ≤ l) : sqBox u l ⊆ sqBox u (2 * l) := by
  intro z ⟨h1, h2⟩
  exact ⟨by linarith, by linarith⟩

lemma isCompact_sqBox (c : ℂ) {l : ℝ} (hl : 0 ≤ l) : IsCompact (sqBox c l) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_sqBox c l)
    (Metric.isBounded_closedBall.subset (sqBox_subset_closedBall c hl))

lemma cthickening_sqBox_subset (u : ℂ) {l : ℝ} (hl : 0 ≤ l) :
    cthickening (l / 2) (sqBox u l) ⊆ sqBox u (2 * l) := by
  rw [(isCompact_sqBox u hl).cthickening_eq_biUnion_closedBall (by linarith)]
  refine iUnion₂_subset fun w hw => (closedBall_subset_sqBox_of_mem hw).trans ?_
  rw [show l + 2 * (l / 2) = 2 * l by ring]

lemma sqSide_subset_sqBox (u : ℂ) (l : ℝ) (j : Fin 4) : sqSide u l j ⊆ sqBox u l := by
  intro z hz
  fin_cases j <;> simp only [sqSide, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hz <;> rw [Complex.mem_reProdIm] at hz <;>
    simp only [mem_Icc, mem_singleton_iff] at hz <;>
    refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith [hz.1, hz.2]

lemma isCompact_sqSide (u : ℂ) (l : ℝ) (j : Fin 4) : IsCompact (sqSide u l j) := by
  fin_cases j <;> simp only [sqSide, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;>
  exact Metric.isCompact_of_isClosed_isBounded
    (IsClosed.reProdIm (by first | exact isClosed_Icc | exact isClosed_singleton)
      (by first | exact isClosed_Icc | exact isClosed_singleton))
    (Bornology.IsBounded.reProdIm (by first | exact Metric.isBounded_Icc _ _ | exact Bornology.isBounded_singleton)
      (by first | exact Metric.isBounded_Icc _ _ | exact Bornology.isBounded_singleton))

/-- The closed `l/2`-ball about a point of the `j`-th side of `∂𝕍_{u,l}` lies in `legSq u l j`. -/
lemma closedBall_subset_legSq {u w : ℂ} {l : ℝ} {j : Fin 4} (hw : w ∈ sqSide u l j) :
    closedBall w (l / 2) ⊆ legSq u l j := by
  intro z hz
  obtain ⟨h1, h2⟩ := re_im_le_of_mem_closedBall hz
  rw [abs_le] at h1 h2
  fin_cases j <;> simp only [sqSide, legSq, legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hw ⊢ <;> rw [Complex.mem_reProdIm] at hw <;>
    simp only [mem_Icc, mem_singleton_iff] at hw <;>
    simp only [sqBox, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im] <;>
    refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith [hw.1, hw.2]

lemma sqBox_subset_legSq (u : ℂ) {l : ℝ} (hl : 0 ≤ l) (j : Fin 4) : sqBox u l ⊆ legSq u l j := by
  intro z ⟨h1, h2⟩
  rw [abs_le] at h1 h2
  fin_cases j <;> simp only [legSq, legDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;>
    simp only [sqBox, mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im] <;>
    refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith

lemma cthickening_subset_legSq {u : ℂ} {l : ℝ} (hl : 0 ≤ l) {j : Fin 4} {L : Set ℂ}
    (hL : L ⊆ sqSide u l j) : cthickening (l / 2) L ⊆ legSq u l j := by
  refine (cthickening_subset_of_subset _ hL).trans ?_
  rw [(isCompact_sqSide u l j).cthickening_eq_biUnion_closedBall (by linarith)]
  exact iUnion₂_subset fun w hw => closedBall_subset_legSq hw

/-- `legWall u l L` is DZZ's `𝕍_{u,2l}`, or `legSq u l j` for a side `j` containing `L`. -/
lemma legWall_eq_or (u : ℂ) (l : ℝ) (L : Set ℂ) :
    legWall u l L = sqBox u (2 * l) ∨ ∃ j, L ⊆ sqSide u l j ∧ legWall u l L = legSq u l j := by
  unfold legWall
  split_ifs with h
  · exact Or.inr ⟨Classical.choose h, Classical.choose_spec h, rfl⟩
  · exact Or.inl rfl

lemma sqBox_subset_legWall (u : ℂ) {l : ℝ} (hl : 0 ≤ l) (L : Set ℂ) :
    sqBox u l ⊆ legWall u l L := by
  rcases legWall_eq_or u l L with h | ⟨j, -, h⟩ <;> rw [h]
  · exact sqBox_subset_sqBox_two u hl
  · exact sqBox_subset_legSq u hl j

/-- **DEC-117's stadium wall lies in the D123 wall** (for `L ⊆ ∂𝕍_{u,l}`). -/
theorem legWallC_subset_legWall (u : ℂ) {l : ℝ} (hl : 0 ≤ l) {L : Set ℂ}
    (hL : L ⊆ frontier (sqBox u l)) : legWallC u l L ⊆ legWall u l L := by
  refine union_subset (sqBox_subset_legWall u hl L) ?_
  rcases legWall_eq_or u l L with h | ⟨j, hj, h⟩ <;> rw [h]
  · exact (cthickening_subset_of_subset _ (hL.trans (isClosed_sqBox u l).frontier_subset)).trans
      (cthickening_sqBox_subset u hl)
  · exact cthickening_subset_legSq hl hj

/-- **Truncation lemma for the D123 leg walls** (DEC-117 §2(a)(ii), DEC-123): `DZZLegTrunc u`
for `u ∈ 𝕍̄`, from the stadium version `dzzLegTruncC_of_mem` (S5L54F3) by monotonicity. -/
theorem dzzLegTrunc_of_mem {u : ℂ} (hu : u ∈ dzzVbar) : DZZLegTrunc u := by
  intro ν δ hB I S hS hcov
  obtain ⟨i, hi⟩ := dzzLegTruncC_of_mem hu ν δ hB S hS hcov
  exact ⟨i, (lgdMinSet_dzzWall_anti (legWallC_subset_legWall u (by norm_num) (hS i)) ν δ _ _).trans
    hi⟩

/-- The five possible leg walls at `u` (`λ = 1/20`): `𝕍_{u,1/10}` and the four `legSq u (1/20) j`.
All are axis-parallel closed squares of side `1/10`. -/
def legWalls (u : ℂ) : Set (Set ℂ) := insert (sqBox u (1 / 10)) (range (legSq u (1 / 20)))

lemma legWall_mem_legWalls (u : ℂ) (L : Set ℂ) : legWall u (1 / 20) L ∈ legWalls u := by
  rcases legWall_eq_or u (1 / 20) L with h | ⟨j, -, h⟩ <;> rw [h]
  · exact Or.inl (by norm_num)
  · exact Or.inr ⟨j, rfl⟩

end DZZ
end LQGMetric
