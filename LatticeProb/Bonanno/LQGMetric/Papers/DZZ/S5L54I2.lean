/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54I2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54I1

/-!
# D117 P-54T (2): a boundary segment lies on one side, and its image under `θ_j` (P2-DZZ54C)

Own elementary geometry (DZZ use it implicitly, l. 2555 "we assume without loss (by symmetry)").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma three_pts {a s m t : ℝ} (hs : |s - a| = 1 / 20 / 2) (hm : |m - a| = 1 / 20 / 2)
    (ht : |t - a| = 1 / 20 / 2) (h1 : s < m) (h2 : m < t) : False := by
  rcases (abs_eq (by norm_num)).1 hs with hs | hs <;>
  rcases (abs_eq (by norm_num)).1 hm with hm | hm <;>
  rcases (abs_eq (by norm_num)).1 ht with ht | ht <;> linarith

/-- **a boundary segment of positive length lies on one side `j`; its leg wall is `legSq u λ j`
and `θ_j(L)` lies in a vertical segment of the configuration of the same length** -/
theorem seg_side {u : ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) {L : Set ℂ} (h : IsBdrySeg u (1 / 20) ℓ L) :
    ∃ j : Fin 4, legWall u (1 / 20) L = legSq u (1 / 20) j ∧ L ⊆ sqSide u (1 / 20) j ∧
      ∃ s' t' : ℝ, 19 / 40 ≤ s' ∧ t' ≤ 21 / 40 ∧ ℓ / 2 ≤ t' - s' ∧ t' - s' ≤ ℓ ∧
        thJ u j '' L ⊆ vSeg s' t' := by
  obtain ⟨hLf, s, t, y, hform, h1, h2⟩ := h
  have hst : s < t := by linarith
  have hbox : L ⊆ sqBox u (1 / 20) := hLf.trans (isClosed_sqBox _ _).frontier_subset
  have hedge : ∀ z ∈ L, |z.re - u.re| = 1 / 20 / 2 ∨ |z.im - u.im| = 1 / 20 / 2 :=
    fun z hz => edge_of_mem_frontier_sqBox' (by norm_num) (hLf hz)
  rcases hform with rfl | rfl
  · -- horizontal
    have ps : (⟨s, y⟩ : ℂ) ∈ Icc s t ×ℂ {y} := Complex.mem_reProdIm.2 ⟨⟨le_rfl, hst.le⟩, rfl⟩
    have pt : (⟨t, y⟩ : ℂ) ∈ Icc s t ×ℂ {y} := Complex.mem_reProdIm.2 ⟨⟨hst.le, le_rfl⟩, rfl⟩
    have pm : (⟨(s + t) / 2, y⟩ : ℂ) ∈ Icc s t ×ℂ {y} :=
      Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, rfl⟩
    have hne : (⟨s, y⟩ : ℂ) ≠ ⟨t, y⟩ := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    obtain ⟨bs, -⟩ := hbox ps
    obtain ⟨bt, -⟩ := hbox pt
    simp only at bs bt
    rw [abs_le] at bs bt
    by_cases hy : |y - u.im| = 1 / 20 / 2
    · rcases (abs_eq (by norm_num)).1 hy with hy' | hy'
      · -- top side, `j = 2`
        have hside : Icc s t ×ℂ {y} ⊆ sqSide u (1 / 20) 2 := by
          intro z hz
          obtain ⟨⟨hz1, hz2⟩, hz3⟩ := Complex.mem_reProdIm.1 hz
          simp only [sqSide, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
          refine Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ?_⟩
          rw [mem_singleton_iff] at hz3 ⊢; linarith
        refine ⟨2, legWall_eq_legSq (by norm_num) hside ps pt hne, hside, 1 / 2 + u.re - t,
          1 / 2 + u.re - s, by linarith, by linarith, by linarith, by linarith, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨⟨hz1, hz2⟩, hz3⟩ := Complex.mem_reProdIm.1 hz
        rw [mem_singleton_iff] at hz3
        refine mem_vSeg.2 ⟨?_, ?_, ?_⟩ <;>
          simp [thJ, aJ, legC, legDir, c₅₄] <;> linarith
      · -- bottom side, `j = 0`
        have hside : Icc s t ×ℂ {y} ⊆ sqSide u (1 / 20) 0 := by
          intro z hz
          obtain ⟨⟨hz1, hz2⟩, hz3⟩ := Complex.mem_reProdIm.1 hz
          simp only [sqSide, Matrix.cons_val_zero]
          refine Complex.mem_reProdIm.2 ⟨⟨by linarith, by linarith⟩, ?_⟩
          rw [mem_singleton_iff] at hz3 ⊢; linarith
        refine ⟨0, legWall_eq_legSq (by norm_num) hside ps pt hne, hside, 1 / 2 + s - u.re,
          1 / 2 + t - u.re, by linarith, by linarith, by linarith, by linarith, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨⟨hz1, hz2⟩, hz3⟩ := Complex.mem_reProdIm.1 hz
        rw [mem_singleton_iff] at hz3
        refine mem_vSeg.2 ⟨?_, ?_, ?_⟩ <;>
          simp [thJ, aJ, legC, legDir, c₅₄] <;> linarith
    · exfalso
      have es := (hedge _ ps).resolve_right (by simpa using hy)
      have et := (hedge _ pt).resolve_right (by simpa using hy)
      have em := (hedge _ pm).resolve_right (by simpa using hy)
      exact three_pts es em et (by linarith) (by linarith)
  · -- vertical
    have ps : (⟨y, s⟩ : ℂ) ∈ {y} ×ℂ Icc s t := Complex.mem_reProdIm.2 ⟨rfl, ⟨le_rfl, hst.le⟩⟩
    have pt : (⟨y, t⟩ : ℂ) ∈ {y} ×ℂ Icc s t := Complex.mem_reProdIm.2 ⟨rfl, ⟨hst.le, le_rfl⟩⟩
    have pm : (⟨y, (s + t) / 2⟩ : ℂ) ∈ {y} ×ℂ Icc s t :=
      Complex.mem_reProdIm.2 ⟨rfl, ⟨by linarith, by linarith⟩⟩
    have hne : (⟨y, s⟩ : ℂ) ≠ ⟨y, t⟩ := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    obtain ⟨-, bs⟩ := hbox ps
    obtain ⟨-, bt⟩ := hbox pt
    simp only at bs bt
    rw [abs_le] at bs bt
    by_cases hy : |y - u.re| = 1 / 20 / 2
    · rcases (abs_eq (by norm_num)).1 hy with hy' | hy'
      · -- right side, `j = 3`
        have hside : {y} ×ℂ Icc s t ⊆ sqSide u (1 / 20) 3 := by
          intro z hz
          obtain ⟨hz3, ⟨hz1, hz2⟩⟩ := Complex.mem_reProdIm.1 hz
          simp only [sqSide, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
          refine Complex.mem_reProdIm.2 ⟨?_, ⟨by linarith, by linarith⟩⟩
          rw [mem_singleton_iff] at hz3 ⊢; linarith
        refine ⟨3, legWall_eq_legSq (by norm_num) hside ps pt hne, hside, 1 / 2 + s - u.im,
          1 / 2 + t - u.im, by linarith, by linarith, by linarith, by linarith, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨hz3, ⟨hz1, hz2⟩⟩ := Complex.mem_reProdIm.1 hz
        rw [mem_singleton_iff] at hz3
        refine mem_vSeg.2 ⟨?_, ?_, ?_⟩ <;>
          simp [thJ, aJ, legC, legDir, c₅₄] <;> linarith
      · -- left side, `j = 1`
        have hside : {y} ×ℂ Icc s t ⊆ sqSide u (1 / 20) 1 := by
          intro z hz
          obtain ⟨hz3, ⟨hz1, hz2⟩⟩ := Complex.mem_reProdIm.1 hz
          simp only [sqSide, Matrix.cons_val_one, Matrix.head_cons]
          refine Complex.mem_reProdIm.2 ⟨?_, ⟨by linarith, by linarith⟩⟩
          rw [mem_singleton_iff] at hz3 ⊢; linarith
        refine ⟨1, legWall_eq_legSq (by norm_num) hside ps pt hne, hside, 1 / 2 + u.im - t,
          1 / 2 + u.im - s, by linarith, by linarith, by linarith, by linarith, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨hz3, ⟨hz1, hz2⟩⟩ := Complex.mem_reProdIm.1 hz
        rw [mem_singleton_iff] at hz3
        refine mem_vSeg.2 ⟨?_, ?_, ?_⟩ <;>
          simp [thJ, aJ, legC, legDir, c₅₄] <;> linarith
    · exfalso
      have es := (hedge _ ps).resolve_left (by simpa using hy)
      have et := (hedge _ pt).resolve_left (by simpa using hy)
      have em := (hedge _ pm).resolve_left (by simpa using hy)
      exact three_pts es em et (by linarith) (by linarith)

end DZZ
end LQGMetric
