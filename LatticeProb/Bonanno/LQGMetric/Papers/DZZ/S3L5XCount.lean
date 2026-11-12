/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XConn

/-!
# DZZ Lemma 3.5: the cells of a ring (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1069–1070: "`|ℂ_i| ≤ λ/ε²`"): the
`δ'`-cells of the boundary squares of an enclosure box `B'` are counted by `Ψ_{B',δ'}`
(Def 3.6: cells contained in `B'` touching `∂B'`, or the cell containing `B'`).

* `mem_frontier_of_edge`: points of `B` on an edge lie on `∂B`.
* `bdrySq_meets_frontier`: a boundary square of `B` meets `∂B`.
* **`bdry_cell_mem`**: the cell of a boundary square of `B` is the cell containing `B`, or a cell
  inside `B` touching `∂B` (and then no cell contains `B`).

Own elementary arguments; DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma mem_frontier_of_edge {B : DyBox} {z : ℂ} (hz : z ∈ B.closedBox)
    (he : z.re = B.j * B.side ∨ z.re = (B.j + 1) * B.side ∨ z.im = B.k * B.side ∨
      z.im = (B.k + 1) * B.side) : z ∈ frontier B.closedBox := by
  refine ⟨subset_closure hz, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hε2 : 0 < ε / 2 := by positivity
  have nr : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε2]
  have ni : ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ = ε / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, nr]
  have lt : ε / 2 < ε := by linarith
  rcases he with h | h | h | h
  · have hw : z - ((ε / 2 : ℝ) : ℂ) ∈ B.closedBox :=
      hball (by rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, nr]; exact lt)
    have := hw.1; simp only [Complex.sub_re, Complex.ofReal_re] at this; linarith
  · have hw : z + ((ε / 2 : ℝ) : ℂ) ∈ B.closedBox :=
      hball (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, nr]; exact lt)
    have := hw.2.1; simp only [Complex.add_re, Complex.ofReal_re] at this; linarith
  · have hw : z - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ B.closedBox :=
      hball (by rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, ni]; exact lt)
    have := hw.2.2.1
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at this
    linarith
  · have hw : z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ B.closedBox :=
      hball (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ni]; exact lt)
    have := hw.2.2.2
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero] at this
    linarith

lemma side_mul_rel {s B : DyBox} {N : ℕ} (hs : s.n = N) (hB : B.n ≤ N) :
    s.side * ((2 ^ (N - B.n) : ℕ) : ℝ) = B.side := by
  have e1 := bx_side_mul (b := s) (N := N) hs.le
  have e2 := bx_side_mul (b := B) (N := N) hB
  rw [hs, Nat.sub_self, pow_zero] at e1
  have hp : (2 : ℝ) ^ N ≠ 0 := by positivity
  push_cast
  apply mul_right_cancel₀ hp
  rw [e2, mul_comm s.side, mul_assoc, e1, mul_one]

/-- A boundary square of `B` meets `∂B`. -/
lemma bdrySq_meets_frontier {s B : DyBox} {N : ℕ} (hB : B.n ≤ N) (h : IsBdrySq N B s) :
    (s.closedBox ∩ frontier B.closedBox).Nonempty := by
  obtain ⟨hsn, hsB, hc⟩ := h
  have e := side_mul_rel hsn hB
  have hs0 : 0 < s.side := by unfold DyBox.side; positivity
  have lo : (⟨s.j * s.side, s.k * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> nlinarith
  have hi : (⟨(s.j + 1) * s.side, (s.k + 1) * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> nlinarith
  rcases hc with h | h | h | h
  · refine ⟨_, lo, mem_frontier_of_edge (hsB lo) (Or.inl ?_)⟩
    show (s.j : ℝ) * s.side = B.j * B.side
    rw [← e, h]; push_cast; ring
  · refine ⟨_, hi, mem_frontier_of_edge (hsB hi) (Or.inr (Or.inl ?_))⟩
    show ((s.j : ℝ) + 1) * s.side = (B.j + 1) * B.side
    rw [← e]
    have : ((s.j : ℝ) + 1) = (((B.j + 1) * 2 ^ (N - B.n) : ℕ) : ℝ) := by exact_mod_cast h
    rw [this]; push_cast; ring
  · refine ⟨_, lo, mem_frontier_of_edge (hsB lo) (Or.inr (Or.inr (Or.inl ?_)))⟩
    show (s.k : ℝ) * s.side = B.k * B.side
    rw [← e, h]; push_cast; ring
  · refine ⟨_, hi, mem_frontier_of_edge (hsB hi) (Or.inr (Or.inr (Or.inr ?_)))⟩
    show ((s.k : ℝ) + 1) * s.side = (B.k + 1) * B.side
    rw [← e]
    have : ((s.k : ℝ) + 1) = (((B.k + 1) * 2 ^ (N - B.n) : ℕ) : ℝ) := by exact_mod_cast h
    rw [this]; push_cast; ring

lemma n_le_of_sub {B c : DyBox} (h : B.closedBox ⊆ c.closedBox) : c.n ≤ B.n := by
  have hs0 : 0 < B.side := by unfold DyBox.side; positivity
  have lo : (⟨B.j * B.side, B.k * B.side⟩ : ℂ) ∈ B.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> nlinarith
  have hi : (⟨(B.j + 1) * B.side, (B.k + 1) * B.side⟩ : ℂ) ∈ B.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> nlinarith
  obtain ⟨a1, -, -, -⟩ := h lo
  obtain ⟨-, b2, -, -⟩ := h hi
  simp only at a1 b2
  have hside : B.side ≤ c.side := by nlinarith
  by_contra hlt
  have : c.side < B.side := by
    unfold DyBox.side
    exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-- **The cell of a boundary square of `B`** is the cell containing `B`, or (when no cell contains
`B`) a cell inside `B` touching `∂B`: the cells counted by `Ψ_{B,δ}`. -/
theorem bdry_cell_mem {B s T : DyBox} {N : ℕ} (hB : B.n ≤ N) (hs : IsBdrySq N B s)
    (hT : IsSqCell m δ s T) :
    (IsCell m δ T ∧ B.closedBox ⊆ T.closedBox) ∨
      ((¬ ∃ c, IsCell m δ c ∧ B.closedBox ⊆ c.closedBox) ∧
        T ∈ {c | IsCell m δ c ∧ c.closedBox ⊆ B.closedBox ∧
          (c.closedBox ∩ frontier B.closedBox).Nonempty}) := by
  have hsn := hs.1
  have hsB : s.anc B.n = B := anc_eq_of_sub hsn hB hs.2.1
  rcases le_total T.n B.n with hle | hle
  · left
    refine ⟨hT.1, ?_⟩
    have : B.anc T.n = T := by rw [← hsB, anc_anc s hle, hT.2.2]
    rw [← this]; exact closedBox_sub_anc B _
  · have hTB : T.anc B.n = B := by rw [← hT.2.2, anc_anc s hle, hsB]
    have hsub : T.closedBox ⊆ B.closedBox := by rw [← hTB]; exact closedBox_sub_anc T _
    by_cases hc : ∃ c, IsCell m δ c ∧ B.closedBox ⊆ c.closedBox
    · left
      obtain ⟨c, hc1, hc2⟩ := hc
      have hcn : c.n ≤ N := (n_le_of_sub hc2).trans hB
      have hcT : c = T := isSqCell_unique ⟨hc1, (by omega : c.n ≤ s.n),
        anc_eq_of_sub hsn hcn (hs.2.1.trans hc2)⟩ hT
      subst hcT
      exact ⟨hT.1, hc2⟩
    · right
      exact ⟨hc, hT.1, hsub, (bdrySq_meets_frontier hB hs).mono
        (inter_subset_inter_left _ hT.sub)⟩

/-- The cells of the boundary squares of a box `B` with `Ψ_{B,δ} ≤ λ` form a finite set of size
`≤ λ`. -/
theorem bdry_cells_finset {B : DyBox} {N : ℕ} {lam : ℝ} (hB : B.n ≤ N) (hpsi : PsiLe m δ B lam) :
    ∃ S : Finset DyBox, (S.card : ℝ) ≤ lam ∧
      ∀ s, IsBdrySq N B s → ∀ T, IsSqCell m δ s T → T ∈ S := by
  classical
  obtain ⟨K, hK, hKl⟩ := hpsi
  unfold cellPsi at hK
  by_cases hc : ∃ c, IsCell m δ c ∧ B.closedBox ⊆ c.closedBox
  · rw [if_pos hc] at hK
    have hK1 : K = 1 := by exact_mod_cast hK.symm
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨{c}, by rw [Finset.card_singleton]; rw [hK1] at hKl; exact_mod_cast hKl,
      fun s hs T hT => ?_⟩
    rw [Finset.mem_singleton]
    exact isSqCell_unique hT ⟨hc1, by rw [hs.1]; exact (n_le_of_sub hc2).trans hB,
      anc_eq_of_sub hs.1 ((n_le_of_sub hc2).trans hB) (hs.2.1.trans hc2)⟩
  · rw [if_neg hc] at hK
    set Z := {c | IsCell m δ c ∧ c.closedBox ⊆ B.closedBox ∧
      (c.closedBox ∩ frontier B.closedBox).Nonempty} with hZ
    have hfin : Z.Finite := Set.finite_of_encard_eq_coe hK
    refine ⟨hfin.toFinset, ?_, fun s hs T hT => ?_⟩
    · have e : (hfin.toFinset.card : ℕ∞) = K := by
        rw [← hK, hfin.encard_eq_coe_toFinset_card]
      have : hfin.toFinset.card = K := by exact_mod_cast e
      rw [this]; exact hKl
    · rcases bdry_cell_mem hB hs hT with h | h
      · exact absurd ⟨T, h.1, h.2⟩ hc
      · exact hfin.mem_toFinset.2 h.2

/-- **The cells of a ring**: for boxes `l` (level `≤ N`) with `Ψ_{·,δ} ≤ λ`, the cells of
`ringSq N l` lie in a finite set of size `≤ #l · λ`. -/
theorem ring_cells_finset {l : List DyBox} {N : ℕ} {lam : ℝ}
    (hl : ∀ B ∈ l, B.n ≤ N ∧ PsiLe m δ B lam) :
    ∃ S : Finset DyBox, (S.card : ℝ) ≤ l.toFinset.card * lam ∧
      ∀ s ∈ ringSq N {B | B ∈ l}, ∀ T, IsSqCell m δ s T → T ∈ S := by
  classical
  have h : ∀ B, B ∈ l → ∃ S : Finset DyBox, (S.card : ℝ) ≤ lam ∧
      ∀ s, IsBdrySq N B s → ∀ T, IsSqCell m δ s T → T ∈ S := fun B hB =>
    bdry_cells_finset (hl B hB).1 (hl B hB).2
  choose f hf1 hf2 using h
  set g : DyBox → Finset DyBox := fun B => if hB : B ∈ l then f B hB else ∅
  refine ⟨l.toFinset.biUnion g, ?_, fun s ⟨B, hB, hs⟩ T hT => ?_⟩
  · calc ((l.toFinset.biUnion g).card : ℝ) ≤ ∑ B ∈ l.toFinset, ((g B).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ l.toFinset, lam := by
          refine Finset.sum_le_sum fun B hB => ?_
          have hB' : B ∈ l := List.mem_toFinset.1 hB
          simp only [g, dif_pos hB']
          exact hf1 B hB'
      _ = l.toFinset.card * lam := by rw [Finset.sum_const, nsmul_eq_mul]
  · have hB' : B ∈ l := hB
    exact Finset.mem_biUnion.2 ⟨B, List.mem_toFinset.2 hB', by
      simp only [g, dif_pos hB']; exact hf2 B hB' s hs T hT⟩

/-- Column/row bounds of a box of `𝓑(C, 2^{-k})` (evaluation at two child squares). -/
lemma boxColl_bounds {C B : DyBox} {k : ℕ} (hB : B ∈ boxColl C k) :
    (C.j : ℤ) * 2 ^ k < B.j + 2 ^ k ∧ (B.j : ℤ) < C.j * 2 ^ k + 2 * 2 ^ k ∧
      (C.k : ℤ) * 2 ^ k < B.k + 2 ^ k ∧ (B.k : ℤ) < C.k * 2 ^ k + 2 * 2 ^ k := by
  obtain ⟨hn, hsub⟩ := hB
  set N := B.n + 1 with hN
  have hBN : B.n ≤ N := by omega
  have hCN : C.n + 1 ≤ N := by omega
  have e : N - C.n - 1 = k := by omega
  have hj2 : 2 * B.j < 2 ^ N := by rw [hN, pow_succ]; have := B.hj; omega
  have hk2 : 2 * B.k < 2 ^ N := by rw [hN, pow_succ]; have := B.hk; omega
  have hj3 : 2 * B.j + 1 < 2 ^ N := by rw [hN, pow_succ]; have := B.hj; omega
  have hk3 : 2 * B.k + 1 < 2 ^ N := by rw [hN, pow_succ]; have := B.hk; omega
  have hw : 2 ^ (N - B.n) = 2 := by rw [show N - B.n = 1 by omega]; rfl
  have lo := sq_sub_of_bounds hBN hj2 hk2 (by rw [hw]; omega) (by rw [hw]; omega)
    (by rw [hw]; omega) (by rw [hw]; omega)
  have hi := sq_sub_of_bounds hBN hj3 hk3 (by rw [hw]; omega) (by rw [hw]; omega)
    (by rw [hw]; omega) (by rw [hw]; omega)
  obtain ⟨a1, -, a3, -⟩ := int_of_sub_largeBox rfl hCN (lo.trans hsub)
  obtain ⟨-, b2, -, b4⟩ := int_of_sub_largeBox rfl hCN (hi.trans hsub)
  simp only [sqAt, e] at a1 a3 b2 b4
  push_cast at a1 a3 b2 b4
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- `#𝓑(C, 2^{-k}) ≤ 4^{k+2}` (crude), for the boxes of a list. -/
theorem card_toFinset_boxColl_le {C : DyBox} {k : ℕ} {l : List DyBox}
    (hl : ∀ B ∈ l, B ∈ boxColl C k) : l.toFinset.card ≤ 4 ^ (k + 2) := by
  classical
  set φ : DyBox → ℕ × ℕ := fun B => (B.j + 2 ^ k - C.j * 2 ^ k, B.k + 2 ^ k - C.k * 2 ^ k)
  have hmaps : ∀ B ∈ l.toFinset, φ B ∈ Finset.range (2 ^ (k + 2)) ×ˢ Finset.range (2 ^ (k + 2)) := by
    intro B hB
    obtain ⟨c1, c2, c3, c4⟩ := boxColl_bounds (hl B (List.mem_toFinset.1 hB))
    have h4 : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; norm_num; ring
    simp only [Finset.mem_product, Finset.mem_range, φ]
    constructor <;> zify [show C.j * 2 ^ k ≤ B.j + 2 ^ k by zify; omega,
      show C.k * 2 ^ k ≤ B.k + 2 ^ k by zify; omega] <;> push_cast <;> omega
  have hinj : Set.InjOn φ l.toFinset := by
    intro B hB B' hB' h
    have n1 := (hl B (List.mem_toFinset.1 hB)).1
    have n2 := (hl B' (List.mem_toFinset.1 hB')).1
    obtain ⟨c1, -, c3, -⟩ := boxColl_bounds (hl B (List.mem_toFinset.1 hB))
    obtain ⟨d1, -, d3, -⟩ := boxColl_bounds (hl B' (List.mem_toFinset.1 hB'))
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : B.j = B'.j := by zify [show C.j * 2 ^ k ≤ B.j + 2 ^ k by zify; omega,
      show C.j * 2 ^ k ≤ B'.j + 2 ^ k by zify; omega] at h1; omega
    have : B.k = B'.k := by zify [show C.k * 2 ^ k ≤ B.k + 2 ^ k by zify; omega,
      show C.k * 2 ^ k ≤ B'.k + 2 ^ k by zify; omega] at h2; omega
    ext <;> omega
  calc l.toFinset.card ≤ (Finset.range (2 ^ (k + 2)) ×ˢ Finset.range (2 ^ (k + 2))).card :=
        Finset.card_le_card_of_injOn φ hmaps hinj
    _ = 4 ^ (k + 2) := by
        rw [Finset.card_product, Finset.card_range, ← mul_pow]; norm_num

end DZZ
end LQGMetric
