/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53L6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13G7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Lower

/-!
# DZZ Lemma 5.3, part 1: P-131A remainder — the L3.13 refinement of the cell chain (P2-DZZ53LR)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2366–2379 (`𝓔*`: the chain of L3.13
boxes inside the cells of a good cell chain), l. 1327–1336 (the L3.13 construction and size check).

* `l53_last`, `l53_tail`, `l53_assemble`: copies of `l313_last`, `l313_tail`, `l313_assemble`
  (S3L13G6) with the extra invariant that every box lies in a cell **of the given cell chain**
  (`L53SafeIn`).
* **`l53D1EventR_subset_l53D1EventB`** (DEC-131 §2, corrected form): on `𝒟₁` (cell chain meeting
  `R`, I5) with `u`, `v` good, the selected box chain of `𝓔*` is nonempty, with region any
  `R' ⊇ cthickening (2 δ^{C_Mc}) R` and length exponent `T + 2 epsStarN log 4 + log 9`. The
  disjointness clause is `disjoint_boxReg_fineReg_of_cov` with the cover argument of
  `l313GeomC_of_pos` (S3L13G7), the length from `l313_len_asym`.

The region has to be enlarged: the boxes only lie in cells meeting `R`, they need not meet `R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

section Assemble

variable {m : DyBox → ℝ} {δ : ℝ}

/-- `L313Safe` with the cell taken from the list `S`. -/
def L53SafeIn (m : DyBox → ℝ) (δ : ℝ) (k : ℕ) (S : List DyBox) (b : DyBox) : Prop :=
  ∃ C ∈ S, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * k ∧
    ∀ z ∈ dzzV, l313Near ((2 : ℝ)⁻¹ ^ k * C.side / 10) b z →
      (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z

lemma L53SafeIn.mono {k : ℕ} {S S' : List DyBox} (hS : S ⊆ S') {b : DyBox}
    (h : L53SafeIn m δ k S b) : L53SafeIn m δ k S' b := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hS hC, h⟩

/-- `l313_last` with the cell recorded. -/
lemma l53_last {k : ℕ} {v : ℂ} (hv : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) v) {C s0 : DyBox}
    (hC : IsCell m δ C) (hCv : C.Mem v) (hs0 : s0.n = C.n + 2 * k)
    (hs0C : s0.closedBox ⊆ C.closedBox) :
    ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s0 ∧ (L.getLast hL).Mem v ∧
      L.IsChain Neighbour ∧ (∀ b ∈ L, L53SafeIn m δ k [C] b) ∧ L.length ≤ 4 ^ (2 * k) := by
  have hvC : v ∈ C.largeBox := closedBox_sub_largeBox' C (mem_closedBox_of_mem hCv)
  have hε1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := side_pos' C
  obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := exists_chain_in_box (show C.n ≤ C.n + 2 * k by omega)
    hs0 rfl hs0C (boxAt_sub_cell hCv (show C.n ≤ C.n + 2 * k by omega))
  refine ⟨L, hL, h1, by rw [h2]; exact boxAt_mem_self hCv.1, h3, fun b hb => ?_, by
    rwa [show C.n + 2 * k - C.n = 2 * k by omega] at h4⟩
  obtain ⟨hbn, hbC⟩ := h5 b hb
  refine ⟨C, List.mem_singleton_self C, hC, hbC, hbn,
    fun z hz hn => le_cellSide_of_goodPoint hv hC hvC hbC ?_ hz hn⟩
  nlinarith

/-- `l313_tail` with the cell recorded in the cell chain `C :: l`. -/
theorem l53_tail {k : ℕ} (hk : 4 ≤ k) {v : ℂ} (hv : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) v) :
    ∀ (l : List DyBox) (C : DyBox) (x0 : ℂ) (s0 : DyBox), IsCell m δ C → (∀ c ∈ l, IsCell m δ c) →
      IsGoodSeq ((2 : ℝ)⁻¹ ^ k) (C :: l) → ((C :: l).getLast (List.cons_ne_nil _ _)).Mem v →
      s0.n = C.n + 2 * k → s0.closedBox ⊆ C.closedBox → x0 ∈ s0.closedBox →
      (∀ z ∈ dzzV, l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) x0 z →
        (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z) →
      ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s0 ∧ (L.getLast hL).Mem v ∧
        L.IsChain Neighbour ∧ (∀ b ∈ L, L53SafeIn m δ k (C :: l) b) ∧
        L.length ≤ (l.length + 1) * 4 ^ (2 * k)
  | [], C, x0, s0, hC, _, _, hlast, hs0, hs0C, _, _ => by
    obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := l53_last hv hC hlast hs0 hs0C
    exact ⟨L, hL, h1, h2, h3, h4, by simpa using h5⟩
  | C' :: l', C, x0, s0, hC, hcells, hG, hlast, hs0, hs0C, hx0, hdoor0 => by
    rw [IsGoodSeq, List.isChain_cons_cons] at hG
    obtain ⟨⟨hN, hr⟩, hG'⟩ := hG
    have hC' := hcells C' List.mem_cons_self
    obtain ⟨x, s, s', D1, D2, hss'⟩ := exists_door hC hC' hN (by omega) hr
    obtain ⟨L1, hL1, a1, a2, a3, a4, a5⟩ :=
      exists_corridor hk hs0 hs0C hx0 D1.1 D1.2.1 D1.2.2.1
    have hlast' : ((C' :: l').getLast (List.cons_ne_nil _ _)).Mem v := by
      rwa [List.getLast_cons (List.cons_ne_nil _ _)] at hlast
    obtain ⟨L2, hL2, b1, b2, b3, b4, b5⟩ := l53_tail hk hv l' C' x s' hC'
      (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hG' hlast' D2.1 D2.2.1 D2.2.2.1
      D2.2.2.2.2
    have hs := side_pos' C
    have hε1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine ⟨L1 ++ L2, List.append_ne_nil_of_left_ne_nil hL1 _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head_append_of_ne_nil hL1]; exact a1
    · rw [List.getLast_append_of_ne_nil _ hL2]; exact b2
    · refine a3.append b3 fun p hp q hq => ?_
      rw [List.getLast?_eq_some_getLast hL1, a2, Option.mem_some_iff] at hp
      rw [List.head?_eq_some_head hL2, b1, Option.mem_some_iff] at hq
      rw [← hp, ← hq]; exact hss'
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨hbn, hbC, hcov⟩ := a5 b hb
        refine ⟨C, List.mem_cons_self, hC, hbC, hbn, fun z hz hn => ?_⟩
        rcases hcov z hn with ho | hd | hd
        · obtain ⟨o1, o2, o3, o4⟩ := ho
          rw [cellSide_eq_of_ho hC hz o1.le o2 o3.le o4]; nlinarith
        · exact hdoor0 z hz hd
        · exact D1.2.2.2.2 z hz hd
      · exact (b4 b hb).mono (List.subset_cons_self _ _)
    · rw [List.length_append, List.length_cons]
      calc L1.length + L2.length ≤ 4 ^ (2 * k) + (l'.length + 1) * 4 ^ (2 * k) := add_le_add a4 b5
        _ = (l'.length + 1 + 1) * 4 ^ (2 * k) := by ring

/-- `l313_assemble` with every box inside a cell of the cell chain `l`. -/
theorem l53_assemble {k : ℕ} (hk : 4 ≤ k) {u v : ℂ} (hu : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) u)
    (hv : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) v) {l : List DyBox} (hJ : JoinsCells m δ u v l)
    (hG : IsGoodSeq ((2 : ℝ)⁻¹ ^ k) l) :
    ∃ L : List DyBox, ((∃ hL : L ≠ [], (L.head hL).Mem u ∧ (L.getLast hL).Mem v) ∧
      L.IsChain Neighbour) ∧ (∀ b ∈ L, L53SafeIn m δ k l b) ∧
      L.length ≤ l.length * 4 ^ (2 * k) := by
  obtain ⟨hl, hcells, hhead, hlast⟩ := hJ
  obtain ⟨C, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hC := hcells C List.mem_cons_self
  have hCu : C.Mem u := hhead
  have huV := hCu.1
  have hs := side_pos' C
  have hε0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hε1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have huC := mem_closedBox_of_mem hCu
  have hdoor : ∀ z ∈ dzzV, l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) u z →
      (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z := by
    rintro z hz ⟨d1, d2⟩
    obtain ⟨c1, c2, c3, c4⟩ := huC
    refine hu C hC (closedBox_sub_largeBox' C (mem_closedBox_of_mem hCu)) z ⟨?_, ?_⟩ hz <;>
      simp only [DyBox.center] <;> rw [abs_lt] at d1 d2 ⊢ <;> constructor <;> nlinarith
  obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := l53_tail hk hv l' C u (boxAt (C.n + 2 * k) u) hC
    (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hG hlast rfl
    (boxAt_sub_cell hCu (by omega)) (mem_closedBox_boxAt huV) hdoor
  refine ⟨L, ⟨⟨hL, by rw [h1]; exact boxAt_mem_self huV, h2⟩, h3⟩, h4, ?_⟩
  simpa using h5

end Assemble

variable {Ω : Type*} {W : WNSpace → Ω → ℝ}

/-- **The refinement, general form**: for small `δ`, on `𝒟₁` with `u`, `v` good, the box chain of
`𝓔*` exists, for any region `R' ⊇ (R)^{2δ^{C_Mc}}` and any `T'` with `e^T 4^{2 n_{ε*}} ≤ e^{T'}`. -/
theorem l53D1EventR_subset_l53D1EventB_gen {αs : ℝ} (hαs : 0 < αs) (γ : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ (u v : ℂ) (R R' : Set ℂ) (T T' : ℝ),
      Metric.cthickening (2 * δ ^ dzzCMc γ) R ⊆ R' →
      Real.exp T * (4 : ℝ) ^ (2 * epsStarN αs δ) ≤ Real.exp T' →
      l53D1EventR γ W αs δ u v R T ∩ {ω | IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) u ∧
        IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) v} ⊆
      l53D1EventB γ W αs δ u v R' T' := by
  obtain ⟨δ₁, hδ₁, hA⟩ := l313_len_asym hαs
  obtain ⟨δ₂, hδ₂, hS⟩ := l313_size_asym hαs (abs_nonneg (dzzCmc γ))
  refine ⟨min (min δ₁ δ₂) 1, lt_min (lt_min hδ₁ hδ₂) one_pos,
    fun δ hδ u v R R' T T' hR' hT' ω ⟨⟨hcs, l, hJ, hG, hmeet, hl⟩, hgu, hgv⟩ => ?_⟩
  have hδ1 : δ ∈ Ioo 0 δ₁ := ⟨hδ.1, hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hδ2 : δ ∈ Ioo 0 δ₂ := ⟨hδ.1, hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hδlt1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  obtain ⟨hk4, -⟩ := hA δ hδ1
  obtain ⟨L, hL1, hL2, hL3⟩ := l53_assemble (k := epsStarN αs δ) hk4 hgu hgv hJ hG
  have hside : ∀ b : DyBox, ∀ C : DyBox, b.n = C.n + 2 * epsStarN αs δ →
      b.side = C.side * epsStar αs δ ^ 2 := by
    intro b C hbn
    show (2 : ℝ)⁻¹ ^ b.n = (2 : ℝ)⁻¹ ^ C.n * ((2 : ℝ)⁻¹ ^ epsStarN αs δ) ^ 2
    rw [hbn, ← pow_mul, ← pow_add, mul_comm 2]
  -- the cover condition (`l313GeomC_of_pos`)
  have hcov : ∀ b ∈ L, ∀ x ∈ b.largeBox, ∀ z ∈ dzzV, dist z x < l313Rho b.side →
      b.side ≤ cellSide (approxLQG γ W ω) δ z := by
    intro b hb x hx z hz hd
    obtain ⟨C, -, hC, hbC, hbn, hcov⟩ := hL2 b hb
    have hsb := hside b C hbn
    have hCs : δ ^ |dzzCmc γ| ≤ C.side :=
      (Real.rpow_le_rpow_of_exponent_ge hδ.1 hδlt1.le (le_abs_self _)).trans (hcs.2 C hC).1
    have hsz := hS δ hδ2 C.side hCs (side_pos' C)
    rw [← hsb] at hsz
    have hb0 := side_pos' b
    have hn := l313Near_mono (show l313Rho b.side + b.side / 2 ≤
      epsStar αs δ * C.side / 10 by linarith) (l313Near_of_largeBox hx hd)
    have hc := hcov z hz hn
    have hε0 : 0 < epsStar αs δ := by unfold epsStar; positivity
    have hε1 : epsStar αs δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hCs0 := side_pos' C
    calc b.side = epsStar αs δ * (epsStar αs δ * C.side) := by rw [hsb]; ring
      _ ≤ 1 * (epsStar αs δ * C.side) := mul_le_mul_of_nonneg_right hε1 (by positivity)
      _ = (2 : ℝ)⁻¹ ^ epsStarN αs δ * C.side := by rw [one_mul]; rfl
      _ ≤ _ := hc
  refine ⟨hcs, l53Chain_ne_nil ⟨⟨hL1, fun b hb => ?_, disjoint_boxReg_fineReg_of_cov _ δ L hcov⟩,
    fun b hb => ?_, ?_⟩⟩
  · obtain ⟨C, -, hC, hbC, hbn, -⟩ := hL2 b hb
    exact ⟨C, hC, hbC, hside b C hbn⟩
  · -- the box lies in a cell meeting `R`, of side `≤ δ^{C_Mc}`
    obtain ⟨C, hCl, hC, hbC, -, -⟩ := hL2 b hb
    obtain ⟨p, hpC, hpR⟩ := hmeet C hCl
    have hcen := hbC (center_mem_closedBox' b)
    refine ⟨b.center, center_mem_closedBox' b, hR' ?_⟩
    refine Metric.mem_cthickening_of_dist_le _ p _ R hpR ?_
    have := dist_le_of_mem_closedBox hcen hpC
    linarith [(hcs.2 C hC).2]
  · -- the length: `d_L ≤ d_l 4^{2k} ≤ e^T 4^{2k}`
    have hL3' : (L.length : ℝ) ≤ (l.length : ℝ) * (4 : ℝ) ^ (2 * epsStarN αs δ) := by
      exact_mod_cast hL3
    have h0 : (0 : ℝ) ≤ (4 : ℝ) ^ (2 * epsStarN αs δ) := by positivity
    exact hL3'.trans ((mul_le_mul_of_nonneg_right hl h0).trans hT')

end DZZ
end LQGMetric
