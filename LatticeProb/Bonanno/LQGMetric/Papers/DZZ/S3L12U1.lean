/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12U1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T5

/-!
# DZZ Lemma 3.12: ring enclosures and the parent count (P2-DEC93, D93)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`: proof of Lemma 3.12, l. 1462–1497.
DZZ split `𝒞_{i,cross}` "into two segments with respective ending cells `𝖢_{i,1}` and `𝖢_{i,2}`"
(l. 1471–1473): this presumes that the enclosure is a closed ring. Decision D93 (DEC-93): the
enclosure consumed by Lemma 3.12 is the ring that DZZ's percolation argument actually produces
(the four rectangle crossings of Lemma 3.7/3.16, l. 1009–1011 "by duality"), in the cell form
`CellRing`: a cyclic `Neighbour`-sequence of cells in which every parent (cell of side `> s_𝖢`,
DZZ's `𝔠_parents`, l. 1462–1466) occurs exactly once; it is only required when
`𝖢_large ⊆ 𝕍°` (DZZ's "harder case", l. 1461; in the other case `𝔠_parents` has at most one
cell, l. 1498).

* `CellRing m δ ε C`: (eq-percolation-good-surrounding) with the ring structure;
* `L312CoreR`: `L312Core` with `CellRing` as hypothesis (the new open node of DEC-93);
* `card_l312Bad_le_one_of_parents`: a chain of cells of side `≥ ε s` containing at most one
  cell of side `> s` has at most one bad cell (Cases 1, 2: `ψ(𝒞_{i,replace}) ⊆ {𝖢_{i,1}}`);
* `l312Bad_case3_diag`, `card_l312Bad_case3_adj`: DZZ's Case 3 (l. 1489–1497): the replacing
  sequences `𝖢_{i,1}, 𝖢, 𝖢_{i,2}` (diagonal parents) and `𝖢_{i,1}, 𝖢_{i,2}` (neighbouring
  parents) have `ψ = ∅`, resp. at most one bad cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- **Ring form of (eq-percolation-good-surrounding)** (D93): a cell enclosure of `𝖢` and, when
`𝖢_large ⊆ 𝕍°`, a cyclic `Neighbour`-sequence `Z` of cells of side `≥ ε s_𝖢` meeting
`𝖢_large \ 𝖢`, enclosing `𝖢`, in which every cell of side `> s_𝖢` occurs exactly once. -/
def CellRing (m : DyBox → ℝ) (δ ε : ℝ) (C : DyBox) : Prop :=
  CellEnclosure m δ ε C ∧
    (C.largeBox ⊆ interior dzzV → ∃ Z : List DyBox, ∃ hne : Z ≠ [],
      Z.IsChain Neighbour ∧ Neighbour (Z.getLast hne) (Z.head hne) ∧
      (∀ c ∈ Z, IsCell m δ c ∧ ε * C.side ≤ c.side ∧
        (c.closedBox ∩ (C.largeBox \ C.closedBox)).Nonempty) ∧
      EnclosesBox C {c | c ∈ Z} ∧
      ∀ p ∈ Z, C.side < p.side → Z.count p = 1)

/-- `L312Core` with the ring enclosures of D93 as hypothesis (DZZ l. 1462–1497). -/
def L312CoreR (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∀ l : List DyBox, JoinsCells m δ u v l → l.IsChain Neighbour → l.Nodup →
      ∀ C ∈ l312Bad (epsStar αs δ) l, (∀ c ∈ l312Bad (epsStar αs δ) l, c.side ≤ C.side) →
        ∃ (A M B R : List DyBox) (x y : DyBox), l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧
          (x :: R ++ [y]).IsChain Neighbour ∧ R.Nodup ∧
          (∀ c ∈ R, IsCell m δ c ∧ epsStar αs δ * C.side ≤ c.side ∧
            (c.closedBox ∩ C.largeBox).Nonempty) ∧
          epsStar αs δ * C.side ≤ x.side ∧ epsStar αs δ * C.side ≤ y.side ∧
          (l312Bad (epsStar αs δ) (x :: R ++ [y])).card ≤ 1

/-- Cases 1 and 2 (l. 1478–1488): in a sequence of cells of side `≥ ε s` with at most one cell
of side `> s`, at most one cell is bad. -/
theorem card_l312Bad_le_one_of_parents {ε s : ℝ} (hε : 0 < ε) {W : List DyBox}
    (hW : ∀ c ∈ W, ε * s ≤ c.side)
    (hpar : ∀ c ∈ W, ∀ c' ∈ W, s < c.side → s < c'.side → c = c') :
    (l312Bad ε W).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  exact hpar a (mem_of_mem_l312Bad ha) b (mem_of_mem_l312Bad hb)
    (side_gt_of_mem_l312Bad hε hW ha) (side_gt_of_mem_l312Bad hε hW hb)

lemma pair_infix_two {c c' x y : DyBox} (h : [c, c'] <:+: [x, y]) : c = x ∧ c' = y := by
  rw [List.infix_cons_iff] at h
  rcases h with h | h
  · rw [List.cons_prefix_cons, List.cons_prefix_cons] at h
    exact ⟨h.1, h.2.1⟩
  · exact absurd (List.IsInfix.length_le h) (by simp)

lemma pair_infix_three {c c' x C y : DyBox} (h : [c, c'] <:+: [x, C, y]) :
    (c = x ∧ c' = C) ∨ (c = C ∧ c' = y) := by
  rw [List.infix_cons_iff] at h
  rcases h with h | h
  · rw [List.cons_prefix_cons, List.cons_prefix_cons] at h
    exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr (pair_infix_two h)

/-- Case 3, diagonal parents (l. 1493–1495): `𝖢_{i,1}, 𝖢, 𝖢_{i,2}` has no bad cell when
`s_𝖢 ≤ s_{𝖢_{i,j}} ≤ s_𝖢 / ε*` (the upper bound by maximality of `𝖢`, l. 1491–1492). -/
theorem l312Bad_case3_diag {ε : ℝ} (hε : ε ≤ 1) {x C y : DyBox} (hx : C.side ≤ x.side)
    (hy : C.side ≤ y.side) (hx' : ε * x.side ≤ C.side) (hy' : ε * y.side ≤ C.side) :
    l312Bad ε [x, C, y] = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  have hC : ε * C.side ≤ C.side := by
    have := mul_le_mul_of_nonneg_right hε C.side_pos'.le; linarith
  obtain ⟨-, c', hp, hs⟩ := exists_pair_of_mem_l312Bad hc
  rcases hp with h | h
  · rcases pair_infix_three h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  · rcases pair_infix_three h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith

/-- Case 3, neighbouring parents (l. 1495–1496): `𝖢_{i,1}, 𝖢_{i,2}` has at most one bad cell
(`ε ≤ 1`: the two cells cannot both be bad). -/
theorem card_l312Bad_case3_adj {ε : ℝ} (hε : ε ≤ 1) {x y : DyBox} :
    (l312Bad ε [x, y]).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  by_contra hab
  have hx := x.side_pos'
  have hy := y.side_pos'
  obtain ⟨-, a', hpa, hsa⟩ := exists_pair_of_mem_l312Bad ha
  obtain ⟨-, b', hpb, hsb⟩ := exists_pair_of_mem_l312Bad hb
  have ha' : (a = x ∧ a' = y) ∨ (a = y ∧ a' = x) := by
    rcases hpa with h | h
    · exact Or.inl (pair_infix_two h)
    · exact Or.inr ⟨(pair_infix_two h).2, (pair_infix_two h).1⟩
  have hb' : (b = x ∧ b' = y) ∨ (b = y ∧ b' = x) := by
    rcases hpb with h | h
    · exact Or.inl (pair_infix_two h)
    · exact Or.inr ⟨(pair_infix_two h).2, (pair_infix_two h).1⟩
  rcases ha' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab rfl
  · nlinarith [mul_le_mul_of_nonneg_right hε hx.le, mul_le_mul_of_nonneg_right hε hy.le]
  · nlinarith [mul_le_mul_of_nonneg_right hε hx.le, mul_le_mul_of_nonneg_right hε hy.le]
  · exact hab rfl

end DZZ
end LQGMetric
