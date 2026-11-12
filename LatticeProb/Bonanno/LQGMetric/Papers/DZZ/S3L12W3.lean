/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Main

/-!
# DZZ Lemma 3.12: the clipped case of `L312CoreR` (D93, packet P-7)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1461 ("the
harder case" `𝖢_large ⊆ 𝕍°`) and l. 1498 (`𝖢 ∩ ∂𝕍 ≠ ∅`: at most one parent). When `𝖢_large`
meets `∂𝕍`, any segment of the enclosure between `𝖢_{i,1}` and `𝖢_{i,2}` contains at most one
parent, so it has at most one bad cell (Cases 1–2):

* `L312CoreRing`: `L312CoreR` in the case `𝖢_large ⊆ 𝕍°`;
* **`l312CoreR_of_ring : L312CoreRing γ → L312CoreR γ`** (`exists_enc_split`,
  `exists_enc_path`, `le_one_parent_of_not_interior`, `card_l312Bad_le_one_of_parents`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- `L312CoreR` in DZZ's "harder case" `𝖢_large ⊆ 𝕍°` (l. 1461–1497). -/
def L312CoreRing (γ : ℝ) : Prop :=
  ∀ αs : ℝ, 0 < αs → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ m : DyBox → ℝ,
    (∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) →
    (∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ) →
    (∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C) →
    ∀ u ∈ dzzV, ∀ v ∈ dzzV, IsGoodPoint m δ (epsStar αs δ) u →
      IsGoodPoint m δ (epsStar αs δ) v →
      ∀ l : List DyBox, JoinsCells m δ u v l → l.IsChain Neighbour → l.Nodup →
      ∀ C ∈ l312Bad (epsStar αs δ) l, (∀ c ∈ l312Bad (epsStar αs δ) l, c.side ≤ C.side) →
        C.largeBox ⊆ interior dzzV →
        ∃ (A M B R : List DyBox) (x y : DyBox), l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧
          (x :: R ++ [y]).IsChain Neighbour ∧ R.Nodup ∧
          (∀ c ∈ R, IsCell m δ c ∧ epsStar αs δ * C.side ≤ c.side ∧
            (c.closedBox ∩ C.largeBox).Nonempty) ∧
          epsStar αs δ * C.side ≤ x.side ∧ epsStar αs δ * C.side ≤ y.side ∧
          (l312Bad (epsStar αs δ) (x :: R ++ [y])).card ≤ 1

/-- The level of a bad cell is below the finest level `N` (its small neighbour is a cell). -/
lemma n_add_one_le_of_bad {m : DyBox → ℝ} {δ ε : ℝ} (hε1 : ε ≤ 1) {N : ℕ}
    (hN : ∀ b, IsCell m δ b → b.n ≤ N) {l : List DyBox} (hl : ∀ c ∈ l, IsCell m δ c)
    {C : DyBox} (hC : C ∈ l312Bad ε l) : C.n + 1 ≤ N := by
  obtain ⟨-, c', hp, hs⟩ := exists_pair_of_mem_l312Bad hC
  have hc' : c' ∈ l := by
    rcases hp with h | h
    · exact infix_mem_right h
    · exact infix_mem_left h
  have h1 := hN c' (hl c' hc')
  have h2 : C.n < c'.n :=
    n_lt_of_side_lt (hs.trans_le (mul_le_of_le_one_left C.side_pos'.le hε1))
  omega

/-- **`L312CoreR` from its ring case** (the clipped case, DZZ l. 1498). -/
theorem l312CoreR_of_ring {γ : ℝ} (h : L312CoreRing γ) : L312CoreR γ := by
  intro αs hαs
  obtain ⟨δ₀, hδ₀, h⟩ := h αs hαs
  refine ⟨δ₀, hδ₀, fun δ hδ m hcov hsize hring u hu v hv hgu hgv l hj hch hnd C hC hmax => ?_⟩
  by_cases hint : C.largeBox ⊆ interior dzzV
  · exact h δ hδ m hcov hsize hring u hu v hv hgu hgv l hj hch hnd C hC hmax hint
  set ε := epsStar αs δ
  have hε : 0 < ε := by simp only [ε, epsStar]; positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hCcell : IsCell m δ C := hj.2.1 C (mem_of_mem_l312Bad hC)
  obtain ⟨E, -, hEch, hEc, henc⟩ := (hring C hCcell).1
  set N := ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊
  have hN : ∀ b, IsCell m δ b → b.n ≤ N := fun b hb =>
    Nat.le_floor (n_le_of_rpow_le_side hδ.1 (hsize b hb).1)
  have hCN := n_add_one_le_of_bad hε1 hN hj.2.1 hC
  obtain ⟨A, M, B, x, y, hl, hCM, hx, hy, -⟩ := exists_enc_split hN hε1 hgu hgv hj hch hC hCN
    (fun c hc => ⟨(hEc c hc).1, (hEc c hc).2.2⟩) henc
  have hxy : x ≠ y := by
    rintro rfl
    have h2 : (x :: (M ++ x :: B)).Nodup := (hl ▸ hnd).sublist (List.sublist_append_right A _)
    exact (List.nodup_cons.1 h2).1 (by simp)
  obtain ⟨R, hRch, hRnd, hRE⟩ := exists_enc_path hEch (fun c hc => (hEc c hc).1) hx hy hxy
  have hRnd' : R.Nodup := by
    have := (List.nodup_cons.1 (by simpa using hRnd : (x :: (R ++ [y])).Nodup)).2
    exact this.sublist (List.sublist_append_left R [y])
  have hWE : ∀ c ∈ x :: R ++ [y], c ∈ E := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | hc | rfl
    · exact hx
    · exact hRE c hc
    · exact hy
  have hmeet : ∀ c ∈ E, (c.closedBox ∩ C.largeBox).Nonempty := fun c hc =>
    (hEc c hc).2.2.mono (inter_subset_inter_right _ sdiff_subset)
  refine ⟨A, M, B, R, x, y, hl, hCM, hRch, hRnd', fun c hc => ⟨(hEc c (hRE c hc)).1,
    (hEc c (hRE c hc)).2.1, hmeet c (hRE c hc)⟩, (hEc x hx).2.1, (hEc y hy).2.1, ?_⟩
  refine card_l312Bad_le_one_of_parents hε (fun c hc => (hEc c (hWE c hc)).2.1) ?_
  intro c hc c' hc' hs hs'
  exact le_one_parent_of_not_interior hint hCcell (hEc c (hWE c hc)).1 (hEc c' (hWE c' hc')).1
    hs hs' (hmeet c (hWE c hc)) (hmeet c' (hWE c' hc'))

end DZZ
end LQGMetric
