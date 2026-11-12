/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XGeo
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XBridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XCell

/-!
# DZZ Lemma 3.12, one-step claim: the chain meets the enclosure in a common cell (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1468–1470: "Suppose that
`𝒞_{i,cross}` intersects `[𝖢_enter, 𝖢_exit]_{𝒞_i}` at `𝖢_{i,1}` and `𝖢_{i,2}`": DZZ splice at
cells common to the chain and the enclosure. `exists_meet_of_enclosesBox` (S3L12S6) only gives
closed boxes that touch; here, via the level-`N` square grid of decision D84
(`sqSep_of_enclosesBox`, `exists_labelled_path`), a genuinely common cell:

* **`exists_mem_enc_of_chain`**: a `Neighbour`-chain of cells from `𝖢` to a cell containing a point
  outside `𝖢_large` contains a cell of every enclosure of `𝖢` made of cells.

Own elementary argument (DZZ use it without comment); DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma mem_of_sq_sub {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {s b b' : DyBox} (hs : s.n = N)
    (hb : IsCell m δ b) (hb' : IsCell m δ b') (h : s.closedBox ⊆ b.closedBox)
    (h' : s.closedBox ⊆ b'.closedBox) : b = b' := by
  have n1 := hN b hb; have n2 := hN b' hb'
  exact isSqCell_unique ⟨hb, by omega, anc_eq_of_sub hs n1 h⟩ ⟨hb', by omega, anc_eq_of_sub hs n2 h'⟩

/-- **A chain from `𝖢` to the outside of `𝖢_large` contains a cell of each enclosure of `𝖢`**
(DZZ l. 1468–1470, with common cells). -/
theorem exists_mem_enc_of_chain {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {C : DyBox}
    (hCN : C.n + 1 ≤ N) {E : List DyBox} (hE : ∀ c ∈ E, IsCell m δ c)
    (henc : EnclosesBox C {c | c ∈ E}) {L : List DyBox} (hne : L ≠ [])
    (hch : L.IsChain Neighbour) (hcells : ∀ c ∈ L, IsCell m δ c) (hhead : L.head hne = C)
    {w : ℂ} (hw : (L.getLast hne).Mem w) (hwC : w ∉ C.largeBox) : ∃ c ∈ L, c ∈ E := by
  by_contra hno
  push Not at hno
  have hC : IsCell m δ C := hhead ▸ hcells _ (List.head_mem hne)
  obtain ⟨p, hp⟩ := exists_walk_of_isChain L hne (isChain_cellGraph_of L hch hcells)
  have hCn := hN C hC
  have hlast := hcells _ (List.getLast_mem hne)
  have hLn := hN _ hlast
  set s₀ := cornerSq N (L.head hne) (by rw [hhead]; omega)
  set s₁ := boxAt N w
  obtain ⟨M, f, lab, hf0, hfM, -, -, hft, hfs⟩ := exists_labelled_path hN p
    (hhead ▸ hC) s₀ s₁ rfl (cornerSq_sub _ _) rfl (boxAt_sub_cell hw hLn)
  have hsep := sqSep_of_enclosesBox henc (fun b hb => hN b (hE b hb)) hCN
  have hfree : ∀ t ≤ M, SqFree {c | c ∈ E} (f t) := by
    intro t ht b hb hsub
    obtain ⟨hn, -, hsubv⟩ := hft t ht
    have e := mem_of_sq_sub hN hn (hE b hb) (isCell_of_mem_support (hhead ▸ hC) p _
      (p.getVert_mem_support _)) hsub hsubv
    exact hno b (hp ▸ e ▸ p.getVert_mem_support _) hb
  have hrt : ∀ t ≤ M, Relation.ReflTransGen (SqStep {c | c ∈ E}) s₀ (f t) := by
    intro t
    induction t with
    | zero => intro _; rw [hf0]
    | succ t ih =>
      intro ht
      rcases (hfs t (by omega)).1 with e | e
      · rw [← e]; exact ih (by omega)
      · exact (ih (by omega)).tail ⟨e, hfree (t + 1) ht⟩
  have h1 := hsep s₀ s₁ rfl (by rw [← hhead]; exact cornerSq_sub _ _) (hf0 ▸ hfree 0 (Nat.zero_le _))
    (hfM ▸ hrt M le_rfl)
  exact hwC (h1 (mem_closedBox_boxAt hw.1))

end DZZ
end LQGMetric
