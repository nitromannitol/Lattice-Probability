/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XCell at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XSq
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XRec
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Mono
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi

/-!
# DZZ Lemma 3.5: cells of grid squares and the count of a crossing (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1076–1079, (Eq.boundDprime)): the
crossing built from the cells of `(⋃ ℂ_i) ∪ ℂ_start ∪ ℂ_end` bounds `D'_{δ'}` by its number of
cells. On the level-`N` grid (decision D84), with all `δ'`-cells of level `≤ N`:

* `IsSqCell m δ s T`: `T` is the `δ`-cell containing the square `s` (`s` lies in `T`).
* `exists_isSqCell`, `isSqCell_unique`, `isSqCell_adj` (cells of adjacent squares are equal or
  neighbours).
* **`approxDist_le_card_of_path`**: a path of squares from a square containing `u` to one
  containing `v` all of whose cells lie in a finite set `S` gives `D'_δ(u, v) ≤ #S`.

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

lemma boxAt_center {s : DyBox} {N : ℕ} (hs : s.n = N) : boxAt N s.center = s := by
  have hre := bx_center_re hs
  have him := bx_center_im hs
  have hj : s.j < 2 ^ N := hs ▸ s.hj
  have hk : s.k < 2 ^ N := hs ▸ s.hk
  have fj : ⌊s.center.re * 2 ^ N⌋₊ = s.j := by
    rw [hre, Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have fk : ⌊s.center.im * 2 ^ N⌋₊ = s.k := by
    rw [him, Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  ext
  · exact hs.symm
  · show min _ _ = _; rw [fj]; omega
  · show min _ _ = _; rw [fk]; omega

/-- `T` is the `δ`-cell containing the square `s`. -/
def IsSqCell (m : DyBox → ℝ) (δ : ℝ) (s T : DyBox) : Prop :=
  IsCell m δ T ∧ T.n ≤ s.n ∧ s.anc T.n = T

lemma IsSqCell.sub {s T : DyBox} (h : IsSqCell m δ s T) : s.closedBox ⊆ T.closedBox := by
  rw [← h.2.2]; exact closedBox_sub_anc s _

lemma exists_isSqCell (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀) {s : DyBox} (hs : N₀ ≤ s.n) : ∃ T, IsSqCell m δ s T := by
  obtain ⟨T, hT, hTm⟩ := hpart s.center (closedBox_sub_dzzV' s (center_mem_closedBox' s))
  have hTn := hN₀ T hT
  refine ⟨T, hT, by omega, ?_⟩
  have := anc_boxAt (show T.n ≤ s.n by omega) s.center
  rw [boxAt_center rfl] at this
  rw [this]; exact hTm.2

lemma isSqCell_unique {s T T' : DyBox} (h : IsSqCell m δ s T) (h' : IsSqCell m δ s T') :
    T = T' := by
  wlog hle : T.n ≤ T'.n generalizing T T'
  · exact (this h' h (by omega)).symm
  have e : T = T'.anc T.n := by rw [← h'.2.2, anc_anc s hle, h.2.2]
  rcases Nat.lt_or_ge T.n T'.n with hlt | hge
  · have := h'.1.2 T.n hlt
    rw [← e] at this
    exact absurd h.1.1 (not_lt.2 this)
  · rw [e, anc_self (show T'.n ≤ T.n by omega)]

lemma neighbour_of_sqAdj {s t : DyBox} (h : SqAdj s t) : Neighbour s t := by
  obtain ⟨hn, h⟩ := h
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact neighbour_of_k_succ hn.symm h1.symm h2.symm
  · exact (neighbour_of_k_succ hn h1 h2.symm).symm
  · exact neighbour_of_j_succ hn.symm h1.symm h2.symm
  · exact (neighbour_of_j_succ hn h1 h2.symm).symm

lemma isSqCell_adj {s t T T' : DyBox} (hst : SqAdj s t) (h : IsSqCell m δ s T)
    (h' : IsSqCell m δ t T') : T = T' ∨ (cellGraph m δ).Adj T T' := by
  rcases eq_or_neighbour_of_sub (neighbour_of_sqAdj hst) h.sub h'.sub with e | hN
  · exact Or.inl e
  · exact Or.inr ⟨h.1, h'.1, hN⟩

/-- A path of squares whose cells lie in `S` gives a walk of cells with support in `S`. -/
lemma exists_walk_of_path (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀) (p : ℕ → DyBox) (M : ℕ) (hpn : ∀ t ≤ M, N₀ ≤ (p t).n)
    (hstep : ∀ t < M, p t = p (t + 1) ∨ SqAdj (p t) (p (t + 1))) (S : Set DyBox)
    (hS : ∀ t ≤ M, ∀ T, IsSqCell m δ (p t) T → T ∈ S) {T₀ : DyBox} (h₀ : IsSqCell m δ (p 0) T₀) :
    ∀ k ≤ M, ∀ T, IsSqCell m δ (p k) T →
      ∃ w : (cellGraph m δ).Walk T₀ T, ∀ x ∈ w.support, x ∈ S := by
  intro k
  induction k with
  | zero =>
    intro _ T hT
    obtain rfl := isSqCell_unique h₀ hT
    exact ⟨.nil, fun x hx => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      exact hx ▸ hS 0 (Nat.zero_le _) _ h₀⟩
  | succ k ih =>
    intro hk T hT
    obtain ⟨T', hT'⟩ := exists_isSqCell hpart hN₀ (hpn k (by omega))
    obtain ⟨w, hw⟩ := ih (by omega) T' hT'
    rcases hstep k (by omega) with he | ha
    · rw [← he] at hT
      obtain rfl := isSqCell_unique hT' hT
      exact ⟨w, hw⟩
    · rcases isSqCell_adj ha hT' hT with e | hadj
      · subst e; exact ⟨w, hw⟩
      · refine ⟨w.concat hadj, fun x hx => ?_⟩
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact hS (k + 1) hk _ hT

/-- A walk whose support lies in a finite set `S` bounds the graph distance by `#S - 1`. -/
lemma edist_add_one_le_card {T T' : DyBox} (w : (cellGraph m δ).Walk T T') (S : Finset DyBox)
    (hw : ∀ x ∈ w.support, x ∈ S) : (cellGraph m δ).edist T T' + 1 ≤ (S.card : ℕ∞) := by
  classical
  set q := w.toPath with hq
  have hsub : ∀ x ∈ (q : (cellGraph m δ).Walk T T').support, x ∈ S := fun x hx =>
    hw x (SimpleGraph.Walk.support_toPath_subset_support w hx)
  have hnd := q.2.support_nodup
  have hlen : (q : (cellGraph m δ).Walk T T').support.length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun x hx => hsub x (List.mem_toFinset.1 hx)
  rw [SimpleGraph.Walk.length_support] at hlen
  calc (cellGraph m δ).edist T T' + 1 ≤ ((q : (cellGraph m δ).Walk T T').length : ℕ∞) + 1 := by
        gcongr; exact SimpleGraph.edist_le _
    _ = (((q : (cellGraph m δ).Walk T T').length + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ (S.card : ℕ∞) := by exact_mod_cast hlen

/-- **The count of a crossing**: a path of squares (equal or 4-adjacent consecutive ones, level
`≥ N₀`) from a square containing `u` to one containing `v`, all of whose cells lie in a finite
set `S`, gives `D'_δ(u, v) ≤ #S`. -/
theorem approxDist_le_card_of_path (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v) {N₀ : ℕ}
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ N₀) (p : ℕ → DyBox) (M : ℕ) (hpn : ∀ t ≤ M, N₀ ≤ (p t).n)
    (hstep : ∀ t < M, p t = p (t + 1) ∨ SqAdj (p t) (p (t + 1))) (S : Finset DyBox)
    (hS : ∀ t ≤ M, ∀ T, IsSqCell m δ (p t) T → T ∈ S) {u v : ℂ}
    (hu0 : (p 0).Mem u) (hvM : (p M).Mem v) : approxDist m δ u v ≤ (S.card : ℕ∞) := by
  obtain ⟨T₀, h₀⟩ := exists_isSqCell hpart hN₀ (hpn 0 (Nat.zero_le _))
  obtain ⟨T₁, h₁⟩ := exists_isSqCell hpart hN₀ (hpn M le_rfl)
  obtain ⟨w, hw⟩ := exists_walk_of_path hpart hN₀ p M hpn hstep S hS h₀ M le_rfl T₁ h₁
  have hT₀ : T₀.Mem u := by
    have := mem_anc hu0 h₀.2.1; rwa [h₀.2.2] at this
  have hT₁ : T₁.Mem v := by
    have := mem_anc hvM h₁.2.1; rwa [h₁.2.2] at this
  unfold approxDist
  refine (iInf_le_of_le T₀ (iInf_le_of_le T₁ (iInf_le_of_le
    (show IsCell m δ _ ∧ _ from ⟨h₀.1, hT₀⟩) (iInf_le_of_le
      (show IsCell m δ _ ∧ _ from ⟨h₁.1, hT₁⟩) le_rfl)))).trans ?_
  exact edist_add_one_le_card w S hw

end DZZ
end LQGMetric
