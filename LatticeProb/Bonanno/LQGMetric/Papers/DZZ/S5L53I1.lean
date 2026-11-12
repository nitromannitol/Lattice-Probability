/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53I1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W10
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W3

/-!
# Walled DZZ Lemma 3.12, step 1: the replacement claim with the position of `𝖢_{i,1}`, `𝖢_{i,2}`
(P2-DZZ53I)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1436–1499:
the cells `𝖢_{i,1}`, `𝖢_{i,2}` where the replacing segment is attached are cells of the
enclosure (eq-percolation-good-surrounding) of `𝖢`, hence meet `𝖢_large` (l. 1467–1470).
`L312CoreR` (S3L12U1) forgets this; **`l312CoreLoc`** is `L312CoreR` with the two extra
conclusions `x, y` meet `𝖢_large`. The proof is the proof of `l312CoreR_of_ring` (S3L12W3) and
`l312CoreRing_holds` (S3L12W10), copied, with `x, y ∈ Z` (resp. `∈ E`) recorded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- **`L312CoreR` with the position of `x`, `y`** (DZZ l. 1462–1499). -/
theorem l312CoreLoc {γ : ℝ} {αs δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {m : DyBox → ℝ}
    (hsize : ∀ b, IsCell m δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ)
    (hring : ∀ C, IsCell m δ C → CellRing m δ (epsStar αs δ) C)
    {u v : ℂ} (hgu : IsGoodPoint m δ (epsStar αs δ) u) (hgv : IsGoodPoint m δ (epsStar αs δ) v)
    {l : List DyBox} (hj : JoinsCells m δ u v l) (hch : l.IsChain Neighbour) (hnd : l.Nodup)
    {C : DyBox} (hC : C ∈ l312Bad (epsStar αs δ) l)
    (hmax : ∀ c ∈ l312Bad (epsStar αs δ) l, c.side ≤ C.side) :
    ∃ (A M B R : List DyBox) (x y : DyBox), l = A ++ x :: (M ++ y :: B) ∧ C ∈ M ∧
      (x :: R ++ [y]).IsChain Neighbour ∧ R.Nodup ∧
      (∀ c ∈ R, IsCell m δ c ∧ epsStar αs δ * C.side ≤ c.side ∧
        (c.closedBox ∩ C.largeBox).Nonempty) ∧
      epsStar αs δ * C.side ≤ x.side ∧ epsStar αs δ * C.side ≤ y.side ∧
      (l312Bad (epsStar αs δ) (x :: R ++ [y])).card ≤ 1 ∧
      (x.closedBox ∩ C.largeBox).Nonempty ∧ (y.closedBox ∩ C.largeBox).Nonempty := by
  set ε := epsStar αs δ
  have hε : 0 < ε := by simp only [ε, epsStar]; positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hCcell : IsCell m δ C := hj.2.1 C (mem_of_mem_l312Bad hC)
  set N := ⌊dzzCmc γ * Real.logb 2 δ⁻¹⌋₊
  have hN : ∀ b, IsCell m δ b → b.n ≤ N := fun b hb =>
    Nat.le_floor (n_le_of_rpow_le_side hδ.1 (hsize b hb).1)
  have hCN := n_add_one_le_of_bad hε1 hN hj.2.1 hC
  by_cases hint : C.largeBox ⊆ interior dzzV
  swap
  · -- the clipped case (`l312CoreR_of_ring`, S3L12W3)
    obtain ⟨E, -, hEch, hEc, henc⟩ := (hring C hCcell).1
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
      (hEc c (hRE c hc)).2.1, hmeet c (hRE c hc)⟩, (hEc x hx).2.1, (hEc y hy).2.1, ?_,
      hmeet x hx, hmeet y hy⟩
    refine card_l312Bad_le_one_of_parents hε (fun c hc => (hEc c (hWE c hc)).2.1) ?_
    intro c hc c' hc' hs hs'
    exact le_one_parent_of_not_interior hint hCcell (hEc c (hWE c hc)).1 (hEc c' (hWE c' hc')).1
      hs hs' (hmeet c (hWE c hc)) (hmeet c' (hWE c' hc'))
  -- the ring case (`l312CoreRing_holds`, S3L12W10)
  obtain ⟨Z, hZne, hZch, hZcyc, hZc, hZenc, hZcount⟩ := (hring C hCcell).2 hint
  have hZcells : ∀ c ∈ Z, IsCell m δ c := fun c hc => (hZc c hc).1
  have hZmeet : ∀ c ∈ Z, (c.closedBox ∩ C.largeBox).Nonempty := fun c hc =>
    (hZc c hc).2.2.mono (inter_subset_inter_right _ sdiff_subset)
  obtain ⟨A, M, B, x, y, hl, hCM, hx, hy, hM⟩ := exists_enc_split hN hε1 hgu hgv hj hch hC hCN
    (fun c hc => ⟨(hZc c hc).1, (hZc c hc).2.2⟩) hZenc
  have hxy : x ≠ y := by
    rintro rfl
    have h2 : (x :: (M ++ x :: B)).Nodup := (hl ▸ hnd).sublist (List.sublist_append_right A _)
    exact (List.nodup_cons.1 h2).1 (by simp)
  obtain ⟨w, hwi, hwZ, hwc, hws, hwL⟩ :=
    succ_small hN hCcell hCN hZcells hZenc hch hj.2.1 hl hCM hM
  obtain ⟨w', hwi', hwZ', hwc', hws', hwL'⟩ :=
    pred_small hN hCcell hCN hZcells hZenc hch hj.2.1 hl hCM hM
  have hxw : Neighbour x w := List.isChain_pair.1 (hch.infix hwi)
  have hw'y : Neighbour w' y := List.isChain_pair.1 (hch.infix hwi')
  have hxs := (hZc x hx).2.1
  have hys := (hZc y hy).2.1
  have finish : ∀ R : List DyBox, (x :: R ++ [y]).IsChain Neighbour → (∀ c ∈ R, c ∈ Z) →
      LeOneParent C (x :: R ++ [y]) →
      ∃ (A M B R : List DyBox) (x' y' : DyBox), l = A ++ x' :: (M ++ y' :: B) ∧ C ∈ M ∧
        (x' :: R ++ [y']).IsChain Neighbour ∧ R.Nodup ∧
        (∀ c ∈ R, IsCell m δ c ∧ ε * C.side ≤ c.side ∧ (c.closedBox ∩ C.largeBox).Nonempty) ∧
        ε * C.side ≤ x'.side ∧ ε * C.side ≤ y'.side ∧ (l312Bad ε (x' :: R ++ [y'])).card ≤ 1 ∧
        (x'.closedBox ∩ C.largeBox).Nonempty ∧ (y'.closedBox ∩ C.largeBox).Nonempty := by
    intro R hR hRZ hpar
    have hEZ : ∀ c ∈ x :: R ++ [y], c ∈ Z := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | hc | rfl
      · exact hx
      · exact hRZ c hc
      · exact hy
    obtain ⟨R', hR'ch, hR'nd, hR'E⟩ := exists_enc_path (E := x :: R ++ [y])
      (hR.imp fun a b h => Or.inr h) (fun c hc => hZcells c (hEZ c hc)) (by simp) (by simp) hxy
    have hsub : ∀ c ∈ x :: R' ++ [y], c ∈ x :: R ++ [y] := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | hc | rfl
      · simp
      · exact hR'E c hc
      · simp
    have hR'nd' : R'.Nodup := by
      have := (List.nodup_cons.1 (by simpa using hR'nd : (x :: (R' ++ [y])).Nodup)).2
      exact this.sublist (List.sublist_append_left R' [y])
    refine ⟨A, M, B, R', x, y, hl, hCM, hR'ch, hR'nd', fun c hc => ?_, hxs, hys, ?_,
      hZmeet x hx, hZmeet y hy⟩
    · have hcZ := hEZ c (hR'E c hc)
      exact ⟨hZcells c hcZ, (hZc c hcZ).2.1, hZmeet c hcZ⟩
    · refine card_l312Bad_le_one_of_parents hε (fun c hc => (hZc c (hEZ c (hsub c hc))).2.1) ?_
      intro c hc c' hc' hs hs'
      exact hpar c (hsub c hc) c' (hsub c' hc') hs hs'
  by_cases hboth : C.side < x.side ∧ C.side < y.side
  · have hxP : IsParent m δ C x := ⟨hZcells x hx, hboth.1, hZmeet x hx⟩
    have hyP : IsParent m δ C y := ⟨hZcells y hy, hboth.2, hZmeet y hy⟩
    have hxε : ε * x.side ≤ C.side := by
      by_contra hlt; push Not at hlt
      have := hmax x (mem_l312Bad_of_pair (Or.inl hwi) (lt_of_le_of_lt hws hlt))
      linarith [hboth.1]
    have hyε : ε * y.side ≤ C.side := by
      by_contra hlt; push Not at hlt
      have := hmax y (mem_l312Bad_of_pair (Or.inr hwi') (lt_of_le_of_lt hws' hlt))
      linarith [hboth.2]
    rcases parents_nbr hCcell hxP hyP hxy with hn | ⟨hxC, hCy⟩
    · refine ⟨A, M, B, [], x, y, hl, hCM, by simpa using hn, List.nodup_nil, by simp, hxs,
        hys, ?_, hZmeet x hx, hZmeet y hy⟩
      simpa using card_l312Bad_case3_adj hε1 (x := x) (y := y)
    · refine ⟨A, M, B, [C], x, y, hl, hCM, ?_, List.nodup_singleton _, ?_, hxs, hys, ?_,
        hZmeet x hx, hZmeet y hy⟩
      · simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
          List.isChain_singleton, and_true]
        exact ⟨hxC, hCy⟩
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨hCcell, mul_le_of_le_one_left c.side_pos'.le hε1,
          ⟨c.center, center_mem_closedBox' c, mem_largeBox_of_mem_self (center_mem_closedBox' c)⟩⟩
      · have := l312Bad_case3_diag hε1 hboth.1.le hboth.2.le hxε hyε
        simp [this]
  · have hcyc : ∀ a ∈ Z.getLast?, ∀ b ∈ Z.head?, Neighbour a b := by
      intro a ha b hb
      rw [List.getLast?_eq_some_getLast hZne, Option.mem_def, Option.some.injEq] at ha
      rw [List.head?_eq_some_head hZne, Option.mem_def, Option.some.injEq] at hb
      subst ha hb
      exact hZcyc
    obtain ⟨R₁, R₂, hW₁, hW₂, hperm⟩ := exists_arcs ⟨hZch, hcyc⟩ hx hy hxy
    have hR1Z : ∀ c ∈ R₁, c ∈ Z := fun c hc => hperm.subset (by simp [hc])
    have hR2Z : ∀ c ∈ R₂, c ∈ Z := fun c hc => hperm.subset (by simp [hc])
    rcases pick_arc hCcell hW₁ hW₂ hperm (fun c hc => ⟨hZcells c hc, hZmeet c hc⟩) hZcount hxy
      hxw hwc hwL hwZ hw'y hwc' hwL' hwZ' hboth with h | h
    · exact finish R₁ hW₁ hR1Z h
    · exact finish R₂ hW₂ hR2Z h

end DZZ
end LQGMetric
