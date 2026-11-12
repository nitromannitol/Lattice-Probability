/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53I2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T2

/-!
# Walled DZZ Lemma 3.12, step 2: the localized surgery step (P2-DZZ53I)

DZZ arXiv:1807.00422, proof of Lemma 3.12, l. 1436–1499. Copies (credited) of
`l312_loop_erase` (S3L12T1) and `l312_splice` (S3L12T2) that also record where the cells of the
new chain come from (`l312_loop_eraseMem`, `l312_spliceLoc`), and **`l312StepLoc`**: one
surgery step preserves the localization invariant
* every cell is within `ρ` of `K` (`L53Near K ρ`), and
* every bad cell `b` is within `4 s_b` of `K`,
as long as `8 δ^{C_Mc} ≤ ρ` (own elementary argument: the cells added around the bad cell `𝖢`
meet `𝖢_large`, and a newly bad cell has side `≥ 2 s_𝖢`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

theorem l312_loop_eraseMem {ε : ℝ} {u v : ℂ} {L : List DyBox} (hj : JoinsCells m δ u v L)
    (hch : L.IsChain Neighbour) :
    ∃ L' : List DyBox, JoinsCells m δ u v L' ∧ L'.IsChain Neighbour ∧ L'.Nodup ∧
      L'.length ≤ L.length ∧ l312Bad ε L' ⊆ l312Bad ε L ∧ ∀ c ∈ L', c ∈ L := by
  obtain ⟨hne, hcells, hhead, hlast⟩ := hj
  obtain ⟨p, hp⟩ := exists_walk_of_isChain L hne (isChain_cellGraph_of L hch hcells)
  set q := p.bypass
  have hsub : ∀ c ∈ q.support, c ∈ L := fun c hc => hp ▸ p.support_bypass_subset_support hc
  refine ⟨q.support, ⟨by simp, fun c hc => hcells c (hsub c hc), ?_, ?_⟩,
    (SimpleGraph.Walk.isChain_adj_support q).imp fun a b h => h.2.2,
    (p.bypass_isPath).support_nodup, ?_, ?_, hsub⟩
  · rw [SimpleGraph.Walk.head_support]; exact hhead
  · rw [SimpleGraph.Walk.getLast_support]; exact hlast
  · have h1 := congrArg List.length hp
    rw [SimpleGraph.Walk.length_support] at h1
    rw [SimpleGraph.Walk.length_support]
    have : q.length ≤ p.length := SimpleGraph.Walk.length_bypass_le_length p
    omega
  · refine l312Bad_mono hsub fun a b h => ?_
    rw [← hp]
    exact pair_of_edge_support p (p.edges_bypass_subset_edges (edge_of_pair_support q h))


theorem l312_spliceLoc {ε : ℝ} {u v : ℂ} {l A M B R : List DyBox} {x y C : DyBox}
    (hj : JoinsCells m δ u v l) (hch : l.IsChain Neighbour) (hnd : l.Nodup)
    (hC : C ∈ l312Bad ε l) (hmax : ∀ c ∈ l312Bad ε l, c.side ≤ C.side)
    (hl : l = A ++ x :: (M ++ y :: B)) (hCM : C ∈ M)
    (hW : (x :: R ++ [y]).IsChain Neighbour) (hR : ∀ c ∈ R, IsCell m δ c)
    (hCW : C ∉ l312Bad ε (x :: R ++ [y]))
    (hD1 : (l312Bad ε (x :: R ++ [y]) \ l312Bad ε l).card ≤ 1)
    (hD2 : ∀ c ∈ l312Bad ε (x :: R ++ [y]) \ l312Bad ε l, 2 * C.side ≤ c.side) :
    ∃ l' : List DyBox, JoinsCells m δ u v l' ∧ l'.IsChain Neighbour ∧ l'.Nodup ∧
      l'.length ≤ l.length + R.length ∧ L312Progress ε l l' ∧
      (∀ c ∈ l', c ∈ l ∨ c ∈ x :: R ++ [y]) ∧
      l312Bad ε l' ⊆ (l312Bad ε l).erase C ∪ (l312Bad ε (x :: R ++ [y]) \ l312Bad ε l) := by
  set W := x :: R ++ [y] with hWdef
  set L := A ++ x :: (R ++ y :: B) with hLdef
  set D := l312Bad ε W \ l312Bad ε l
  have hMne : M ≠ [] := List.ne_nil_of_mem hCM
  -- the untouched parts are infixes of `l`
  have hIA : A ++ [x] <:+: l := by
    rw [hl]
    have : A ++ x :: (M ++ y :: B) = (A ++ [x]) ++ (M ++ y :: B) := by simp
    rw [this]; exact (List.prefix_append _ _).isInfix
  have hIB : y :: B <:+: l := by
    rw [hl]
    have : A ++ x :: (M ++ y :: B) = (A ++ x :: M) ++ y :: B := by simp
    rw [this]; exact (List.suffix_append _ _).isInfix
  -- `𝖢` is not in the untouched parts
  have hCA : ∀ c ∈ A ++ [x], c ≠ C := by
    intro c hc
    have e : l = (A ++ [x]) ++ (M ++ y :: B) := by rw [hl]; simp
    rw [e] at hnd
    exact (List.nodup_append.1 hnd).2.2 c hc C (List.mem_append_left _ hCM)
  have hCB : ∀ c ∈ y :: B, c ≠ C := by
    intro c hc
    have e : l = (A ++ x :: M) ++ (y :: B) := by rw [hl]; simp
    rw [e] at hnd
    exact ((List.nodup_append.1 hnd).2.2 C (by simp [hCM]) c hc).symm
  -- adjacent pairs of the spliced chain
  have hpair : ∀ a b, [a, b] <:+: L → [a, b] <:+: A ++ [x] ∨ [a, b] <:+: W ∨ [a, b] <:+: y :: B := by
    intro a b h
    rcases pair_append_cons A (R ++ y :: B) h with h | h
    · exact Or.inl h
    · have e : x :: (R ++ y :: B) = (x :: R) ++ y :: B := by simp
      rw [e] at h
      rcases pair_append_cons (x :: R) B h with h | h
      · right; left; simpa [hWdef] using h
      · exact Or.inr (Or.inr h)
  -- the bad cells of the spliced chain
  have hbad : l312Bad ε L ⊆ (l312Bad ε l).erase C ∪ D := by
    intro c hc
    obtain ⟨-, c', hp, hs⟩ := exists_pair_of_mem_l312Bad hc
    have key : ∃ P, (P = A ++ [x] ∨ P = W ∨ P = y :: B) ∧ ([c, c'] <:+: P ∨ [c', c] <:+: P) := by
      rcases hp with h | h
      · rcases hpair _ _ h with h | h | h
        · exact ⟨_, Or.inl rfl, Or.inl h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), Or.inl h⟩
        · exact ⟨_, Or.inr (Or.inr rfl), Or.inl h⟩
      · rcases hpair _ _ h with h | h | h
        · exact ⟨_, Or.inl rfl, Or.inr h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), Or.inr h⟩
        · exact ⟨_, Or.inr (Or.inr rfl), Or.inr h⟩
    obtain ⟨P, hP, hcP⟩ := key
    have hmemP : c ∈ P := by
      rcases hcP with h | h
      · exact infix_mem_left h
      · exact infix_mem_right h
    have hlift : ∀ Q : List DyBox, P <:+: Q → c ∈ l312Bad ε Q := fun Q hQ => by
      refine mem_l312Bad_of_pair ?_ hs
      rcases hcP with h | h
      · exact Or.inl (h.trans hQ)
      · exact Or.inr (h.trans hQ)
    rw [Finset.mem_union, Finset.mem_erase]
    rcases hP with rfl | rfl | rfl
    · exact Or.inl ⟨hCA c hmemP, hlift l hIA⟩
    · have hcW := hlift W (List.infix_refl _)
      by_cases hcl : c ∈ l312Bad ε l
      · exact Or.inl ⟨fun e => hCW (e ▸ hcW), hcl⟩
      · exact Or.inr (Finset.mem_sdiff.2 ⟨hcW, hcl⟩)
    · exact Or.inl ⟨hCB c hmemP, hlift l hIB⟩
  -- the spliced chain joins `u` and `v`
  obtain ⟨hne, hcells, hhead, hlast⟩ := hj
  have hLne : L ≠ [] := by simp [hLdef]
  have hjL : JoinsCells m δ u v L := by
    refine ⟨hLne, fun c hc => ?_, ?_, ?_⟩
    · simp only [hLdef, List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc | rfl | hc
      · exact hcells c (hIA.subset (by simp [hc]))
      · exact hcells c (hIA.subset (by simp))
      · exact hR c hc
      · exact hcells c (hIB.subset (by simp))
      · exact hcells c (hIB.subset (by simp [hc]))
    · have e := head_append_cons_eq A (R ++ y :: B) (M ++ y :: B) x hLne (hl ▸ hne)
      rw [e]; convert hhead using 2; simp only [hl]
    · have e1 : L = (A ++ x :: R) ++ y :: B := by simp [hLdef]
      have e2 : l = (A ++ x :: M) ++ y :: B := by rw [hl]; simp
      have h1 : L.getLast hLne = ((A ++ x :: R) ++ y :: B).getLast (by simp) := by
        simp only [e1]
      have h2 : l.getLast hne = ((A ++ x :: M) ++ y :: B).getLast (by simp) := by
        simp only [e2]
      rw [h1, getLast_append_cons_eq _ (A ++ x :: M) B y _ (by simp), ← h2]
      exact hlast
  -- the spliced chain is a `Neighbour`-chain
  have hchL : L.IsChain Neighbour := by
    have c1 : (A ++ [x]).IsChain Neighbour := hch.infix hIA
    have c2 : ([x] ++ (R ++ [y])).IsChain Neighbour := by simpa [hWdef] using hW
    have c3 := c1.append_overlap c2 (by simp)
    have c4 : ((A ++ x :: R) ++ [y]).IsChain Neighbour := by simpa using c3
    have c5 : ([y] ++ B).IsChain Neighbour := by simpa using hch.infix hIB
    have c6 := c4.append_overlap c5 (by simp)
    simpa [hLdef] using c6
  -- loop erasure
  obtain ⟨l', hj', hch', hnd', hlen', hsub', hmem'⟩ := l312_loop_eraseMem (ε := ε) hjL hchL
  refine ⟨l', hj', hch', hnd', ?_, ?_, ?_, hsub'.trans hbad⟩
  rotate_right
  · intro c hc
    have hcL := hmem' c hc
    simp only [hLdef, List.mem_append, List.mem_cons] at hcL
    rcases hcL with hc | rfl | hc | rfl | hc
    · exact Or.inl (hIA.subset (by simp [hc]))
    · exact Or.inr (by rw [hWdef]; simp)
    · exact Or.inr (by rw [hWdef]; simp [hc])
    · exact Or.inr (by rw [hWdef]; simp)
    · exact Or.inl (hIB.subset (by simp [hc]))
  · have : L.length ≤ l.length + R.length := by
      rw [hl, hLdef]
      have := List.length_pos_iff.2 hMne
      simp only [List.length_append, List.length_cons]; omega
    omega
  -- (i) or (ii)
  have hCcard : ((l312Bad ε l).erase C).card + 1 = (l312Bad ε l).card :=
    Finset.card_erase_add_one hC
  by_cases hd : ∃ d ∈ D, d ∈ l312Bad ε l'
  · obtain ⟨d, hdD, hdl'⟩ := hd
    right
    refine ⟨?_, d, hdl', fun c hc => ?_⟩
    · calc (l312Bad ε l').card ≤ ((l312Bad ε l).erase C ∪ D).card :=
            Finset.card_le_card (hsub'.trans hbad)
        _ ≤ ((l312Bad ε l).erase C).card + D.card := Finset.card_union_le _ _
        _ ≤ (l312Bad ε l).card := by omega
    · have := hmax c hc; have := hD2 d hdD; linarith
  · left
    have hs : l312Bad ε l' ⊆ (l312Bad ε l).erase C := by
      intro c hc
      rcases Finset.mem_union.1 (hbad (hsub' hc)) with h | h
      · exact h
      · exact absurd ⟨c, h, hc⟩ hd
    have := Finset.card_le_card hs
    omega


end DZZ
end LQGMetric
