/-
# Flattening simple polygonal pieces into a simple polygonal ray

Let `L 0, L 1, …` be geometrically simple finite polygonal chains with at least two vertices each, each
ending where the next one starts, such that consecutive pieces meet only at their common vertex and pieces
two or more steps apart are disjoint. Concatenating them gives a simple polygonal ray: a vertex sequence `v`
with consecutive vertices distinct, consecutive edges meeting only at their common vertex and edges two or
more steps apart disjoint. Every edge lies on the union of the pieces, and for every `N` all late vertices
lie on pieces of index at least `N`.

The proof goes through the finite concatenations `L 0 ++ (L 1).tail ++ ⋯ ++ (L n).tail`, which are
geometrically simple and each a prefix of the next; the ray reads its `m`-th vertex off any of them that is
long enough.
-/
import LatticeProb.Topology.SimplePolygonalChain

open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Edges of a finite chain -/

/-- Every edge of a polygonal chain lies on its trace. -/
theorem segment_getElem_subset_polygonalChain : ∀ (vs : List E) (k : ℕ) (hk : k + 1 < vs.length),
    segment ℝ vs[k] vs[k + 1] ⊆ polygonalChain vs
  | [], _, hk => by simp at hk
  | [_], _, hk => by simp at hk
  | a :: b :: rest, 0, _ => by
    rw [polygonal_chain_cons_cons]
    exact subset_union_left
  | a :: b :: rest, k + 1, hk => by
    rw [polygonal_chain_cons_cons]
    exact (segment_getElem_subset_polygonalChain (b :: rest) k
      (by simp only [List.length_cons] at hk ⊢; omega)).trans subset_union_right

/-- Every point of a polygonal chain with at least two vertices lies on one of its edges. -/
theorem exists_mem_segment_getElem_of_mem_polygonalChain : ∀ {vs : List E}, 2 ≤ vs.length →
    ∀ {p : E}, p ∈ polygonalChain vs → ∃ k, ∃ hk : k + 1 < vs.length, p ∈ segment ℝ vs[k] vs[k + 1]
  | [], h, _, _ => by simp at h
  | [_], h, _, _ => by simp at h
  | [a, b], _, p, hp => by
    rw [polygonal_chain_cons_cons, polygonal_chain_singleton] at hp
    rcases hp with hp | hp
    · exact ⟨0, by simp, hp⟩
    · rw [mem_singleton_iff.mp hp]
      exact ⟨0, by simp, right_mem_segment ℝ a b⟩
  | a :: b :: c :: rest, _, p, hp => by
    rw [polygonal_chain_cons_cons] at hp
    rcases hp with hp | hp
    · exact ⟨0, by simp, hp⟩
    · obtain ⟨k, hk, hpk⟩ :=
        exists_mem_segment_getElem_of_mem_polygonalChain (vs := b :: c :: rest) (by simp) hp
      exact ⟨k + 1, by simp only [List.length_cons] at hk ⊢; omega, hpk⟩

/-! ### Index facts for geometrically simple chains -/

/-- The first vertex of a geometrically simple chain is not on the chain starting at its second vertex. -/
theorem IsSimplePolygonalChain.head_notMem_polygonalChain_tail {a b : E} {rest : List E}
    (h : IsSimplePolygonalChain (a :: b :: rest)) : a ∉ polygonalChain (b :: rest) := by
  intro ha
  have hab : a ∈ segment ℝ a b ∩ polygonalChain (b :: rest) := ⟨left_mem_segment ℝ a b, ha⟩
  rw [h.2.2] at hab
  exact h.1 hab

/-- Consecutive vertices of a geometrically simple chain are distinct. -/
theorem IsSimplePolygonalChain.getElem_ne_getElem_succ : ∀ {vs : List E}, IsSimplePolygonalChain vs →
    ∀ (k : ℕ) (hk : k + 1 < vs.length), vs[k] ≠ vs[k + 1]
  | [], h, _, _ => h.elim
  | [_], _, _, hk => by simp at hk
  | _ :: _ :: _, h, 0, _ => h.1
  | _ :: b :: rest, h, k + 1, hk =>
    h.2.1.getElem_ne_getElem_succ k (by simp only [List.length_cons] at hk ⊢; omega)

/-- Consecutive edges of a geometrically simple chain meet only at their common vertex. -/
theorem IsSimplePolygonalChain.segment_inter_segment_succ_subset : ∀ {vs : List E},
    IsSimplePolygonalChain vs → ∀ (k : ℕ) (hk : k + 2 < vs.length),
      segment ℝ vs[k] vs[k + 1] ∩ segment ℝ vs[k + 1] vs[k + 2] ⊆ {vs[k + 1]}
  | [], h, _, _ => h.elim
  | [_], _, _, hk => by simp at hk
  | a :: b :: rest, h, 0, hk => by
    intro p hp
    exact h.2.2.subset ⟨hp.1, segment_getElem_subset_polygonalChain (b :: rest) 0
      (by simp only [List.length_cons] at hk ⊢; omega) hp.2⟩
  | _ :: b :: rest, h, k + 1, hk =>
    h.2.1.segment_inter_segment_succ_subset k (by simp only [List.length_cons] at hk ⊢; omega)

/-- Edges two or more steps apart in a geometrically simple chain are disjoint. -/
theorem IsSimplePolygonalChain.disjoint_segment_getElem : ∀ {vs : List E},
    IsSimplePolygonalChain vs → ∀ (k k' : ℕ) (hkk' : k + 2 ≤ k') (hk' : k' + 1 < vs.length),
      Disjoint (segment ℝ (vs[k]'(by omega)) (vs[k + 1]'(by omega))) (segment ℝ vs[k'] vs[k' + 1])
  | [], h, _, _, _, _ => h.elim
  | [_], _, _, _, _, hk' => by simp at hk'
  | [_, _], _, _, _, hkk', hk' => by simp only [List.length_cons, List.length_nil] at hk'; omega
  | a :: b :: c :: rest, h, 0, k', hkk', hk' => by
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 2 := ⟨k' - 2, by omega⟩
    rw [Set.disjoint_left]
    intro p hp hp'
    have hpc : p ∈ polygonalChain (c :: rest) :=
      segment_getElem_subset_polygonalChain (c :: rest) j
        (by simp only [List.length_cons] at hk' ⊢; omega) hp'
    have hpb : p ∈ polygonalChain (b :: c :: rest) := by
      rw [polygonal_chain_cons_cons]
      exact Or.inr hpc
    have hpeq : p = b := h.2.2.subset ⟨hp, hpb⟩
    rw [hpeq] at hpc
    exact h.2.1.head_notMem_polygonalChain_tail hpc
  | _ :: b :: rest, h, k + 1, k', hkk', hk' => by
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    exact h.2.1.disjoint_segment_getElem k j (by omega)
      (by simp only [List.length_cons] at hk' ⊢; omega)

/-! ### Concatenation at a common vertex -/

/-- The trace of two chains glued at a common vertex is the union of their traces. -/
theorem polygonalChain_append_tail : ∀ {vs : List E} (hv : vs ≠ []) {ws : List E} (hw : ws ≠ []),
    vs.getLast hv = ws.head hw →
      polygonalChain (vs ++ ws.tail) = polygonalChain vs ∪ polygonalChain ws
  | [], hv, _, _, _ => absurd rfl hv
  | [a], _, [], hw, _ => absurd rfl hw
  | [a], _, w :: ws, _, hj => by
    change a = w at hj
    subst hj
    change polygonalChain (a :: ws) = {a} ∪ polygonalChain (a :: ws)
    exact (union_eq_right.mpr
      (singleton_subset_iff.mpr (head_mem_polygonal_chain (List.cons_ne_nil a ws)))).symm
  | a :: b :: rest, _, ws, hw, hj => by
    have ih : polygonalChain ((b :: rest) ++ ws.tail) = polygonalChain (b :: rest) ∪ polygonalChain ws :=
      polygonalChain_append_tail (List.cons_ne_nil b rest) hw (by rw [← hj, List.getLast_cons_cons])
    change polygonalChain (a :: b :: (rest ++ ws.tail)) = polygonalChain (a :: b :: rest) ∪ polygonalChain ws
    rw [polygonal_chain_cons_cons, polygonal_chain_cons_cons, union_assoc]
    exact congrArg (segment ℝ a b ∪ ·) ih

/-- Gluing two geometrically simple chains at a common vertex, where they meet only at that vertex, gives
a geometrically simple chain. -/
theorem IsSimplePolygonalChain.append_tail : ∀ {vs : List E} (hs : IsSimplePolygonalChain vs)
    {ws : List E} (ht : IsSimplePolygonalChain ws),
    vs.getLast hs.ne_nil = ws.head ht.ne_nil →
    polygonalChain vs ∩ polygonalChain ws ⊆ {ws.head ht.ne_nil} →
    IsSimplePolygonalChain (vs ++ ws.tail)
  | [], hs, _, _, _, _ => hs.elim
  | [_], _, [], ht, _, _ => ht.elim
  | [a], _, w :: ws, ht, hj, _ => by
    change a = w at hj
    subst hj
    exact ht
  | a :: b :: rest, hs, ws, ht, hj, hmeet => by
    have hj' : (b :: rest).getLast hs.2.1.ne_nil = ws.head ht.ne_nil := by
      rw [← hj, List.getLast_cons_cons]
    have hsub : polygonalChain (b :: rest) ⊆ polygonalChain (a :: b :: rest) := by
      rw [polygonal_chain_cons_cons]
      exact subset_union_right
    have ih : IsSimplePolygonalChain ((b :: rest) ++ ws.tail) :=
      hs.2.1.append_tail ht hj' fun p hp => hmeet ⟨hsub hp.1, hp.2⟩
    change a ≠ b ∧ IsSimplePolygonalChain ((b :: rest) ++ ws.tail) ∧
      segment ℝ a b ∩ polygonalChain ((b :: rest) ++ ws.tail) = {b}
    refine ⟨hs.1, ih, ?_⟩
    rw [polygonalChain_append_tail hs.2.1.ne_nil ht.ne_nil hj', inter_union_distrib_left, hs.2.2]
    refine union_eq_left.mpr ?_
    rintro p ⟨hpab, hpw⟩
    have hp1 : p = ws.head ht.ne_nil := hmeet ⟨by
      rw [polygonal_chain_cons_cons]
      exact Or.inl hpab, hpw⟩
    have hp2 : p ∈ polygonalChain (b :: rest) := by
      rw [hp1, ← hj']
      exact getLast_mem_polygonal_chain _
    exact hs.2.2.subset ⟨hpab, hp2⟩

/-! ### Finite concatenations of pieces -/

/-- The concatenation `L 0 ++ (L 1).tail ++ ⋯ ++ (L n).tail` of the first `n + 1` pieces, each piece after
the first entered without its first vertex. -/
def piecesConcat {α : Type*} (L : ℕ → List α) : ℕ → List α
  | 0 => L 0
  | n + 1 => piecesConcat L n ++ (L (n + 1)).tail

/-- Each finite concatenation of pieces is a prefix of the later ones. -/
theorem piecesConcat_prefix {α : Type*} (L : ℕ → List α) {m n : ℕ} (hmn : m ≤ n) :
    piecesConcat L m <+: piecesConcat L n := by
  induction n, hmn using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (List.prefix_append _ _)

/-- If every piece has at least two vertices, the concatenation of the first `n + 1` pieces has at least
`n + 2` vertices. -/
theorem le_length_piecesConcat {α : Type*} {L : ℕ → List α} (hlen : ∀ n, 2 ≤ (L n).length) :
    ∀ n, n + 2 ≤ (piecesConcat L n).length
  | 0 => hlen 0
  | n + 1 => by
    have h1 := le_length_piecesConcat hlen n
    have h2 := hlen (n + 1)
    simp only [piecesConcat, List.length_append, List.length_tail]
    omega

/-- The concatenation of the first `n + 1` pieces is geometrically simple, ends at the last vertex of
`L n`, and its trace is the union of the traces of `L 0, …, L n`. -/
theorem piecesConcat_spec (L : ℕ → List E) (hL : ∀ n, IsSimplePolygonalChain (L n))
    (hlen : ∀ n, 2 ≤ (L n).length)
    (hjoin : ∀ n, (L n).getLast (hL n).ne_nil = (L (n + 1)).head (hL (n + 1)).ne_nil)
    (hnext : ∀ n, polygonalChain (L n) ∩ polygonalChain (L (n + 1)) ⊆
      {(L (n + 1)).head (hL (n + 1)).ne_nil})
    (hfar : ∀ n m, n + 2 ≤ m → Disjoint (polygonalChain (L n)) (polygonalChain (L m))) :
    ∀ n, ∃ hs : IsSimplePolygonalChain (piecesConcat L n),
      (piecesConcat L n).getLast hs.ne_nil = (L n).getLast (hL n).ne_nil ∧
      ∀ p, p ∈ polygonalChain (piecesConcat L n) ↔ ∃ j ≤ n, p ∈ polygonalChain (L j)
  | 0 => ⟨hL 0, rfl, fun p => ⟨fun hp => ⟨0, le_rfl, hp⟩, fun ⟨j, hj, hp⟩ => by
      rw [Nat.le_zero.mp hj] at hp
      exact hp⟩⟩
  | n + 1 => by
    obtain ⟨hs, hlast, hmem⟩ := piecesConcat_spec L hL hlen hjoin hnext hfar n
    have hj : (piecesConcat L n).getLast hs.ne_nil = (L (n + 1)).head (hL (n + 1)).ne_nil :=
      hlast.trans (hjoin n)
    have htail : (L (n + 1)).tail ≠ [] := by
      intro h
      have h1 := congrArg List.length h
      simp only [List.length_tail, List.length_nil] at h1
      have h2 := hlen (n + 1)
      omega
    have hmeet : polygonalChain (piecesConcat L n) ∩ polygonalChain (L (n + 1)) ⊆
        {(L (n + 1)).head (hL (n + 1)).ne_nil} := by
      rintro p ⟨hp, hp'⟩
      obtain ⟨j, hjn, hpj⟩ := (hmem p).mp hp
      rcases Nat.lt_or_eq_of_le hjn with hlt | rfl
      · exact absurd hp' (Set.disjoint_left.mp (hfar j (n + 1) (by omega)) hpj)
      · exact hnext j ⟨hpj, hp'⟩
    have hs' : IsSimplePolygonalChain (piecesConcat L (n + 1)) :=
      hs.append_tail (hL (n + 1)) hj hmeet
    refine ⟨hs', ?_, fun p => ?_⟩
    · have h3 : ∀ (l : List E) (hl : l ≠ []), l = piecesConcat L n ++ (L (n + 1)).tail →
          l.getLast hl = (L (n + 1)).getLast (hL (n + 1)).ne_nil := by
        rintro l hl rfl
        rw [List.getLast_append_of_ne_nil _ htail, List.getLast_tail]
      exact h3 _ _ rfl
    · change p ∈ polygonalChain (piecesConcat L n ++ (L (n + 1)).tail) ↔ _
      rw [polygonalChain_append_tail hs.ne_nil (hL (n + 1)).ne_nil hj, mem_union, hmem]
      constructor
      · rintro (⟨j, hj, hp⟩ | hp)
        · exact ⟨j, by omega, hp⟩
        · exact ⟨n + 1, le_rfl, hp⟩
      · rintro ⟨j, hj, hp⟩
        rcases Nat.lt_or_eq_of_le hj with hlt | rfl
        · exact Or.inl ⟨j, by omega, hp⟩
        · exact Or.inr hp

/-! ### The flattened ray -/

/-- **Flattening simple pieces into a simple polygonal ray.** Let `L 0, L 1, …` be geometrically simple
finite polygonal chains with at least two vertices each, each ending where the next one starts, such that
consecutive pieces meet only at their common vertex and pieces two or more steps apart are disjoint. Then
there is a vertex sequence `v` with consecutive vertices distinct, consecutive edges meeting only at their
common vertex and edges two or more steps apart disjoint, whose edges lie on the union of the pieces and
whose vertices eventually lie on pieces of index at least `N`, for every `N`. -/
theorem exists_simple_ray_of_simple_pieces (L : ℕ → List E) (hL : ∀ n, IsSimplePolygonalChain (L n))
    (hlen : ∀ n, 2 ≤ (L n).length)
    (hjoin : ∀ n, (L n).getLast (hL n).ne_nil = (L (n + 1)).head (hL (n + 1)).ne_nil)
    (hnext : ∀ n, polygonalChain (L n) ∩ polygonalChain (L (n + 1)) ⊆
      {(L (n + 1)).head (hL (n + 1)).ne_nil})
    (hfar : ∀ n m, n + 2 ≤ m → Disjoint (polygonalChain (L n)) (polygonalChain (L m))) :
    ∃ v : ℕ → E, (∀ n, v n ≠ v (n + 1)) ∧
      (∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)}) ∧
      (∀ n m, n + 2 ≤ m → Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1)))) ∧
      (∀ n, segment ℝ (v n) (v (n + 1)) ⊆ ⋃ j, polygonalChain (L j)) ∧
      ∀ N, ∃ k, ∀ m, k ≤ m → ∃ j, N ≤ j ∧ v m ∈ polygonalChain (L j) := by
  have hPlen : ∀ n, n + 2 ≤ (piecesConcat L n).length := le_length_piecesConcat hlen
  have hspec := piecesConcat_spec L hL hlen hjoin hnext hfar
  obtain ⟨v, hv⟩ : ∃ v : ℕ → E, ∀ N m (hm : m < (piecesConcat L N).length),
      v m = (piecesConcat L N)[m] := by
    refine ⟨fun m => (piecesConcat L m)[m]'(by have := hPlen m; omega), fun N m hm => ?_⟩
    have h1 := (piecesConcat_prefix L (le_max_left m N)).getElem
      (show m < (piecesConcat L m).length by have := hPlen m; omega)
    have h2 := (piecesConcat_prefix L (le_max_right m N)).getElem hm
    exact h1.trans h2.symm
  refine ⟨v, fun n => ?_, fun n => ?_, fun n m hnm => ?_, fun n => ?_, fun N => ?_⟩
  · obtain ⟨hs, -, -⟩ := hspec (n + 1)
    have hl := hPlen (n + 1)
    rw [hv (n + 1) n (by omega), hv (n + 1) (n + 1) (by omega)]
    exact hs.getElem_ne_getElem_succ n (by omega)
  · obtain ⟨hs, -, -⟩ := hspec (n + 2)
    have hl := hPlen (n + 2)
    rw [hv (n + 2) n (by omega), hv (n + 2) (n + 1) (by omega), hv (n + 2) (n + 2) (by omega)]
    exact hs.segment_inter_segment_succ_subset n (by omega)
  · obtain ⟨hs, -, -⟩ := hspec (m + 1)
    have hl := hPlen (m + 1)
    rw [hv (m + 1) n (by omega), hv (m + 1) (n + 1) (by omega), hv (m + 1) m (by omega),
      hv (m + 1) (m + 1) (by omega)]
    exact hs.disjoint_segment_getElem n m hnm (by omega)
  · obtain ⟨-, -, hmem⟩ := hspec (n + 1)
    have hl := hPlen (n + 1)
    rw [hv (n + 1) n (by omega), hv (n + 1) (n + 1) (by omega)]
    intro p hp
    obtain ⟨j, -, hpj⟩ := (hmem p).mp (segment_getElem_subset_polygonalChain _ n (by omega) hp)
    exact mem_iUnion.mpr ⟨j, hpj⟩
  · refine ⟨(piecesConcat L N).length, fun m hm => ?_⟩
    obtain ⟨hs, -, hmem⟩ := hspec (m + 1)
    have hl := hPlen (m + 1)
    have hlN := hPlen N
    have hvm : v m ∈ polygonalChain (piecesConcat L (m + 1)) := by
      rw [hv (m + 1) m (by omega)]
      exact mem_polygonal_chain_of_mem (List.getElem_mem ..)
    obtain ⟨j, -, hpj⟩ := (hmem _).mp hvm
    refine ⟨j, ?_, hpj⟩
    by_contra hjN
    rw [not_le] at hjN
    obtain ⟨-, -, hmemN⟩ := hspec N
    have hvN : v m ∈ polygonalChain (piecesConcat L N) := (hmemN _).mpr ⟨j, hjN.le, hpj⟩
    obtain ⟨i, hi, hvi⟩ := exists_mem_segment_getElem_of_mem_polygonalChain (by omega) hvN
    have hpre := piecesConcat_prefix L (show N ≤ m + 1 by omega)
    rw [hpre.getElem (show i < (piecesConcat L N).length by omega), hpre.getElem hi,
      hv (m + 1) m (by omega)] at hvi
    exact Set.disjoint_left.mp (hs.disjoint_segment_getElem i m (by omega) (by omega)) hvi
      (left_mem_segment ℝ _ _)

end LatticeProb.Topology
