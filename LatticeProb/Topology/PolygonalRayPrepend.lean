import LatticeProb.Topology.SimplePolygonalChain

/-!
# Prepending a simple polygonal chain to a simple polygonal ray

A polygonal ray is a vertex sequence `v : ℕ → E`. It is *simple* when consecutive vertices are
distinct, consecutive edges meet only at their common vertex, and edges that are not consecutive
are disjoint. If a geometrically simple finite chain ends at `v 0` and meets the trace of the ray
only there, then the chain followed by the ray is again a simple polygonal ray. Its trace is the
union of the two traces, and after finitely many steps it agrees with `v`.

## Main results

* `notMem_segment_of_simple_ray`: the initial vertex lies on no edge but the first.
* `exists_simple_ray_cons`: prepending one vertex.
* `exists_simple_ray_of_simplePolygonalChain`: prepending a simple finite chain.
-/

open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The initial vertex of a simple polygonal ray lies on none of its edges except the first. -/
theorem notMem_segment_of_simple_ray {v : ℕ → E} (hne : ∀ n, v n ≠ v (n + 1))
    (hadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    {k : ℕ} (hk : 1 ≤ k) : v 0 ∉ segment ℝ (v k) (v (k + 1)) := by
  intro h
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    exact hne 0 (hadj 0 ⟨left_mem_segment ℝ _ _, h⟩)
  · exact Set.disjoint_left.mp (hfar 0 k hk2) (left_mem_segment ℝ _ _) h

/-- **Prepending a vertex.** If `x ≠ v 0` and the segment `[x, v 0]` meets the trace of a simple
polygonal ray `v` only at `v 0`, then `x, v 0, v 1, …` is a simple polygonal ray whose trace is
`[x, v 0]` together with the trace of `v`. -/
theorem exists_simple_ray_cons {v : ℕ → E} {x : E} (hne : ∀ n, v n ≠ v (n + 1))
    (hadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    (hx : x ≠ v 0) (hmeet : segment ℝ x (v 0) ∩ ⋃ n, segment ℝ (v n) (v (n + 1)) ⊆ {v 0}) :
    ∃ r : ℕ → E, r 0 = x ∧ (∀ n, r (n + 1) = v n) ∧ (∀ n, r n ≠ r (n + 1)) ∧
      (∀ n, segment ℝ (r n) (r (n + 1)) ∩ segment ℝ (r (n + 1)) (r (n + 2)) ⊆ {r (n + 1)}) ∧
      (∀ n m, n + 2 ≤ m →
        Disjoint (segment ℝ (r n) (r (n + 1))) (segment ℝ (r m) (r (m + 1)))) ∧
      (⋃ n, segment ℝ (r n) (r (n + 1))) =
        segment ℝ x (v 0) ∪ ⋃ n, segment ℝ (v n) (v (n + 1)) := by
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → E, r 0 = x ∧ ∀ n, r (n + 1) = v n :=
    ⟨fun n => Nat.casesOn n x v, rfl, fun _ => rfl⟩
  refine ⟨r, hr0, hrs, ?_, ?_, ?_, ?_⟩
  · rintro (_ | n)
    · rw [hr0, hrs]
      exact hx
    · rw [hrs, hrs]
      exact hne n
  · rintro (_ | n)
    · show segment ℝ (r 0) (r (0 + 1)) ∩ segment ℝ (r (0 + 1)) (r (1 + 1)) ⊆ {r (0 + 1)}
      rw [hr0, hrs, hrs]
      exact fun z hz => hmeet ⟨hz.1, mem_iUnion.mpr ⟨0, hz.2⟩⟩
    · show segment ℝ (r (n + 1)) (r (n + 1 + 1)) ∩ segment ℝ (r (n + 1 + 1)) (r (n + 1 + 1 + 1))
        ⊆ {r (n + 1 + 1)}
      simp only [hrs]
      exact hadj n
  · rintro (_ | n) (_ | m) h
    · omega
    · simp only [hr0, hrs]
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have hz : z = v 0 := hmeet ⟨hz1, mem_iUnion.mpr ⟨m, hz2⟩⟩
      rw [hz] at hz2
      exact notMem_segment_of_simple_ray hne hadj hfar (k := m) (by omega) hz2
    · omega
    · simp only [hrs]
      exact hfar n m (by omega)
  · have h := (union_iUnion_nat_succ (fun n => segment ℝ (r n) (r (n + 1)))).symm
    simpa only [hr0, hrs] using h

/-- **Prepending a simple finite chain.** If a geometrically simple finite chain `vs` ends at the
initial vertex `v 0` of a simple polygonal ray `v` and meets the trace of the ray only there, then
the chain followed by the ray is a simple polygonal ray `r`: it starts at the first vertex of `vs`,
satisfies `r (n + k) = v n` for some `k`, and its trace is the union of the two traces. -/
theorem exists_simple_ray_of_simplePolygonalChain {v : ℕ → E} (hne : ∀ n, v n ≠ v (n + 1))
    (hadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1)))) :
    ∀ {vs : List E} (hs : IsSimplePolygonalChain vs), vs.getLast hs.ne_nil = v 0 →
      polygonalChain vs ∩ (⋃ n, segment ℝ (v n) (v (n + 1))) ⊆ {v 0} →
      ∃ r : ℕ → E, ∃ k : ℕ, r 0 = vs.head hs.ne_nil ∧ (∀ n, r (n + k) = v n) ∧
        (∀ n, r n ≠ r (n + 1)) ∧
        (∀ n, segment ℝ (r n) (r (n + 1)) ∩ segment ℝ (r (n + 1)) (r (n + 2)) ⊆ {r (n + 1)}) ∧
        (∀ n m, n + 2 ≤ m →
          Disjoint (segment ℝ (r n) (r (n + 1))) (segment ℝ (r m) (r (m + 1)))) ∧
        (⋃ n, segment ℝ (r n) (r (n + 1))) =
          polygonalChain vs ∪ ⋃ n, segment ℝ (v n) (v (n + 1))
  | [], hs, _, _ => hs.elim
  | [x], _, hlast, _ => by
      have hx : x = v 0 := hlast
      refine ⟨v, 0, hx.symm, fun _ => rfl, hne, hadj, hfar, ?_⟩
      rw [polygonal_chain_singleton, eq_comm, union_eq_right, singleton_subset_iff, hx]
      exact mem_iUnion.mpr ⟨0, left_mem_segment ℝ _ _⟩
  | x :: y :: rest, hs, hlast, hmeet => by
      obtain ⟨hxy, hs', hseg⟩ := hs
      have hch : polygonalChain (x :: y :: rest) = segment ℝ x y ∪ polygonalChain (y :: rest) :=
        rfl
      have hlast' : (y :: rest).getLast hs'.ne_nil = v 0 := hlast
      obtain ⟨r', k, hr'0, hr'k, hne', hadj', hfar', htr'⟩ :=
        exists_simple_ray_of_simplePolygonalChain hne hadj hfar hs' hlast'
          (fun z hz => hmeet ⟨by rw [hch]; exact Or.inr hz.1, hz.2⟩)
      have hy : r' 0 = y := hr'0
      have hv0 : v 0 ∈ polygonalChain (y :: rest) := by
        rw [← hlast']
        exact getLast_mem_polygonal_chain _
      obtain ⟨r, hr0, hrs, hne'', hadj'', hfar'', htr⟩ :=
        exists_simple_ray_cons (x := x) hne' hadj' hfar' (by rw [hy]; exact hxy) (by
          rw [hy, htr']
          rintro z ⟨hz1, hz2 | hz2⟩
          · exact hseg.subset ⟨hz1, hz2⟩
          · have hzv : z = v 0 := hmeet ⟨by rw [hch]; exact Or.inl hz1, hz2⟩
            exact hseg.subset ⟨hz1, hzv ▸ hv0⟩)
      refine ⟨r, k + 1, hr0, fun n => ?_, hne'', hadj'', hfar'', ?_⟩
      · rw [← add_assoc, hrs, hr'k]
      · rw [htr, hy, htr', hch, union_assoc]

end LatticeProb.Topology
