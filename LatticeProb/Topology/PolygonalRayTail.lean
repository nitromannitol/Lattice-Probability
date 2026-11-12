import LatticeProb.Topology.PolygonalRayPrepend

/-!
# Tails and junctions of simple polygonal rays

A polygonal ray is a vertex sequence `v : ℕ → E`. It is *simple* when consecutive vertices are
distinct, consecutive edges meet only at their common vertex, and edges that are not consecutive
are disjoint.

## Main results

* `exists_simple_ray_tail`: from any point of an edge of a simple polygonal ray, the rest of the
  ray is again a simple polygonal ray, whose trace lies in the trace of the ray from that edge on.
* `disjoint_segments_of_simple_rays`: two simple polygonal rays from a common vertex whose traces
  meet only at that vertex have disjoint edges, except for their two first edges, which meet only
  at the common vertex.
-/

open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Tail of a simple polygonal ray.** If `s` lies on the edge `[v k, v (k + 1)]` of a simple
polygonal ray, then `s` followed by the vertices of the ray after some index `j ≥ k` is a simple
polygonal ray, and its trace lies in the trace of the ray from the edge `k` on. -/
theorem exists_simple_ray_tail {v : ℕ → E} (hne : ∀ n, v n ≠ v (n + 1))
    (hadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    {s : E} {k : ℕ} (hs : s ∈ segment ℝ (v k) (v (k + 1))) :
    ∃ r : ℕ → E, ∃ j : ℕ, k ≤ j ∧ r 0 = s ∧ (∀ n, r (n + 1) = v (n + j + 1)) ∧
      (∀ n, r n ≠ r (n + 1)) ∧
      (∀ n, segment ℝ (r n) (r (n + 1)) ∩ segment ℝ (r (n + 1)) (r (n + 2)) ⊆ {r (n + 1)}) ∧
      (∀ n m, n + 2 ≤ m →
        Disjoint (segment ℝ (r n) (r (n + 1))) (segment ℝ (r m) (r (m + 1)))) ∧
      (⋃ n, segment ℝ (r n) (r (n + 1))) ⊆ ⋃ n, segment ℝ (v (n + k)) (v (n + k + 1)) := by
  -- Move to the next edge when `s` is the far vertex of the edge `k`.
  obtain ⟨j, hkj, hsj, hsne⟩ : ∃ j, k ≤ j ∧ s ∈ segment ℝ (v j) (v (j + 1)) ∧ s ≠ v (j + 1) := by
    by_cases h : s = v (k + 1)
    · refine ⟨k + 1, by omega, ?_, ?_⟩
      · rw [h]
        exact left_mem_segment ℝ _ _
      · rw [h]
        exact hne (k + 1)
    · exact ⟨k, le_rfl, hs, h⟩
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → E, r 0 = s ∧ ∀ n, r (n + 1) = v (n + j + 1) :=
    ⟨fun n => Nat.casesOn n s fun n => v (n + j + 1), rfl, fun _ => rfl⟩
  have e0 : r (0 + 1) = v (j + 1) := by
    rw [hrs]
    congr 1
    omega
  have e1 : r (0 + 1 + 1) = v (j + 2) := by
    rw [hrs]
    congr 1
    omega
  have hrs2 : ∀ n, r (n + 1 + 1) = v (n + j + 1 + 1) := fun n => by
    rw [hrs]
    congr 1
    omega
  have hrs3 : ∀ n, r (n + 1 + 1 + 1) = v (n + j + 1 + 2) := fun n => by
    rw [hrs]
    congr 1
    omega
  have hsub : segment ℝ s (v (j + 1)) ⊆ segment ℝ (v j) (v (j + 1)) :=
    (convex_segment _ _).segment_subset hsj (right_mem_segment ℝ _ _)
  have hseg : ∀ i, k ≤ i →
      segment ℝ (v i) (v (i + 1)) ⊆ ⋃ n, segment ℝ (v (n + k)) (v (n + k + 1)) :=
    fun i hi z hz => mem_iUnion.mpr ⟨i - k, by rw [Nat.sub_add_cancel hi]; exact hz⟩
  refine ⟨r, j, hkj, hr0, hrs, ?_, ?_, ?_, ?_⟩
  · rintro (_ | n)
    · rw [hr0, e0]
      exact hsne
    · rw [hrs2 n, hrs n]
      exact hne _
  · rintro (_ | n)
    · show segment ℝ (r 0) (r (0 + 1)) ∩ segment ℝ (r (0 + 1)) (r (0 + 1 + 1)) ⊆ {r (0 + 1)}
      rw [e1, e0, hr0]
      exact fun z hz => hadj j ⟨hsub hz.1, hz.2⟩
    · show segment ℝ (r (n + 1)) (r (n + 1 + 1)) ∩ segment ℝ (r (n + 1 + 1)) (r (n + 1 + 1 + 1))
        ⊆ {r (n + 1 + 1)}
      rw [hrs3 n, hrs2 n, hrs n]
      exact hadj _
  · rintro (_ | n) (_ | m) h
    · omega
    · rw [hr0, e0, hrs2 m, hrs m]
      exact (hfar j (m + j + 1) (by omega)).mono_left hsub
    · omega
    · rw [hrs2 n, hrs2 m, hrs n, hrs m]
      exact hfar _ _ (by omega)
  · refine iUnion_subset fun n => ?_
    rcases n with _ | n
    · rw [hr0, e0]
      exact hsub.trans (hseg j hkj)
    · rw [hrs2 n, hrs n]
      exact hseg _ (by omega)

/-- **Junction of two simple polygonal rays.** If two simple polygonal rays start at a common
vertex and their traces meet only there, then their first edges meet only at the common vertex
and every other pair of edges is disjoint. -/
theorem disjoint_segments_of_simple_rays {v w : ℕ → E} (h0 : v 0 = w 0)
    (hvne : ∀ n, v n ≠ v (n + 1)) (hwne : ∀ n, w n ≠ w (n + 1))
    (hvadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hwadj : ∀ n, segment ℝ (w n) (w (n + 1)) ∩ segment ℝ (w (n + 1)) (w (n + 2)) ⊆ {w (n + 1)})
    (hvfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    (hwfar : ∀ n m, n + 2 ≤ m →
      Disjoint (segment ℝ (w n) (w (n + 1))) (segment ℝ (w m) (w (m + 1))))
    (hmeet : (⋃ n, segment ℝ (v n) (v (n + 1))) ∩ (⋃ n, segment ℝ (w n) (w (n + 1))) ⊆ {v 0}) :
    segment ℝ (v 0) (v 1) ∩ segment ℝ (w 0) (w 1) ⊆ {w 0} ∧
      ∀ n m, 1 ≤ n + m → Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (w m) (w (m + 1))) := by
  refine ⟨fun z hz => ?_, fun n m hnm => ?_⟩
  · have hz0 : z = v 0 := hmeet ⟨mem_iUnion.mpr ⟨0, hz.1⟩, mem_iUnion.mpr ⟨0, hz.2⟩⟩
    exact hz0.trans h0
  · rw [Set.disjoint_left]
    intro z hz1 hz2
    have hz : z = v 0 := hmeet ⟨mem_iUnion.mpr ⟨n, hz1⟩, mem_iUnion.mpr ⟨m, hz2⟩⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hz, h0] at hz2
      exact notMem_segment_of_simple_ray hwne hwadj hwfar (by omega) hz2
    · rw [hz] at hz1
      exact notMem_segment_of_simple_ray hvne hvadj hvfar hn hz1

end LatticeProb.Topology
