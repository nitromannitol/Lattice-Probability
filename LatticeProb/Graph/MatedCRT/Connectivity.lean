import LatticeProb.Graph.MatedCRT.PathGraphLemmas

/-!
# Connectivity of the deterministic mated-CRT multigraph

Every lattice successor is linked, so integer induction connects every pair of vertices.
-/

namespace LatticeProb.MatedCRT

/-- Any two vertices of the multigraph associated with two rooted paths are connected by
successive adjacency steps. -/
theorem fromPaths_adj_reflTransGen (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath)
    (a b : Vertex ε) :
    Relation.ReflTransGen ((fromPaths ε L R).Adj) a b := by
  let v : ℤ → Vertex ε := fun n => ⟨ε.val * (n : ℝ), n, rfl⟩
  have hsucc (n : ℤ) : successor ε (v n) = v (n + 1) := by
    apply Subtype.ext
    change ε.val * (n : ℝ) + ε.val = ε.val * ((n + 1 : ℤ) : ℝ)
    simp only [Int.cast_add, Int.cast_one, mul_add, mul_one]
  have hedge (n : ℤ) : (fromPaths ε L R).Adj (v n) (v (n + 1)) := by
    rw [← hsucc n]
    exact (consecutive_edge_unique ε L R (v n)).exists
  have chain (n m : ℤ) : Relation.ReflTransGen ((fromPaths ε L R).Adj) (v n) (v m) := by
    refine Int.inductionOn' m n Relation.ReflTransGen.refl ?_ ?_
    · intro k _ ih
      exact ih.tail (hedge k)
    · intro k _ ih
      apply ih.tail
      have h := (hedge (k - 1)).symm
      simpa only [sub_add_cancel] using h
  obtain ⟨n, hn⟩ := a.property
  obtain ⟨m, hm⟩ := b.property
  have ha : a = v n := Subtype.ext hn
  have hb : b = v m := Subtype.ext hm
  rw [ha, hb]
  exact chain n m

end LatticeProb.MatedCRT
