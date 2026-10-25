import LatticeProb.Network.OpenLadder
import LatticeProb.Prob.Percolation.LatticeBondModel

/-!
# Ambient realization of the finite open ladder

Zero padding embeds the actual open ladder into every integer lattice of dimension at least two.
The ambient carrier is given by literal interval and coordinate conditions. Its induced canonical
nearest-neighbor graph is isomorphic to the intrinsic ladder, by the exact ℓ¹ distance formula.
-/

namespace LatticeProb.Network.OpenLadder.Embedding

open scoped BigOperators
open LatticeProb.Percolation

variable {d : ℕ} {n : ℤ}

/-- The first two integer coordinates, with every other coordinate zero. -/
def zeroPad (d : ℕ) (p : ℤ × ℤ) : Percolation.Vertex d :=
  fun i => if i.val = 0 then p.1 else if i.val = 1 then p.2 else 0

/-- The literal ambient open sites, including the requirement of zero extra coordinates. -/
def ambientSites (hd : 2 ≤ d) (n : ℤ) : Set (Percolation.Vertex d) :=
  {x | ((1 ≤ x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ ≤ 4 ∧ x ⟨1, by omega⟩ = 1) ∨
      ((x ⟨0, by omega⟩ = 2 ∨ x ⟨0, by omega⟩ = 3) ∧
        1 ≤ x ⟨1, by omega⟩ ∧ x ⟨1, by omega⟩ ≤ n)) ∧
    ∀ i : Fin d, 2 ≤ i.val → x i = 0}

/-- Zero padding recovers the first coordinate when the dimension is at least two. -/
theorem zeroPad_zero (hd : 2 ≤ d) (p : ℤ × ℤ) :
    zeroPad d p ⟨0, by omega⟩ = p.1 := by simp only [zeroPad, ↓reduceIte]

/-- Zero padding recovers the second coordinate when the dimension is at least two. -/
theorem zeroPad_one (hd : 2 ≤ d) (p : ℤ × ℤ) :
    zeroPad d p ⟨1, by omega⟩ = p.2 := by simp only [zeroPad, Nat.one_ne_zero, ↓reduceIte]

/-- Every coordinate beyond the first two is exactly zero. -/
theorem zeroPad_extra (p : ℤ × ℤ) (i : Fin d) (hi : 2 ≤ i.val) :
    zeroPad d p i = 0 := by
  simp only [zeroPad, if_neg (show i.val ≠ 0 by omega),
    if_neg (show i.val ≠ 1 by omega)]

/-- The literal padding operation is injective in every dimension at least two. -/
theorem zeroPad_injective (hd : 2 ≤ d) : Function.Injective (zeroPad d) := by
  intro p q h
  apply Prod.ext
  · simpa only [zeroPad_zero hd] using congrFun h ⟨0, by omega⟩
  · simpa only [zeroPad_one hd] using congrFun h ⟨1, by omega⟩

/-- The intrinsic open sites map to the literal ambient open carrier. -/
theorem zeroPad_mem (hd : 2 ≤ d) (v : OpenLadder.Vertex n) :
    zeroPad d v.val ∈ ambientSites hd n := by
  constructor
  · simpa only [zeroPad_zero hd, zeroPad_one hd] using
      (mem_vertices n v.val.1 v.val.2).mp v.property
  · exact zeroPad_extra v.val

/-- The actual ambient embedding of an intrinsic open vertex. -/
def ambientMap (_hd : 2 ≤ d) (v : OpenLadder.Vertex n) : Percolation.Vertex d :=
  zeroPad d v.val

/-- No two actual intrinsic vertices have the same ambient image. -/
theorem ambientMap_injective (hd : 2 ≤ d) : Function.Injective (ambientMap (n := n) hd) :=
  fun _ _ h => Subtype.ext (zeroPad_injective hd h)

/-- Every literal ambient open site is recovered from its first two coordinates. -/
theorem zeroPad_coordinates (hd : 2 ≤ d) (x : ambientSites hd n) :
    zeroPad d (x.val ⟨0, by omega⟩, x.val ⟨1, by omega⟩) = x.val := by
  funext i
  by_cases h0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
    rw [hi]
    exact zeroPad_zero hd _
  by_cases h1 : i.val = 1
  · have hi : i = ⟨1, by omega⟩ := Fin.ext h1
    rw [hi]
    exact zeroPad_one hd _
  · rw [zeroPad_extra _ i (by omega), x.property.2 i (by omega)]

/-- The coordinate-defined ambient open carrier is exactly the embedding image. -/
theorem ambientSites_eq_range (hd : 2 ≤ d) (n : ℤ) :
    ambientSites hd n = Set.range (ambientMap (n := n) hd) := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨(x ⟨0, by omega⟩, x ⟨1, by omega⟩),
      (mem_vertices n _ _).mpr hx.1⟩, ?_⟩
    exact zeroPad_coordinates hd ⟨x, hx⟩
  · rintro ⟨v, rfl⟩
    exact zeroPad_mem hd v

/-- The coordinate-defined ambient open carrier is finite. -/
theorem ambientSites_finite (hd : 2 ≤ d) (n : ℤ) : (ambientSites hd n).Finite := by
  rw [ambientSites_eq_range]
  exact Set.finite_range _

/-- Padding preserves exactly the two-coordinate ℓ¹ distance, with zero contribution off-plane. -/
theorem latticeL1Dist_zeroPad (hd : 2 ≤ d) (p q : ℤ × ℤ) :
    latticeL1Dist (zeroPad d p) (zeroPad d q) = |p.1 - q.1| + |p.2 - q.2| := by
  classical
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp only [i0, i1, ne_eq, Fin.mk.injEq]; omega
  have hs : ∑ i ∈ ({i0, i1} : Finset (Fin d)),
      |zeroPad d p i - zeroPad d q i| =
      ∑ i : Fin d, |zeroPad d p i - zeroPad d q i| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have h0 : i.val ≠ 0 := by
      intro h
      exact hi (Finset.mem_insert.mpr (Or.inl (Fin.ext h)))
    have h1 : i.val ≠ 1 := by
      intro h
      exact hi (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext h))))
    rw [zeroPad_extra p i (by omega), zeroPad_extra q i (by omega)]
    norm_num
  rw [latticeL1Dist, ← hs, Finset.sum_pair hne]
  simp only [i0, i1, zeroPad_zero hd, zeroPad_one hd]

/-- Canonical ambient adjacency is exactly intrinsic open-ladder adjacency. -/
theorem ambient_adj_iff (hd : 2 ≤ d) (v w : OpenLadder.Vertex n) :
    (nearestNeighborGraph d).Adj (ambientMap hd v) (ambientMap hd w) ↔
      (graph n).Adj v w := by
  rw [lattice_adj_iff_l1Dist, ambientMap, ambientMap, latticeL1Dist_zeroPad hd]
  simp only [graph]
  rcases le_total 0 (v.val.1 - w.val.1) with hx | hx <;>
    rcases le_total 0 (v.val.2 - w.val.2) with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    omega
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]
    omega
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]
    omega
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]
    omega

/-- The explicit coordinate inverse makes the ambient embedding a bijection. -/
def ambientEquiv (hd : 2 ≤ d) (n : ℤ) : OpenLadder.Vertex n ≃ ambientSites hd n where
  toFun v := ⟨ambientMap hd v, zeroPad_mem hd v⟩
  invFun x := ⟨(x.val ⟨0, by omega⟩, x.val ⟨1, by omega⟩),
    (mem_vertices n _ _).mpr x.property.1⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (zeroPad_zero hd v.val) (zeroPad_one hd v.val)
  right_inv x := Subtype.ext (zeroPad_coordinates hd x)

/-- The full canonical lattice graph induced on the literal finite ambient open carrier. -/
def ambientGraph (hd : 2 ≤ d) (n : ℤ) : SimpleGraph (ambientSites hd n) :=
  (nearestNeighborGraph d).induce (ambientSites hd n)

/-- The intrinsic corrected open gadget is the ambient induced graph in every dimension ≥ two. -/
def ambientIso (hd : 2 ≤ d) (n : ℤ) : graph n ≃g ambientGraph hd n where
  toEquiv := ambientEquiv hd n
  map_rel_iff' := by
    intro v w
    exact ambient_adj_iff hd v w

end LatticeProb.Network.OpenLadder.Embedding
