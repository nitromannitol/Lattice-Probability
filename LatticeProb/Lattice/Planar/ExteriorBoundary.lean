/- Adapted from Lattice-Probability, commit 53bfe67ec31657683152f0b47fab1bbaf19681c0,
   module LatticeProb.Lattice.Planar.ExteriorBoundary. -/
import LatticeProb.Site

/-!
# Exterior vertex boundary of a finite star-connected set in `ℤ^d`

Timár's exterior-boundary connectivity theorem on the lattice (arXiv 0711.1713, Theorem 3, in its
`ℤ^d` form): for `d ≥ 2`, a finite set `D ⊆ ℤ^d` that is connected in the star-adjacency graph has an
exterior vertex boundary that is connected in the star-adjacency graph.

The exterior vertex boundary uses nearest-neighbour adjacency. A point of the boundary lies outside
`D`, is nearest-neighbour adjacent to `D`, and starts an injective nearest-neighbour path that avoids
`D` forever.

This file gives the definitions and the basic lemmas: adjacency, finiteness, nonemptiness of the
boundary, and a splitting criterion for connectivity of induced star-graph subsets.
-/

namespace LatticeProb.Lattice.Planar

/-- The star-adjacency graph on `ℤ^d`: distinct sites that differ by at most one in every
coordinate. -/
def starLattice (d : ℕ) : SimpleGraph (LatticeProb.Site d) where
  Adj x y := x ≠ y ∧ ∀ i, (x i - y i).natAbs ≤ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by have := h.2 i; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The exterior vertex boundary of `D`: sites outside `D` that are nearest-neighbour adjacent to
`D` and start an injective nearest-neighbour path avoiding `D`. -/
def exteriorVertexBoundary {d : ℕ} (D : Set (LatticeProb.Site d)) : Set (LatticeProb.Site d) :=
  {z | z ∉ D ∧ (∃ y ∈ D, (LatticeProb.lattice d).Adj y z) ∧
    ∃ p : ℕ → LatticeProb.Site d, Function.Injective p ∧ p 0 = z ∧
      ∀ n, p n ∉ D ∧ (LatticeProb.lattice d).Adj (p n) (p (n + 1))}

lemma starLattice_adj_iff {d : ℕ} {x y : LatticeProb.Site d} :
    (starLattice d).Adj x y ↔ x ≠ y ∧ ∀ i, (x i - y i).natAbs ≤ 1 :=
  Iff.rfl

lemma natAbs_unit_le {d : ℕ} (i j : Fin d) : (LatticeProb.unit i j).natAbs ≤ 1 := by
  unfold LatticeProb.unit
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

lemma natAbs_sub_le_one_of_lattice_adj {d : ℕ} {x y : LatticeProb.Site d}
    (h : (LatticeProb.lattice d).Adj x y) (j : Fin d) : (x j - y j).natAbs ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · subst hi
    simp only [Pi.add_apply]
    have := natAbs_unit_le i j
    omega
  · subst hi
    simp only [Pi.add_apply]
    have := natAbs_unit_le i j
    omega

lemma lattice_le_starLattice (d : ℕ) : LatticeProb.lattice d ≤ starLattice d := by
  intro x y h
  exact starLattice_adj_iff.mpr
    ⟨(LatticeProb.lattice d).ne_of_adj h, fun j => natAbs_sub_le_one_of_lattice_adj h j⟩

lemma mem_nbrFinset_of_lattice_adj {d : ℕ} {y z : LatticeProb.Site d}
    (h : (LatticeProb.lattice d).Adj y z) : z ∈ LatticeProb.nbrFinset y := by
  classical
  obtain ⟨i, hi | hi⟩ := h
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hi]⟩
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hi]⟩

lemma exteriorVertexBoundary_finite {d : ℕ} {D : Set (LatticeProb.Site d)} (hD : D.Finite) :
    (exteriorVertexBoundary D).Finite := by
  apply (hD.biUnion (fun y _ => (LatticeProb.nbrFinset y).finite_toSet)).subset
  rintro z ⟨_, ⟨y, hy, hadj⟩, _⟩
  exact Set.mem_biUnion hy (Finset.mem_coe.mpr (mem_nbrFinset_of_lattice_adj hadj))

/-- A finite nonempty set in `ℤ^d`, `d ≥ 1`, has a nonempty exterior vertex boundary: a point of
`D` maximal in the first coordinate has a neighbour outside `D` that escapes along that axis. -/
lemma exteriorVertexBoundary_nonempty {d : ℕ} (hd : 0 < d) {D : Set (LatticeProb.Site d)}
    (hD : D.Finite) (hne : D.Nonempty) : (exteriorVertexBoundary D).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := Set.exists_max_image D (fun x => x ⟨0, hd⟩) hD hne
  set i : Fin d := ⟨0, hd⟩ with hi_def
  let p : ℕ → LatticeProb.Site d := fun n => y + (((n : ℤ) + 1) • LatticeProb.unit i)
  have hcoord : ∀ n : ℕ, p n i = y i + ((n : ℤ) + 1) := by
    intro n
    simp [p, LatticeProb.unit]
  have hout : ∀ n : ℕ, p n ∉ D := by
    intro n hn
    have h' : p n i ≤ y i := hmax (p n) hn
    rw [hcoord n] at h'
    omega
  refine ⟨p 0, hout 0, ⟨y, hy, ⟨i, Or.inl ?_⟩⟩, p, ?_, rfl, fun n => ⟨hout n, ?_⟩⟩
  · simp [p]
  · intro m n h
    have h1 := congrFun h i
    rw [hcoord m, hcoord n] at h1
    have h2 : (m : ℤ) = (n : ℤ) := by omega
    exact_mod_cast h2
  · refine ⟨i, Or.inl ?_⟩
    simp only [p, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

/-- Splitting criterion: a nonempty subset `S` of `ℤ^d` whose star-graph induced subgraph has no
split into two nonempty parts without a star edge across is connected. -/
lemma induce_connected_of_split {d : ℕ} {S : Set (LatticeProb.Site d)} (hne : S.Nonempty)
    (hsplit : ∀ T ⊆ S, T.Nonempty → (S \ T).Nonempty →
      ∃ t ∈ T, ∃ s ∈ S \ T, (starLattice d).Adj t s) :
    ((starLattice d).induce S).Connected := by
  obtain ⟨s0, hs0⟩ := hne
  have : Nonempty ↥S := ⟨⟨s0, hs0⟩⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨u, hu⟩ := a
  obtain ⟨v, hv⟩ := b
  by_contra hr
  obtain ⟨t, ⟨ht, hreach⟩, s, hs, hadj⟩ := hsplit
    {x | ∃ hx : x ∈ S, ((starLattice d).induce S).Reachable ⟨u, hu⟩ ⟨x, hx⟩}
    (by rintro x ⟨hx, _⟩; exact hx) ⟨u, hu, SimpleGraph.Reachable.refl _⟩
    ⟨v, hv, fun hvT => hr hvT.2⟩
  have hadj' : ((starLattice d).induce S).Adj ⟨t, ht⟩ ⟨s, hs.1⟩ := hadj
  exact hs.2 ⟨hs.1, hreach.trans hadj'.reachable⟩

end LatticeProb.Lattice.Planar
