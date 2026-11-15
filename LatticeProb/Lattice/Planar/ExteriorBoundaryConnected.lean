import LatticeProb.Lattice.Planar.ExteriorBoundaryVisibility

/-!
# Connectivity of the exterior vertex boundary

The exterior nearest-neighbour boundary of a finite star-connected subset of `ℤ^d` is
star-connected when `d ≥ 2`.
-/

set_option autoImplicit false

namespace LatticeProb.Lattice.Planar

open HigherDimLFPP.Perc

lemma sAdj_iff_starLattice_adj {d : ℕ} {x y : Site d} :
    SAdj x y ↔ (starLattice d).Adj x y := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun i => ?_⟩
    have hi := h i
    change |x i - y i| ≤ 1 at hi
    have hi' : ((x i - y i).natAbs : ℤ) ≤ 1 := by simpa [Int.natCast_natAbs] using hi
    exact_mod_cast hi'
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun i => ?_⟩
    have hi := h i
    change |x i - y i| ≤ 1
    have hi' : ((x i - y i).natAbs : ℤ) ≤ 1 := by exact_mod_cast hi
    simpa [Int.natCast_natAbs] using hi'

lemma connIn_of_induce_connected {d : ℕ} {D : Set (Site d)}
    (hc : ((starLattice d).induce D).Connected) : ConnIn D SAdj := by
  intro x hx y hy
  have hpath : ∀ a b : D, Relation.ReflTransGen ((starLattice d).induce D).Adj a b →
      Relation.ReflTransGen (StepIn D SAdj) a.val b.val := by
    intro a b hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v _ huv ih =>
      exact ih.tail ⟨u.property, v.property, sAdj_iff_starLattice_adj.mpr huv⟩
  exact hpath ⟨x, hx⟩ ⟨y, hy⟩
    ((SimpleGraph.reachable_iff_reflTransGen _ _).mp (hc ⟨x, hx⟩ ⟨y, hy⟩))

lemma induce_connected_of_connIn {d : ℕ} {D : Set (Site d)} (hne : D.Nonempty)
    (hc : ConnIn D SAdj) : ((starLattice d).induce D).Connected := by
  obtain ⟨x, hx⟩ := hne
  have : Nonempty ↥D := ⟨⟨x, hx⟩⟩
  refine ⟨fun a b => (SimpleGraph.reachable_iff_reflTransGen _ _).mpr ?_⟩
  have hp := hc a.val a.property b.val b.property
  have hpath : ∀ y (hy : y ∈ D), Relation.ReflTransGen (StepIn D SAdj) a.val y →
      Relation.ReflTransGen ((starLattice d).induce D).Adj a ⟨y, hy⟩ := by
    intro y hy h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v _ huv ih =>
      exact (ih huv.1).tail (sAdj_iff_starLattice_adj.mp huv.2.2)
  exact hpath b.val b.property hp

/-- Timár's exterior-boundary theorem for the nearest-neighbour and star lattices. -/
theorem exteriorVertexBoundary_connected {d : ℕ} (hd : 2 ≤ d) {D : Set (Site d)} (hD : D.Finite)
    (hc : ((starLattice d).induce D).Connected) :
    ((starLattice d).induce (exteriorVertexBoundary D)).Connected := by
  classical
  let E : Set (Site d) := {x | visible (lattice d) D x}
  have hED : Disjoint E D := Set.disjoint_left.mpr fun _ hx => visible_notMem hx
  obtain ⟨R, hbox⟩ := finite_subset_withinInf hD
  have hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D := by
    intro x hx y hxy hy
    by_contra hyD
    exact hy (visible_of_adj hx hyD (lAdj_iff_lattice_adj.mp hxy))
  have hconn := boundary_conn_of_connected_exterior hED (connIn_of_induce_connected hc)
    (visible_connected hd hbox) hfront
  have hB : exteriorVertexBoundary D = {y | y ∈ E ∧ ∃ z ∈ D, LAdj z y} := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, hzy⟩, hp⟩
      exact ⟨hp, z, hz, lAdj_iff_lattice_adj.mpr hzy⟩
    · rintro ⟨hp, z, hz, hzy⟩
      exact ⟨visible_notMem hp, ⟨z, hz, lAdj_iff_lattice_adj.mp hzy⟩, hp⟩
  have hnonempty : D.Nonempty := by
    obtain ⟨x⟩ := hc.nonempty
    exact ⟨x.val, x.property⟩
  have hbne := exteriorVertexBoundary_nonempty (by omega) hD hnonempty
  rw [hB] at hbne ⊢
  exact induce_connected_of_connIn hbne hconn

end LatticeProb.Lattice.Planar
