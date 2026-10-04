/-
Polygonal subsets of the plane: the vocabulary of the classical plane-topology
theorems that the unique-continuation formalization cites from outside itself.

`LatticeProb.IsPolygonal A` says that `A` is a finite union of closed segments,
the setting of the cited plane-topology theorems, which are stated as
`Prop`-valued predicates in `LatticeProb.External.PolygonalTopology`.
-/
import Mathlib

noncomputable section

open Set

namespace LatticeProb

/-- The real coordinate plane. -/
abbrev Plane := Fin 2 → ℝ

/-- A closed segment is compact. -/
theorem isCompact_segment (a b : Plane) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)

/-- A finite union of closed segments: `A = ⋃ p ∈ L, [p.1, p.2]` for some finite
list of endpoint pairs.  This is the polygonal setting of the cited
plane-topology theorems. -/
def IsPolygonal (A : Set Plane) : Prop :=
  ∃ L : List (Plane × Plane), A = ⋃ p ∈ L, segment ℝ p.1 p.2

/-- A polygonal set is closed. -/
theorem IsPolygonal.isClosed {A : Set Plane} (h : IsPolygonal A) : IsClosed A := by
  obtain ⟨L, rfl⟩ := h
  exact L.finite_toSet.isClosed_biUnion fun p _ => (isCompact_segment p.1 p.2).isClosed

/-- A single closed segment is polygonal. -/
theorem IsPolygonal.segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[(a, b)], by simp⟩

/-- `A` separates the point `p` from infinity: the component of `p` in the
complement of `A` is bounded. -/
def Separates (A : Set Plane) (p : Plane) : Prop :=
  Bornology.IsBounded (connectedComponentIn Aᶜ p)

/-- `Separates` is monotone in the separating set: a larger set separates at
least as much. -/
theorem Separates.mono {A B : Set Plane} {p : Plane} (hAB : A ⊆ B)
    (h : Separates A p) : Separates B p := by
  exact h.subset (connectedComponentIn_mono p (compl_subset_compl.mpr hAB))

/-- The empty set separates nothing. -/
theorem not_separates_empty (p : Plane) : ¬ Separates (∅ : Set Plane) p := by
  intro h
  have hcomp : (∅ : Set Plane)ᶜ = Set.univ := by simp
  rw [Separates, hcomp, connectedComponentIn_univ] at h
  haveI : ProperSpace Plane := inferInstance
  have hc : CompactSpace Plane :=
    Metric.compactSpace_iff_isBounded_univ.mpr (by
      rw [← PreconnectedSpace.connectedComponent_eq_univ (x := p)]
      exact h)
  haveI : NoncompactSpace Plane := inferInstance
  exact (not_compactSpace_iff.mpr inferInstance) hc

/-- A point is not separated from itself by a set it avoids. -/
theorem not_separates_of_mem_compl {A : Set Plane} {p : Plane} (hp : p ∉ A) :
    p ∈ connectedComponentIn Aᶜ p :=
  mem_connectedComponentIn (by simpa using hp)

end LatticeProb
