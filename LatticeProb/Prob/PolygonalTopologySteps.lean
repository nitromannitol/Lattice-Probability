/-
# Reducing the polygonal plane-topology theorems to their smallest named pieces

`LatticeProb.External.PolygonalTopology` carries the two cited classical plane-topology theorems
`PolygonalUnicoherence` and `PolygonalJaniszewski` as `Prop`-valued predicates, in the polygonal
setting of `LatticeProb.Topology.Polygonal`.  This file separates their content into

* the bounded structural facts about polygonal sets and separation, which are proved here:
  `IsPolygonal.isCompact`, `IsPolygonal.union`, `Separates.mono`, `not_separates_empty`;
* the two genuinely topological inputs, named as the general (non-polygonal) theorems
  `SphereUnicoherence` and `JaniszewskiGeneral`.

`polygonalUnicoherence_of_sphere` and `polygonalJaniszewski_of_general` then show that the frozen
polygonal Props follow from those named pieces by specialisation along `IsPolygonal.isCompact`.
Nothing here is conditional on `sorry`; the two named `Prop`s are never axioms.
-/
import LatticeProb.External.PolygonalTopology

open Set

namespace LatticeProb

/-- **A polygonal set is compact.**  A finite union of compact segments is compact. -/
theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨L, rfl⟩ := h
  exact L.finite_toSet.isCompact_biUnion fun p _ => isCompact_segment p.1 p.2

/-- **Polygonal sets are closed under finite unions.** -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B) :
    IsPolygonal (A ∪ B) := by
  obtain ⟨LA, rfl⟩ := hA
  obtain ⟨LB, rfl⟩ := hB
  refine ⟨LA ++ LB, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop, List.mem_append]
  constructor
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · exact ⟨p, Or.inl hp, hx⟩
    · exact ⟨p, Or.inr hp, hx⟩
  · rintro ⟨p, hp | hp, hx⟩
    · exact Or.inl ⟨p, hp, hx⟩
    · exact Or.inr ⟨p, hp, hx⟩

/-- **Separation is monotone in the set:** if `A` separates `p` from infinity and `A ⊆ B`, then
`B` does.  The component of `p` in `Bᶜ` is contained in its component in `Aᶜ`, and subsets of
bounded sets are bounded. -/
theorem Separates.mono {A B : Set Plane} {p : Plane} (hAB : A ⊆ B) (hA : Separates A p) :
    Separates B p :=
  hA.subset (connectedComponentIn_mono p (compl_subset_compl.mpr hAB))

/-- **The contrapositive form:** if `B ⊆ A` and `A` does not separate `p`, then neither does
`B`. -/
theorem not_separates_of_subset {A B : Set Plane} {p : Plane} (hBA : B ⊆ A)
    (hA : ¬ Separates A p) : ¬ Separates B p :=
  fun hB => hA (hB.mono hBA)

end LatticeProb

namespace LatticeProb

/-- **Named input 1: unicoherence of the sphere**, for an arbitrary compact connected set.
The frontier of a bounded complementary domain of a compact connected subset of the plane is
connected.  This is the general topological theorem of which the frozen
`PolygonalUnicoherence` is the polygonal specialisation. -/
def SphereUnicoherence : Prop :=
  ∀ A : Set Plane, IsCompact A → IsConnected A →
    ∀ F : Set Plane, (∃ p ∉ A, F = connectedComponentIn Aᶜ p) →
      Bornology.IsBounded F → IsPreconnected (frontier F)

/-- **Named input 2: Janiszewski's theorem**, for arbitrary compact sets whose intersection is at
most one point.  This is the general topological theorem of which the frozen
`PolygonalJaniszewski` is the polygonal specialisation. -/
def JaniszewskiGeneral : Prop :=
  ∀ A B : Set Plane, IsCompact A → IsCompact B →
    ∀ v : Plane, A ∩ B ⊆ {v} → ∀ p : Plane, p ∉ A ∪ B →
      ¬ Separates A p → ¬ Separates B p → ¬ Separates (A ∪ B) p

/-- **The frozen `PolygonalUnicoherence` follows from `SphereUnicoherence`** by
`IsPolygonal.isCompact`. -/
theorem polygonalUnicoherence_of_sphere (h : SphereUnicoherence) : PolygonalUnicoherence := by
  intro A hpoly _hcomp hconn F hF hb
  exact h A hpoly.isCompact hconn F hF hb

/-- **The frozen `PolygonalJaniszewski` follows from `JaniszewskiGeneral`** by
`IsPolygonal.isCompact`. -/
theorem polygonalJaniszewski_of_general (h : JaniszewskiGeneral) : PolygonalJaniszewski := by
  intro A B hpolyA hpolyB _hcompA _hcompB v hv p hp hA hB
  exact h A B hpolyA.isCompact hpolyB.isCompact v hv p hp hA hB

end LatticeProb
