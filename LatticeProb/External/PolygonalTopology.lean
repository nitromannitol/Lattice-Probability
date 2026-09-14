/-
The two classical plane-topology theorems that the unique-continuation
formalization cites from outside itself, in the polygonal setting its drawings
use.

Both are classical.  The sources are Newman, *Elements of the Topology of Plane
Sets of Points*, Chapters V and VI; Mohar and Thomassen, *Graphs on Surfaces*,
Chapter 2; and Thomassen, *The Jordan-Schoenflies theorem and the classification
of surfaces*, Amer. Math. Monthly 99 (1992) 116-130.  They are stated here as
`Prop`-valued predicates so that a paper's chain can be sealed with them as an
explicit hypothesis.
-/
import LatticeProb.Topology.Polygonal

noncomputable section

open Set

namespace LatticeProb

-- FROZEN-STATEMENT-BEGIN
/-- **Unicoherence of the sphere, for polygonal sets.**  The frontier of a
bounded component of the complement of a compact connected finite union of
segments in the plane is connected.  Newman, *Elements of the Topology of Plane
Sets of Points*, Chapter VI; Mohar and Thomassen, *Graphs on Surfaces*, Chapter
2; Thomassen, *The Jordan-Schoenflies theorem and the classification of
surfaces*, Amer. Math. Monthly 99 (1992) 116-130. -/
def PolygonalUnicoherence : Prop :=
  ∀ A : Set Plane, IsPolygonal A → IsCompact A → IsConnected A →
    ∀ F : Set Plane, (∃ p ∉ A, F = connectedComponentIn Aᶜ p) →
      Bornology.IsBounded F → IsPreconnected (frontier F)
-- FROZEN-STATEMENT-END

-- FROZEN-STATEMENT-BEGIN
/-- **Janiszewski's theorem at a point, for polygonal sets.**  If two compact
finite unions of segments meet in at most one point, and neither separates a
point `p` from infinity, then their union does not separate `p` from infinity
either.  Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V,
Theorem 9.3; Mohar and Thomassen, *Graphs on Surfaces*, Chapter 2; Thomassen,
*The Jordan-Schoenflies theorem and the classification of surfaces*, Amer. Math.
Monthly 99 (1992) 116-130. -/
def PolygonalJaniszewski : Prop :=
  ∀ A B : Set Plane, IsPolygonal A → IsPolygonal B → IsCompact A → IsCompact B →
    ∀ v : Plane, A ∩ B ⊆ {v} → ∀ p : Plane, p ∉ A ∪ B →
      ¬ Separates A p → ¬ Separates B p → ¬ Separates (A ∪ B) p
-- FROZEN-STATEMENT-END

end LatticeProb
