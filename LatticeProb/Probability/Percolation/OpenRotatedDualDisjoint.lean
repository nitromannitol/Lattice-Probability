import LatticeProb.Probability.Percolation.RotatedDualEdgeIdentity
import LatticeProb.Probability.Percolation.RotatedPrimalSubdivisionDisjoint

/-!
# Open primal and dual walk disjointness

A primal edge whose rotation is open cannot have the same doubled midpoint as an open dual
edge. Consequently the corresponding subdivisions of such walks have disjoint supports.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- An open rotated primal edge and an open dual edge have distinct doubled midpoints. -/
theorem edgeMidpoint_ne_rotatedFaceMidpoint_of_open (n : ℕ) (ω : BondConfig V)
    {x y f g : V} (hxy : G.Adj x y) (hfg : G.Adj f g)
    (hopen : s(((reflX n).trans transposeIso) x, ((reflX n).trans transposeIso) y) ∈ ω)
    (hdual : s(f, g) ∈ dualConfig ω) :
    x + y ≠ rotatedFaceMidpoint n f g := by
  intro hmid
  have heq := rotated_edge_eq_sepEdge n hfg hxy hmid.symm
  have hsep : sepEdge f g ∈ ω := heq ▸ hopen
  exact (mem_dualConfig_iff.mp hdual).2 _ hsep (dualEdge_sepEdge hfg)

/-- A primal walk with open rotated edges and a dual-open walk have disjoint subdivisions. -/
theorem disjoint_support_subdivideWalk_rotatedDual_of_open (n : ℕ) (ω : BondConfig V)
    {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hp : ∀ x y, s(x, y) ∈ p.edges →
      s(((reflX n).trans transposeIso) x, ((reflX n).trans transposeIso) y) ∈ ω)
    (hq : ∀ f g, s(f, g) ∈ q.edges → s(f, g) ∈ dualConfig ω) :
    Disjoint {z | z ∈ (subdivideWalk p).support}
      {z | z ∈ (subdivideRotatedDualWalk n q).support} := by
  apply disjoint_support_subdivideWalk_rotatedDual n p q
  intro x y hxy f g hfg
  exact edgeMidpoint_ne_rotatedFaceMidpoint_of_open n ω (p.adj_of_mem_edges hxy)
    (q.adj_of_mem_edges hfg) (hp x y hxy) (hq f g hfg)

end
end Percolation.Literature
