module

/-
Rootward orientation of an edge in a tree. The two simple paths from its endpoints
to a common root determine which endpoint has that edge as its first step. The proof
uses uniqueness of simple paths, without a choice of vertex or edge enumeration.
-/
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

set_option autoImplicit false

namespace LatticeProb.Graph

open SimpleGraph

/-- **Rootward edge orientation.** For adjacent vertices of a tree, one of their
simple paths to the root starts with the edge joining them. Its departure vertex
is distinct from the root. -/
theorem adj_eq_snd_or_eq_snd {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {r a b : V} (hab : G.Adj a b) (p : G.Walk a r) (q : G.Walk b r)
    (hp : p.IsPath) (hq : q.IsPath) :
    (a ≠ r ∧ b = p.snd) ∨ (b ≠ r ∧ a = q.snd) := by
  classical
  have root_support {v : V} (w : G.Walk v r) (hw : w.IsPath) (hvr : v = r) :
      w.support = [r] := by
    subst v
    have he : w = Walk.nil := Subtype.mk.inj
      (hG.isAcyclic.path_unique ⟨w, hw⟩ ⟨Walk.nil, Walk.IsPath.nil⟩)
    rw [he]
    rfl
  by_cases hb : b ∈ p.support
  · left
    refine ⟨?_, hG.isAcyclic.eq_snd_of_adj_start hp hab hb⟩
    intro har
    rw [root_support p hp har, List.mem_singleton] at hb
    exact hab.ne (har.trans hb.symm)
  · have ha' : a ∈ q.reverse.support :=
      hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq.reverse hp.reverse
        hab.symm (by simpa only [Walk.support_reverse, List.mem_reverse] using hb)
    have ha : a ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using ha'
    right
    refine ⟨?_, hG.isAcyclic.eq_snd_of_adj_start hq hab.symm ha⟩
    intro hbr
    rw [root_support q hq hbr, List.mem_singleton] at ha
    exact hab.ne (ha.trans hbr.symm)

end LatticeProb.Graph
