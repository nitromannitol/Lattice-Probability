import LatticeProb.Topology.ConvexFibreImageOrder
import LatticeProb.Topology.MonotoneCompactImageRays
import LatticeProb.Topology.IntervalCharacterization

/-! # Arcs from interval maps with convex fibres -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LatticeProb

/-- A continuous interval map with convex fibres and distinct endpoints has the
same image as an injective path with the same ordered endpoints. -/
theorem exists_arc_of_convex_fibres {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (g : unitInterval → Y) (hg : Continuous g)
    (hconv : ∀ x y z, x ≤ y → y ≤ z → g x = g z → g y = g x)
    (hne : g 0 ≠ g 1) :
    ∃ p : unitInterval → Y, Continuous p ∧ Function.Injective p ∧
      p 0 = g 0 ∧ p 1 = g 1 ∧ range p = range g := by
  classical
  let F : unitInterval → range g := fun x => ⟨g x, ⟨x, rfl⟩⟩
  have hF : Continuous F := hg.rangeFactorization
  have hsurj : Function.Surjective F := rangeFactorization_surjective
  obtain ⟨ord, hmono⟩ := exists_linearOrder_range_of_convex_fibres g hconv
  let : LinearOrder (range g) := ord
  let : CompactSpace (range g) := isCompact_iff_compactSpace.mp (isCompact_range hg)
  let : ConnectedSpace (range g) := hsurj.connectedSpace hF
  let : TopologicalSpace.SeparableSpace (range g) := hsurj.denseRange.separableSpace hF
  let : Nontrivial (range g) := nontrivial_of_ne (F 0) (F 1) (fun h => hne (congrArg Subtype.val h))
  obtain ⟨hleft, hright⟩ := isOpen_rays_of_monotone_compact_surjection hF hsurj hmono
  let : OrderTopology (range g) := Topology.orderTopology_of_compactSpace hleft hright
  let : DenselyOrdered (range g) := denselyOrdered_of_preconnectedSpace
  let : CompleteLinearOrder (range g) := Topology.completeLinearOrderOfCompactSpace (range g)
  obtain ⟨e⟩ := Topology.nonempty_orderIso_unitInterval (α := range g)
  have hbot : F 0 = ⊥ := by
    apply le_antisymm _ bot_le
    obtain ⟨x, hx⟩ := hsurj ⊥
    exact (hmono (bot_le : (0 : unitInterval) ≤ x)).trans_eq hx
  have htop : F 1 = ⊤ := by
    apply le_antisymm le_top _
    obtain ⟨x, hx⟩ := hsurj ⊤
    exact hx.symm.le.trans (hmono (le_top : x ≤ (1 : unitInterval)))
  refine ⟨fun t => (e.symm t : Y), continuous_subtype_val.comp e.symm.toHomeomorph.continuous,
    fun x y h => e.symm.injective (Subtype.ext h), ?_, ?_, ?_⟩
  · change (e.symm 0 : Y) = g 0
    have he : e.symm 0 = F 0 := by
      calc
        e.symm 0 = ⊥ := e.symm.map_bot
        _ = F 0 := hbot.symm
    exact congrArg Subtype.val he
  · change (e.symm 1 : Y) = g 1
    have he : e.symm 1 = F 1 := by
      calc
        e.symm 1 = ⊤ := e.symm.map_top
        _ = F 1 := htop.symm
    exact congrArg Subtype.val he
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).property
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩

end LatticeProb
