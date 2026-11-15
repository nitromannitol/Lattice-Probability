import LatticeProb.Topology.CompactIntersectionContainment
import LatticeProb.Topology.CompactIntersectionComponentEvent

/-! # Finite compact cover relations -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open ReflectedGMS ReflectedGMS.Code

namespace LatticeProb

/-- Covering the intersection of two compact sets by finitely many compact
sets is a Borel condition, including for an empty family. -/
theorem measurableSet_inter_subset_iUnion_compactCell (n : ℕ) :
    MeasurableSet {p : (CompactCell × CompactCell) × (Fin n → CompactCell) |
      (p.1.1 : Set Plane) ∩ p.1.2 ⊆ ⋃ i, (p.2 i : Set Plane)} := by
  cases n with
  | zero =>
    have h : MeasurableSet {p : (CompactCell × CompactCell) × (Fin 0 → CompactCell) |
        Disjoint (p.1.1 : Set Plane) p.1.2} :=
      NonemptyCompacts.isOpen_setOfPred_disjoint_coe.measurableSet.preimage measurable_fst
    simpa only [iUnion_of_empty, subset_empty_iff, Set.disjoint_iff_inter_eq_empty] using h
  | succ n =>
    let T := (CompactCell × CompactCell) × (Fin (n + 1) → CompactCell)
    let hs : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_univ _⟩
    let U : T → CompactCell := fun p => Finset.univ.sup' hs p.2
    have hU : Measurable U := by
      apply Continuous.measurable
      exact Continuous.finset_sup'_apply hs (fun i _ => (continuous_apply i).comp continuous_snd)
    have hUcoe (p : T) : (U p : Set Plane) = ⋃ i, (p.2 i : Set Plane) := by
      change ((Finset.univ.sup' hs p.2 : CompactCell) : Set Plane) = _
      rw [Finset.apply_sup'_eq_sup'_comp hs (fun K : CompactCell => (K : Set Plane))
        (fun _ _ => rfl), Finset.sup'_eq_sup]
      ext x
      simp [Finset.sup_set_eq_biUnion]
    have h := LatticeProb.Topology.measurableSet_inter_subset_union_nonemptyCompacts.preimage
      (measurable_fst.prodMk (hU.prodMk hU))
    change MeasurableSet {p : T | (p.1.1 : Set Plane) ∩ p.1.2 ⊆
      (U p : Set Plane) ∪ U p} at h
    simpa only [Set.union_self, hUcoe] using h

end LatticeProb
