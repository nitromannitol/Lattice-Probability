import LatticeProb.Topology.CompactIntersectionComponentEvent

/-! # Finite compact witness relations -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open ReflectedGMS ReflectedGMS.Code

namespace LatticeProb

/-- The finite-family conditions for disjoint compact pieces and connected,
non-singleton witnesses in a compact intersection form a Borel relation. -/
theorem measurableSet_finite_compact_witness_relation (n : ℕ) :
    MeasurableSet {p : (CompactCell × CompactCell) ×
        ((Fin n → CompactCell) × (Fin n → CompactCell)) |
      (∀ i j, i ≠ j → Disjoint (p.2.1 i : Set Plane) (p.2.1 j)) ∧
      (∀ i, (p.2.1 i : Set Plane) ⊆ p.1.1 ∧ (p.2.1 i : Set Plane) ⊆ p.1.2) ∧
      (∀ i, IsConnected (p.2.2 i : Set Plane) ∧
        ¬ (p.2.2 i : Set Plane).Subsingleton ∧ (p.2.2 i : Set Plane) ⊆ p.2.1 i)} := by
  let T := (CompactCell × CompactCell) ×
    ((Fin n → CompactCell) × (Fin n → CompactCell))
  have a : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
  have b : Measurable (fun p : T => p.1.2) := measurable_snd.comp measurable_fst
  have k (i : Fin n) : Measurable (fun p : T => p.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have w (i : Fin n) : Measurable (fun p : T => p.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hd : MeasurableSet {p : T | ∀ i j, i ≠ j →
      Disjoint (p.2.1 i : Set Plane) (p.2.1 j)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact NonemptyCompacts.isOpen_setOfPred_disjoint_coe.measurableSet.preimage
      ((k i).prodMk (k j))
  have hp : MeasurableSet {p : T | ∀ i,
      (p.2.1 i : Set Plane) ⊆ p.1.1 ∧ (p.2.1 i : Set Plane) ⊆ p.1.2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (isClosed_compactCell_subset.measurableSet.preimage ((k i).prodMk a)).inter
      (isClosed_compactCell_subset.measurableSet.preimage ((k i).prodMk b))
  have hw : MeasurableSet {p : T | ∀ i,
      IsConnected (p.2.2 i : Set Plane) ∧ ¬ (p.2.2 i : Set Plane).Subsingleton ∧
        (p.2.2 i : Set Plane) ⊆ p.2.1 i} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (GMS.ValidCodeSet.measurableSet_setOf_isConnected.preimage (w i)).inter
      ((isOpen_compactCell_nonsubsingleton.measurableSet.preimage (w i)).inter
        (isClosed_compactCell_subset.measurableSet.preimage ((w i).prodMk (k i))))
  exact hd.inter (hp.inter hw)

end LatticeProb
