import LatticeProb.Topology.PositiveCompactComponentPartition
import LatticeProb.Topology.FiniteCompactWitnessRelation
import LatticeProb.Topology.FiniteCompactCoverRelation
import LatticeProb.Prob.RandomSetCardinalityThreshold

/-! # Component cardinalities of compact intersections -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open ReflectedGMS ReflectedGMS.Code

namespace LatticeProb

/-- Every finite lower threshold for the number of non-singleton components
of a compact intersection is analytic. -/
theorem analyticSet_le_encard_nonSingletonComponents_inter (n : ℕ) :
    AnalyticSet {p : CompactCell × CompactCell |
      (n : ℕ∞) ≤ (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard} := by
  classical
  cases n with
  | zero =>
    have heq : {p : CompactCell × CompactCell |
        (0 : ℕ∞) ≤ (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard} =
        Set.univ := by ext p; simp
    change AnalyticSet {p : CompactCell × CompactCell |
      (0 : ℕ∞) ≤ (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard}
    rw [heq]
    exact isClosed_univ.analyticSet
  | succ n =>
    let T := (CompactCell × CompactCell) ×
      ((Fin (n + 1) → CompactCell) × (Fin (n + 1) → CompactCell))
    let E : Set T := {p |
      (∀ i j, i ≠ j → Disjoint (p.2.1 i : Set Plane) (p.2.1 j)) ∧
      (∀ i, (p.2.1 i : Set Plane) ⊆ p.1.1 ∧ (p.2.1 i : Set Plane) ⊆ p.1.2) ∧
      (∀ i, IsConnected (p.2.2 i : Set Plane) ∧
        ¬ (p.2.2 i : Set Plane).Subsingleton ∧ (p.2.2 i : Set Plane) ⊆ p.2.1 i) ∧
      (p.1.1 : Set Plane) ∩ p.1.2 ⊆ ⋃ i, (p.2.1 i : Set Plane)}
    have hE : MeasurableSet E := by
      convert (measurableSet_finite_compact_witness_relation (n + 1)).inter
        ((measurableSet_inter_subset_iUnion_compactCell (n + 1)).preimage
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))) using 1
      ext p
      simp only [E, mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hd, hp, hw, hc⟩
        exact ⟨⟨hd, hp, hw⟩, hc⟩
      · rintro ⟨⟨hd, hp, hw⟩, hc⟩
        exact ⟨hd, hp, hw, hc⟩
    have heq : {p : CompactCell × CompactCell |
        ((n + 1 : ℕ) : ℕ∞) ≤
          (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard} =
        Prod.fst '' E := by
      ext p
      simp only [mem_ofPred_eq, mem_image]
      constructor
      · intro h
        have hs : IsCompact ((p.1 : Set Plane) ∩ p.2) :=
          p.1.isCompact.inter_right p.2.isCompact.isClosed
        obtain ⟨P, W, hP, hd, hc, hw⟩ :=
          (Topology.succ_le_encard_nonSingletonComponents_iff_compact_partition hs n).mp
            (by simpa only [Nat.cast_add, Nat.cast_one] using h)
        let P' : Fin (n + 1) → CompactCell := fun i =>
          ⟨⟨P i, hP i⟩, (hw i).2.1.nonempty.mono (hw i).2.2.1⟩
        let W' : Fin (n + 1) → CompactCell := fun i =>
          ⟨⟨W i, (hw i).1⟩, (hw i).2.1.nonempty⟩
        refine ⟨(p, P', W'), ?_, rfl⟩
        change (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
          (∀ i, P i ⊆ (p.1 : Set Plane) ∧ P i ⊆ p.2) ∧
          (∀ i, IsConnected (W i) ∧ ¬ (W i).Subsingleton ∧ W i ⊆ P i) ∧
          (p.1 : Set Plane) ∩ p.2 ⊆ ⋃ i, P i
        refine ⟨hd, ?_, ?_, hc.ge⟩
        · intro i
          have hi : P i ⊆ (p.1 : Set Plane) ∩ p.2 := by
            rw [← hc]; exact subset_iUnion P i
          exact ⟨hi.trans inter_subset_left, hi.trans inter_subset_right⟩
        · intro i
          exact ⟨(hw i).2.1, (hw i).2.2.2, (hw i).2.2.1⟩
      · rintro ⟨⟨q, P, W⟩, hE, rfl⟩
        rcases hE with ⟨hd, hp, hw, hc⟩
        have hs : IsCompact ((q.1 : Set Plane) ∩ q.2) :=
          q.1.isCompact.inter_right q.2.isCompact.isClosed
        apply (Topology.succ_le_encard_nonSingletonComponents_iff_compact_partition hs n).mpr
        refine ⟨(fun i => (P i : Set Plane)), (fun i => (W i : Set Plane)),
          (fun i => (P i).isCompact), hd, ?_, ?_⟩
        · apply subset_antisymm _ hc
          exact iUnion_subset fun i => subset_inter (hp i).1 (hp i).2
        · intro i
          exact ⟨(W i).isCompact, (hw i).1, (hw i).2.2, (hw i).2.1⟩
    rw [heq]
    exact hE.analyticSet.image_of_continuous continuous_fst

/-- Finite component thresholds are null measurable under every finite law. -/
theorem nullMeasurableSet_le_encard_nonSingletonComponents_inter (n : ℕ)
    (μ : Measure (CompactCell × CompactCell)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : CompactCell × CompactCell |
      (n : ℕ∞) ≤ (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard} μ :=
  AnalyticSet.nullMeasurableSet μ (analyticSet_le_encard_nonSingletonComponents_inter n)

/-- The extended cardinality of the non-singleton components is almost
 everywhere measurable under a finite law. -/
theorem aemeasurable_encard_nonSingletonComponents_inter
    (μ : Measure (CompactCell × CompactCell)) [IsFiniteMeasure μ] :
    AEMeasurable (fun p : CompactCell × CompactCell =>
      (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).encard) μ :=
  aemeasurable_enat_of_nullMeasurable_thresholds μ _
    (fun n => nullMeasurableSet_le_encard_nonSingletonComponents_inter n μ)

/-- The natural cardinality, assigning zero to an infinite set of components,
 is almost everywhere measurable under a finite law. -/
theorem aemeasurable_ncard_nonSingletonComponents_inter
    (μ : Measure (CompactCell × CompactCell)) [IsFiniteMeasure μ] :
    AEMeasurable (fun p : CompactCell × CompactCell =>
      (nonSingletonComponents ((p.1 : Set Plane) ∩ p.2)).ncard) μ :=
  aemeasurable_ncard_of_nullMeasurable_encard_thresholds μ _
    (fun n => nullMeasurableSet_le_encard_nonSingletonComponents_inter n μ)

end LatticeProb
