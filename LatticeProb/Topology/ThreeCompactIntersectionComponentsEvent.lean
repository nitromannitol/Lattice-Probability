import LatticeProb.Topology.TwoCompactIntersectionComponentsEvent
import LatticeProb.Topology.ThreeCompactComponents

/-! # Three components of compact intersections -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace
open ReflectedGMS ReflectedGMS.Code

namespace LatticeProb

/-- Having three distinct non-singleton components in a compact intersection is analytic. -/
theorem analyticSet_exists_three_nonsubsingleton_inter_components :
    AnalyticSet {p : CompactCell × CompactCell |
      ∃ x ∈ (p.1 : Set Plane) ∩ p.2, ∃ y ∈ (p.1 : Set Plane) ∩ p.2,
      ∃ z ∈ (p.1 : Set Plane) ∩ p.2,
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z).Subsingleton} := by
  let E : Set ((CompactCell × CompactCell) ×
      ((CompactCell × CompactCell) × (CompactCell × ((CompactCell × CompactCell) × CompactCell)))) := {p |
    Disjoint (p.2.1.1 : Set Plane) p.2.1.2 ∧
    Disjoint (p.2.1.1 : Set Plane) p.2.2.1 ∧
    Disjoint (p.2.1.2 : Set Plane) p.2.2.1 ∧
    (p.2.1.1 : Set Plane) ⊆ p.1.1 ∧ (p.2.1.1 : Set Plane) ⊆ p.1.2 ∧
    (p.2.1.2 : Set Plane) ⊆ p.1.1 ∧ (p.2.1.2 : Set Plane) ⊆ p.1.2 ∧
    (p.2.2.1 : Set Plane) ⊆ p.1.1 ∧ (p.2.2.1 : Set Plane) ⊆ p.1.2 ∧
    (p.1.1 : Set Plane) ∩ p.1.2 ⊆ ((p.2.1.1 : Set Plane) ∪ p.2.1.2) ∪ p.2.2.1 ∧
    IsConnected (p.2.2.2.1.1 : Set Plane) ∧ ¬ (p.2.2.2.1.1 : Set Plane).Subsingleton ∧
    (p.2.2.2.1.1 : Set Plane) ⊆ p.2.1.1 ∧
    IsConnected (p.2.2.2.1.2 : Set Plane) ∧ ¬ (p.2.2.2.1.2 : Set Plane).Subsingleton ∧
    (p.2.2.2.1.2 : Set Plane) ⊆ p.2.1.2 ∧
    IsConnected (p.2.2.2.2 : Set Plane) ∧ ¬ (p.2.2.2.2 : Set Plane).Subsingleton ∧
    (p.2.2.2.2 : Set Plane) ⊆ p.2.2.1}
  have hE : MeasurableSet E := by
    let T := (CompactCell × CompactCell) ×
      ((CompactCell × CompactCell) × (CompactCell × ((CompactCell × CompactCell) × CompactCell)))
    have a : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
    have b : Measurable (fun p : T => p.1.2) := measurable_snd.comp measurable_fst
    have k : Measurable (fun p : T => p.2.1.1) := by fun_prop
    have l : Measurable (fun p : T => p.2.1.2) := by fun_prop
    have m : Measurable (fun p : T => p.2.2.1) := by fun_prop
    have u : Measurable (fun p : T => p.2.2.2.1.1) := by fun_prop
    have v : Measurable (fun p : T => p.2.2.2.1.2) := by fun_prop
    have w : Measurable (fun p : T => p.2.2.2.2) := by fun_prop
    have kl : Measurable (fun p : T => p.2.1.1 ⊔ p.2.1.2) :=
      (continuous_fst.sup continuous_snd).measurable.comp (k.prodMk l)
    have cover := LatticeProb.Topology.measurableSet_inter_subset_union_nonemptyCompacts.preimage
      ((a.prodMk b).prodMk (kl.prodMk m))
    change MeasurableSet {p : T | (p.1.1 : Set Plane) ∩ p.1.2 ⊆
      ((p.2.1.1 : Set Plane) ∪ p.2.1.2) ∪ p.2.2.1} at cover
    exact (NonemptyCompacts.isOpen_setOfPred_disjoint_coe.measurableSet.preimage (k.prodMk l)).inter
      ((NonemptyCompacts.isOpen_setOfPred_disjoint_coe.measurableSet.preimage (k.prodMk m)).inter
      ((NonemptyCompacts.isOpen_setOfPred_disjoint_coe.measurableSet.preimage (l.prodMk m)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (k.prodMk a)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (k.prodMk b)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (l.prodMk a)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (l.prodMk b)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (m.prodMk a)).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (m.prodMk b)).inter
      (cover.inter
      ((GMS.ValidCodeSet.measurableSet_setOf_isConnected.preimage u).inter
      ((isOpen_compactCell_nonsubsingleton.measurableSet.preimage u).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (u.prodMk k)).inter
      ((GMS.ValidCodeSet.measurableSet_setOf_isConnected.preimage v).inter
      ((isOpen_compactCell_nonsubsingleton.measurableSet.preimage v).inter
      ((isClosed_compactCell_subset.measurableSet.preimage (v.prodMk l)).inter
      ((GMS.ValidCodeSet.measurableSet_setOf_isConnected.preimage w).inter
      ((isOpen_compactCell_nonsubsingleton.measurableSet.preimage w).inter
       (isClosed_compactCell_subset.measurableSet.preimage (w.prodMk m)))))))))))))))))))
  have heq : {p : CompactCell × CompactCell |
      ∃ x ∈ (p.1 : Set Plane) ∩ p.2, ∃ y ∈ (p.1 : Set Plane) ∩ p.2,
      ∃ z ∈ (p.1 : Set Plane) ∩ p.2,
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ≠ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z).Subsingleton} = Prod.fst '' E := by
    ext p
    simp only [mem_ofPred_eq]
    rw [LatticeProb.Topology.three_nonsubsingleton_components_iff_compact_partition
      (p.1.isCompact.inter_right p.2.isCompact.isClosed)]
    constructor
    · rintro ⟨K, L, M, hK, hL, hM, hKL, hKM, hLM, he,
        ⟨U, hU, hUc, hUK, hUn⟩, ⟨V, hV, hVc, hVL, hVn⟩,
        ⟨W, hW, hWc, hWM, hWn⟩⟩
      let k : CompactCell := ⟨⟨K, hK⟩, hUc.nonempty.mono hUK⟩
      let l : CompactCell := ⟨⟨L, hL⟩, hVc.nonempty.mono hVL⟩
      let m : CompactCell := ⟨⟨M, hM⟩, hWc.nonempty.mono hWM⟩
      let u : CompactCell := ⟨⟨U, hU⟩, hUc.nonempty⟩
      let v : CompactCell := ⟨⟨V, hV⟩, hVc.nonempty⟩
      let w : CompactCell := ⟨⟨W, hW⟩, hWc.nonempty⟩
      have hk : K ⊆ (p.1 : Set Plane) ∩ p.2 := he ▸ (subset_union_left.trans subset_union_left)
      have hl : L ⊆ (p.1 : Set Plane) ∩ p.2 := he ▸ (subset_union_right.trans subset_union_left)
      have hm : M ⊆ (p.1 : Set Plane) ∩ p.2 := he ▸ subset_union_right
      exact ⟨(p, ((k, l), (m, ((u, v), w)))),
        ⟨hKL, hKM, hLM, hk.trans inter_subset_left, hk.trans inter_subset_right,
          hl.trans inter_subset_left, hl.trans inter_subset_right,
          hm.trans inter_subset_left, hm.trans inter_subset_right, he ▸ Subset.rfl,
          hUc, hUn, hUK, hVc, hVn, hVL, hWc, hWn, hWM⟩, rfl⟩
    · rintro ⟨⟨q, ⟨⟨k, l⟩, m, ⟨⟨u, v⟩, w⟩⟩⟩, h, rfl⟩
      rcases h with ⟨hkl, hkm, hlm, hk1, hk2, hl1, hl2, hm1, hm2, hc,
        hu, hun, huk, hv, hvn, hvl, hw, hwn, hwm⟩
      have he : ((k : Set Plane) ∪ l) ∪ m = (q.1 : Set Plane) ∩ q.2 :=
        subset_antisymm (union_subset (union_subset (subset_inter hk1 hk2) (subset_inter hl1 hl2))
          (subset_inter hm1 hm2)) hc
      exact ⟨k, l, m, k.isCompact, l.isCompact, m.isCompact, hkl, hkm, hlm, he,
        ⟨u, u.isCompact, hu, huk, hun⟩, ⟨v, v.isCompact, hv, hvl, hvn⟩,
        ⟨w, w.isCompact, hw, hwm, hwn⟩⟩
  rw [heq]
  let : PolishSpace (CompactCell × CompactCell) := inferInstance
  let : PolishSpace ((CompactCell × CompactCell) × CompactCell) := inferInstance
  let : PolishSpace (CompactCell × ((CompactCell × CompactCell) × CompactCell)) := inferInstance
  let : SeparableSpace ((CompactCell × CompactCell) ×
      (CompactCell × ((CompactCell × CompactCell) × CompactCell))) := inferInstance
  let : IsCompletelyMetrizableSpace ((CompactCell × CompactCell) ×
      (CompactCell × ((CompactCell × CompactCell) × CompactCell))) := inferInstance
  let : PolishSpace ((CompactCell × CompactCell) ×
      (CompactCell × ((CompactCell × CompactCell) × CompactCell))) := inferInstance
  let : SeparableSpace ((CompactCell × CompactCell) ×
      ((CompactCell × CompactCell) × (CompactCell × ((CompactCell × CompactCell) × CompactCell)))) := inferInstance
  let : IsCompletelyMetrizableSpace ((CompactCell × CompactCell) ×
      ((CompactCell × CompactCell) × (CompactCell × ((CompactCell × CompactCell) × CompactCell)))) := inferInstance
  exact hE.analyticSet.image_of_continuous continuous_fst

/-- The three-component event is null measurable under every finite Borel law. -/
theorem nullMeasurableSet_exists_three_nonsubsingleton_inter_components
    (μ : Measure (CompactCell × CompactCell)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : CompactCell × CompactCell |
      ∃ x ∈ (p.1 : Set Plane) ∩ p.2, ∃ y ∈ (p.1 : Set Plane) ∩ p.2,
      ∃ z ∈ (p.1 : Set Plane) ∩ p.2,
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y ≠
          connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) x).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) y).Subsingleton ∧
        ¬ (connectedComponentIn ((p.1 : Set Plane) ∩ p.2) z).Subsingleton} μ :=
  AnalyticSet.nullMeasurableSet μ analyticSet_exists_three_nonsubsingleton_inter_components

end LatticeProb
