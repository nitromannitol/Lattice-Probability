import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import LatticeProb.Prob.AnalyticUniversalMeasurable
import LatticeProb.Topology.CompactComponentWitness
import Mathlib.Topology.UniformSpace.Closeds

/-! # Connected components in compact intersections -/

set_option autoImplicit false

open Set MeasureTheory Topology TopologicalSpace

namespace LatticeProb

open ReflectedGMS ReflectedGMS.Code

/-- Containment is closed in the Hausdorff topology on nonempty compact sets. -/
theorem isClosed_compactCell_subset :
    IsClosed {p : CompactCell × CompactCell | (p.1 : Set Plane) ⊆ p.2} := by
  have h : {p : CompactCell × CompactCell | (p.1 : Set Plane) ⊆ p.2} =
      {p : CompactCell × CompactCell | p.1 ⊔ p.2 = p.2} := by
    ext p
    change p.1 ≤ p.2 ↔ p.1 ⊔ p.2 = p.2
    exact (sup_eq_right).symm
  rw [h]
  exact isClosed_eq (continuous_fst.sup continuous_snd) continuous_snd

/-- The set of non-singleton compact sets is open. -/
theorem isOpen_compactCell_nonsubsingleton :
    IsOpen {K : CompactCell | ¬ (K : Set Plane).Subsingleton} := by
  have h : {K : CompactCell | ¬ (K : Set Plane).Subsingleton} =
      (Set.range (fun x : Plane => ({x} : CompactCell)))ᶜ := by
    ext K
    simp only [mem_ofPred_eq, mem_compl_iff, mem_range]
    apply not_congr
    constructor
    · intro hs
      obtain ⟨x, hx⟩ := K.nonempty
      refine ⟨x, ?_⟩
      apply SetLike.ext
      intro y
      change y ∈ ({x} : Set Plane) ↔ y ∈ (K : Set Plane)
      simp only [mem_singleton_iff]
      exact ⟨fun hy => hy ▸ hx, fun hy => hs hy hx⟩
    · rintro ⟨x, rfl⟩
      exact Set.subsingleton_singleton
  rw [h]
  exact NonemptyCompacts.isClosedEmbedding_singleton.isClosed_range.isOpen_compl

/-- The existence of a non-singleton connected compact subset common to two
compact sets is an analytic event. -/
theorem analyticSet_exists_connected_compactCell_subset :
    AnalyticSet {p : CompactCell × CompactCell | ∃ K : CompactCell,
      IsConnected (K : Set Plane) ∧ ¬ (K : Set Plane).Subsingleton ∧
      (K : Set Plane) ⊆ p.1 ∧ (K : Set Plane) ⊆ p.2} := by
  let E : Set ((CompactCell × CompactCell) × CompactCell) := {p |
    IsConnected (p.2 : Set Plane) ∧ ¬ (p.2 : Set Plane).Subsingleton ∧
    (p.2 : Set Plane) ⊆ p.1.1 ∧ (p.2 : Set Plane) ⊆ p.1.2}
  have hE : MeasurableSet E := by
    exact (GMS.ValidCodeSet.measurableSet_setOf_isConnected.preimage measurable_snd).inter
      (isOpen_compactCell_nonsubsingleton.measurableSet.preimage measurable_snd |>.inter
        ((isClosed_compactCell_subset.measurableSet.preimage
            (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).inter
         (isClosed_compactCell_subset.measurableSet.preimage
            (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
  have heq : {p : CompactCell × CompactCell | ∃ K : CompactCell,
      IsConnected (K : Set Plane) ∧ ¬ (K : Set Plane).Subsingleton ∧
      (K : Set Plane) ⊆ p.1 ∧ (K : Set Plane) ⊆ p.2} = Prod.fst '' E := by
    ext p
    constructor
    · rintro ⟨K, hK⟩
      exact ⟨(p, K), hK, rfl⟩
    · rintro ⟨⟨q, K⟩, hK, rfl⟩
      exact ⟨K, hK⟩
  rw [heq]
  exact hE.analyticSet.image_of_continuous continuous_fst

/-- Existence of a non-singleton connected component of an intersection of
compact sets is analytic. -/
theorem analyticSet_exists_nonsubsingleton_inter_component :
    AnalyticSet {p : CompactCell × CompactCell |
      ∃ C ∈ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) ''
        ((p.1 : Set Plane) ∩ p.2), ¬ C.Subsingleton} := by
  have heq : {p : CompactCell × CompactCell |
      ∃ C ∈ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) ''
        ((p.1 : Set Plane) ∩ p.2), ¬ C.Subsingleton} =
      {p : CompactCell × CompactCell | ∃ K : CompactCell,
        IsConnected (K : Set Plane) ∧ ¬ (K : Set Plane).Subsingleton ∧
        (K : Set Plane) ⊆ p.1 ∧ (K : Set Plane) ⊆ p.2} := by
    ext p
    simp only [mem_ofPred_eq]
    rw [exists_nonsubsingleton_component_iff_compact_connected_subset
      (p.1.isCompact.inter_right p.2.isCompact.isClosed)]
    constructor
    · rintro ⟨K, hK, hc, hs, hn⟩
      exact ⟨⟨⟨K, hK⟩, hc.nonempty⟩, hc, hn, hs.trans inter_subset_left,
        hs.trans inter_subset_right⟩
    · rintro ⟨K, hc, hn, h1, h2⟩
      exact ⟨K, K.isCompact, hc, subset_inter h1 h2, hn⟩
  rw [heq]
  exact analyticSet_exists_connected_compactCell_subset

/-- The component event is null measurable under every finite Borel law. -/
theorem nullMeasurableSet_exists_nonsubsingleton_inter_component
    (μ : Measure (CompactCell × CompactCell)) [IsFiniteMeasure μ] :
    NullMeasurableSet {p : CompactCell × CompactCell |
      ∃ C ∈ connectedComponentIn ((p.1 : Set Plane) ∩ p.2) ''
        ((p.1 : Set Plane) ∩ p.2), ¬ C.Subsingleton} μ :=
  AnalyticSet.nullMeasurableSet μ analyticSet_exists_nonsubsingleton_inter_component

end LatticeProb
