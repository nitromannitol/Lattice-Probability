import LatticeProb.Topology.Length.InternalOps

/-! # Trimming a path between disjoint closed sets -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- A continuous curve joining two disjoint closed sets has a subinterval whose
interior avoids both sets and whose endpoints lie in the respective sets. -/
theorem exists_subinterval_avoiding_closed_sets {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} {a b : ℝ} {A B : Set X}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (ha : f a ∈ A) (hb : f b ∈ B) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ f s ∈ A ∧ f t ∈ B ∧
      (∀ u ∈ Ioc s t, f u ∉ A) ∧ (∀ u ∈ Ico s t, f u ∉ B) := by
  obtain ⟨t, ht, hft, hbefore⟩ := LatticeProb.MetricGeometry.exists_first_hit hf hB
    ⟨b, ⟨hab, le_rfl⟩, hb⟩
  let S := Icc a t ∩ f ⁻¹' A
  have hSc : IsClosed S := (hf.mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed
    isClosed_Icc hA
  have haS : a ∈ S := ⟨⟨le_rfl, ht.1⟩, ha⟩
  have hSb : BddAbove S := ⟨t, fun _ hu => hu.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem ⟨a, haS⟩ hSb
  have hst : sSup S < t := by
    refine lt_of_le_of_ne hsS.1.2 ?_
    intro h
    have hftA : f t ∈ A := h ▸ hsS.2
    exact Set.disjoint_left.mp hAB hftA hft
  refine ⟨sSup S, t, hsS.1.1, hst, ht.2, hsS.2, hft, ?_, ?_⟩
  · intro u hu huA
    have huS : u ∈ S := ⟨⟨hsS.1.1.trans hu.1.le, hu.2⟩, huA⟩
    exact (not_le_of_gt hu.1) (le_csSup hSb huS)
  · intro u hu
    exact hbefore u ⟨hsS.1.1.trans hu.1, hu.2⟩

end LatticeProb.Topology
