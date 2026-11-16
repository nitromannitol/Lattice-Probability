import LatticeProb.Topology.LocalComplementAccess

/-! # Access to cyclic gaps between disk contacts -/

open Set Metric

namespace LatticeProb.Topology

/-- Three cyclically ordered contacts in distinct components determine three gaps,
each accessible from the complement of the two disks. -/
theorem exists_three_accessible_cyclic_gaps {A B : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ A) (hB : IsClosed B)
    {f : ℝ → ℂ} {a b c p : ℝ}
    (hab : a < b) (hbc : b < c) (hca : c < a + p)
    (hf : ContinuousOn f (Icc a (a + p)))
    (hfront : ∀ t ∈ Icc a (a + p), f t ∈ frontier A)
    (hclose : f (a + p) = f a)
    (ha : f a ∈ A ∩ B) (hb : f b ∈ A ∩ B) (hc : f c ∈ A ∩ B)
    (habcomp : f b ∉ connectedComponentIn (A ∩ B) (f a))
    (hbccomp : f c ∉ connectedComponentIn (A ∩ B) (f b))
    (hcacomp : f a ∉ connectedComponentIn (A ∩ B) (f c)) :
    ∃ t₁ ∈ Ioo a b, ∃ t₂ ∈ Ioo b c, ∃ t₃ ∈ Ioo c (a + p),
      ∀ t ∈ ({t₁, t₂, t₃} : Set ℝ),
        ∃ (q : ℂ) (P : Set ℂ), q ∈ (A ∪ B)ᶜ ∧ IsCompact P ∧ IsConnected P ∧
          f t ∈ P ∧ q ∈ P ∧ P ⊆ Bᶜ ∩ closure Aᶜ := by
  have hf₁ : ContinuousOn f (Icc a b) :=
    hf.mono (Icc_subset_Icc le_rfl (le_of_lt (hbc.trans hca)))
  have hf₂ : ContinuousOn f (Icc b c) :=
    hf.mono (Icc_subset_Icc hab.le (le_of_lt hca))
  have hf₃ : ContinuousOn f (Icc c (a + p)) :=
    hf.mono (Icc_subset_Icc (hab.trans hbc).le le_rfl)
  obtain ⟨t₁, ht₁, hg₁⟩ :=
    exists_interior_point_outside_of_distinct_components hab hf₁ ha hb habcomp
  obtain ⟨t₂, ht₂, hg₂⟩ :=
    exists_interior_point_outside_of_distinct_components hbc hf₂ hb hc hbccomp
  have hclosemem : f (a + p) ∈ A ∩ B := hclose ▸ ha
  have hclosediff : f (a + p) ∉ connectedComponentIn (A ∩ B) (f c) := hclose ▸ hcacomp
  obtain ⟨t₃, ht₃, hg₃⟩ :=
    exists_interior_point_outside_of_distinct_components hca hf₃ hc hclosemem hclosediff
  refine ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, ?_⟩
  intro t ht
  have htall : t ∈ Icc a (a + p) := by
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨ht₁.1.le, (ht₁.2.trans (hbc.trans hca)).le⟩
    · exact ⟨(hab.trans ht₂.1).le, (ht₂.2.trans hca).le⟩
    · exact ⟨((hab.trans hbc).trans ht₃.1).le, ht₃.2.le⟩
  have hAclosed : IsClosed A := by
    have hcompact := isCompact_range (continuous_subtype_val.comp e.continuous)
    have hrange : Set.range (fun z => (e z : ℂ)) = A := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact (e w).property
      · intro hz
        exact ⟨e.symm ⟨z, hz⟩, by simp⟩
    change IsCompact (Set.range (fun z => (e z : ℂ))) at hcompact
    rw [hrange] at hcompact
    exact hcompact.isClosed
  have htB : f t ∉ B := by
    intro htB
    have htA : f t ∈ A := hAclosed.frontier_subset (hfront t htall)
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact hg₁ ⟨htA, htB⟩
    · exact hg₂ ⟨htA, htB⟩
    · exact hg₃ ⟨htA, htB⟩
  exact exists_embedded_disk_local_access e hB (hfront t htall) htB

end LatticeProb.Topology
