import LatticeProb.Topology.ClosedSetsPathTrim
import LatticeProb.Topology.CompactIntervalPath

/-! # Compact subpaths with isolated endpoints -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- A continuous plane path with distinct endpoints contains a subpath with
those endpoints, each visited only at its corresponding parameter endpoint.
Its image is compact, connected and locally connected. -/
theorem exists_endpoint_isolated_subpath {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hne : f a ≠ f b) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ f s = f a ∧ f t = f b ∧
      (∀ u ∈ Icc s t, f u = f a ↔ u = s) ∧
      (∀ u ∈ Icc s t, f u = f b ↔ u = t) ∧
      IsCompact (f '' Icc s t) ∧ IsConnected (f '' Icc s t) ∧
      IsLocallyConnectedSet (f '' Icc s t) ∧ f '' Icc s t ⊆ f '' Icc a b := by
  have hdisj : Disjoint ({f a} : Set ℂ) {f b} := by
    simpa using hne
  obtain ⟨s, t, has, hst, htb, hs, ht, hleft, hright⟩ :=
    exists_subinterval_avoiding_closed_sets hab hf isClosed_singleton isClosed_singleton
      hdisj (mem_singleton (f a)) (mem_singleton (f b))
  have hs' : f s = f a := mem_singleton_iff.mp hs
  have ht' : f t = f b := mem_singleton_iff.mp ht
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hf' : ContinuousOn f (Icc s t) := hf.mono hsub
  refine ⟨s, t, has, hst, htb, hs', ht', ?_, ?_,
    isCompact_Icc.image_of_continuousOn hf',
    (isConnected_Icc hst.le).image f hf',
    isLocallyConnectedSet_image_Icc hst.le hf', image_mono hsub⟩
  · intro u hu
    constructor
    · intro heq
      by_contra h
      have hsu : s < u := lt_of_le_of_ne hu.1 (Ne.symm h)
      exact hleft u ⟨hsu, hu.2⟩ (by simpa using heq)
    · rintro rfl
      exact hs'
  · intro u hu
    constructor
    · intro heq
      by_contra h
      have hut : u < t := lt_of_le_of_ne hu.2 h
      exact hright u ⟨hu.1, hut⟩ (by simpa using heq)
    · rintro rfl
      exact ht'

end LatticeProb.Topology
