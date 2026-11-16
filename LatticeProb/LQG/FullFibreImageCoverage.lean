import Mathlib.Data.Set.Image

/-! # Image intersection coverage and fibre localization -/

namespace LatticeProb

/-- Coverage of an intersection of images is equivalent to finding a point in
    the covering set in every fibre that meets both original sets. -/
theorem image_inter_subset_image_iff_fibre_localization
    {α β : Type*} (η : α → β) (Q : α → α → Prop) (I J K : Set α)
    (hQ : ∀ s t, η s = η t ↔ Q s t) :
    η '' I ∩ η '' J ⊆ η '' K ↔
      ∀ s ∈ I, ∀ t ∈ J, Q s t → ∃ k ∈ K, Q s k := by
  constructor
  · intro h s hs t ht hst
    have hmem : η s ∈ η '' I ∩ η '' J :=
      ⟨⟨s, hs, rfl⟩, ⟨t, ht, ((hQ s t).2 hst).symm⟩⟩
    obtain ⟨k, hk, hks⟩ := h hmem
    exact ⟨k, hk, (hQ s k).1 hks.symm⟩
  · intro h z hz
    obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hz
    obtain ⟨k, hk, hsk⟩ := h s hs t ht ((hQ s t).1 (hsz.trans htz.symm))
    exact ⟨k, hk, ((hQ s k).2 hsk).symm.trans hsz⟩

end LatticeProb
