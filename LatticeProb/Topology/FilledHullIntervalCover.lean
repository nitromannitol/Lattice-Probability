import LatticeProb.Topology.FilledHullShrinkingCover

/-! # Reconstruction of a curve from filled interval images -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous planar curve on a compact interval is recovered from the filled
hulls of interval covers whose mesh can be made arbitrarily small. -/
theorem image_Icc_eq_iInter_iUnion_planarFilledHull
    {a b : ℝ} (f : ℝ → ℂ) (hf : Continuous f)
    {ι : ℕ → Type*} (l r : ∀ n, ι n → ℝ)
    (hleft : ∀ n j, l n j ∈ Icc a b)
    (hsub : ∀ n j, Icc (l n j) (r n j) ⊆ Icc a b)
    (hcover : ∀ n, Icc a b ⊆ ⋃ j, Icc (l n j) (r n j))
    (hmesh : ∀ δ > 0, ∃ n, ∀ j, r n j - l n j < δ) :
    f '' Icc a b = ⋂ n, ⋃ j, planarFilledHull (f '' Icc (l n j) (r n j)) := by
  apply eq_iInter_iUnion_planarFilledHull_of_shrinking_cover
  · exact (isCompact_Icc.image hf).isClosed
  · intro n z hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover n ht)
    exact mem_iUnion.mpr ⟨j, ⟨t, hj, rfl⟩⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδf⟩ :=
      Metric.uniformContinuousOn_iff.mp
        (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
    obtain ⟨n, hn⟩ := hmesh δ hδ
    refine ⟨n, fun j => ⟨f (l n j), ⟨l n j, hleft n j, rfl⟩, ?_⟩⟩
    rintro z ⟨t, ht, rfl⟩
    apply hδf t (hsub n j ht) (l n j) (hleft n j)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact lt_of_le_of_lt (sub_le_sub_right ht.2 _) (hn j)

end LatticeProb
