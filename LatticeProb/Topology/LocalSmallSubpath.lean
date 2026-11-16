import LatticeProb.Topology.CompactIntervalPath

/-! # Short subpaths near points of a compact path image

The construction follows the local argument in Bonanno's `ULC.image_Icc`. -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb.Topology

/-- Near a point of a compact path image, every point in the image can be
joined to it by an original subpath of arbitrarily small diameter. -/
theorem exists_small_subpath_near_image_point {f : ℝ → ℂ} {a b s₀ : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ f '' Icc a b, dist y (f s₀) < δ →
      ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, f s = f s₀ ∧ f t = y ∧
        Metric.diam (f '' uIcc s t) ≤ ε := by
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (half_pos hε)
  let P : Set ℝ := {s ∈ Icc a b | f s = f s₀}
  let C : Set ℝ := Icc a b \ thickening η P
  have hC : IsCompact C := isCompact_Icc.diff isOpen_thickening
  have hfC : IsClosed (f '' C) := (hC.image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hnot : f s₀ ∉ f '' C := by
    rintro ⟨t, ⟨ht, htP⟩, hteq⟩
    exact htP (self_subset_thickening hη P ⟨ht, hteq⟩)
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.mp hfC.isOpen_compl _ hnot
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨t, ht, rfl⟩ hyt
  have htC : t ∉ C := fun htC => hδC (mem_ball.mpr hyt) ⟨t, htC, rfl⟩
  have htth : t ∈ thickening η P := by
    by_contra hn
    exact htC ⟨ht, hn⟩
  obtain ⟨s, hs, hts⟩ := mem_thickening_iff.mp htth
  have hsub : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs.1 ht
  refine ⟨s, hs.1, t, ht, hs.2, rfl, ?_⟩
  apply (diam_le_of_subset_closedBall (x := f s₀) (half_pos hε).le ?_).trans
    (by linarith)
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_closedBall, ← hs.2]
  apply (hηu u (hsub hu) s hs.1 ?_).le
  have hu' := abs_sub_left_of_mem_uIcc hu
  rw [Real.dist_eq] at hts ⊢
  linarith

end LatticeProb.Topology
