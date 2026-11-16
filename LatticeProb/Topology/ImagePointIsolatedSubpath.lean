import LatticeProb.Topology.EndpointIsolatedSubpath

/-! # Isolated endpoints between points of a path image -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- Two distinct points of a compact path image occur as the isolated endpoints
of a compact subpath, in one of the two possible orders. -/
theorem exists_isolated_subpath_between_image_points {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {x y : ℂ}
    (hx : x ∈ f '' Icc a b) (hy : y ∈ f '' Icc a b) (hxy : x ≠ y) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧
      ((f s = x ∧ f t = y) ∨ (f s = y ∧ f t = x)) ∧
      (∀ u ∈ Icc s t, f u = f s ↔ u = s) ∧
      (∀ u ∈ Icc s t, f u = f t ↔ u = t) ∧
      IsCompact (f '' Icc s t) ∧ IsConnected (f '' Icc s t) ∧
      IsLocallyConnectedSet (f '' Icc s t) ∧ f '' Icc s t ⊆ f '' Icc a b := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvy⟩ := hy
  have huv : u ≠ v := by
    intro h
    apply hxy
    rw [← hux, ← hvy, h]
  have hcore : ∀ p q : ℝ, p ∈ Icc a b → q ∈ Icc a b → p < q → f p ≠ f q →
      ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ f s = f p ∧ f t = f q ∧
        (∀ w ∈ Icc s t, f w = f s ↔ w = s) ∧
        (∀ w ∈ Icc s t, f w = f t ↔ w = t) ∧
        IsCompact (f '' Icc s t) ∧ IsConnected (f '' Icc s t) ∧
        IsLocallyConnectedSet (f '' Icc s t) ∧ f '' Icc s t ⊆ f '' Icc a b := by
    intro p q hp hq hpq hpqne
    have hsub : Icc p q ⊆ Icc a b := Icc_subset_Icc hp.1 hq.2
    obtain ⟨s, t, hps, hst, htq, hs, ht, hsf, htf, hc, hconn, hlc, hstsub⟩ :=
      exists_endpoint_isolated_subpath hpq.le (hf.mono hsub) hpqne
    refine ⟨s, t, hp.1.trans hps, hst, htq.trans hq.2, hs, ht, ?_, ?_,
      hc, hconn, hlc, hstsub.trans (image_mono hsub)⟩
    · simpa only [hs] using hsf
    · simpa only [ht] using htf
  rcases lt_or_gt_of_ne huv with huv' | hvu'
  · have hne : f u ≠ f v := by simpa only [hux, hvy] using hxy
    obtain ⟨s, t, has, hst, htb, hs, ht, hsf, htf, hc, hconn, hlc, hsub⟩ :=
      hcore u v hu hv huv' hne
    exact ⟨s, t, has, hst, htb, Or.inl ⟨hs.trans hux, ht.trans hvy⟩,
      hsf, htf, hc, hconn, hlc, hsub⟩
  · have hne : f v ≠ f u := by simpa only [hux, hvy] using hxy.symm
    obtain ⟨s, t, has, hst, htb, hs, ht, hsf, htf, hc, hconn, hlc, hsub⟩ :=
      hcore v u hv hu hvu' hne
    exact ⟨s, t, has, hst, htb, Or.inr ⟨hs.trans hvy, ht.trans hux⟩,
      hsf, htf, hc, hconn, hlc, hsub⟩

end LatticeProb.Topology
