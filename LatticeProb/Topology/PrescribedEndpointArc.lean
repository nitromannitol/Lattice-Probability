import LatticeProb.Topology.MinimalLocallyConnectedArc
import LatticeProb.OpenAI.Geometry.Cannon.PlaneTopology.Consecutive

/-! # Subarcs with prescribed endpoints -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- Two distinct points in an injective path image are joined by an injective
path contained in the same image. -/
theorem exists_injective_path_between_points_in_range
    {X : Type*} [TopologicalSpace X] {f : unitInterval → X}
    (hf : Continuous f) (hfi : Function.Injective f) {a b : X}
    (ha : a ∈ range f) (hb : b ∈ range f) (hab : a ≠ b) :
    ∃ p : unitInterval → X, Continuous p ∧ Function.Injective p ∧
      p 0 = a ∧ p 1 = b ∧ range p ⊆ range f := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hst : s ≠ t := fun h => hab (congrArg f h)
  have hcomb : Function.Injective (Icc.convexComb s t) := by
    rcases lt_or_gt_of_ne hst with h | h
    · exact OAI.CannonEmbeddedArc.Arc.convexComb_injective h
    · intro u v huv
      apply unitInterval.symm_involutive.injective
      apply OAI.CannonEmbeddedArc.Arc.convexComb_injective h
      simpa only [Icc.convexComb_symm] using huv
  refine ⟨f ∘ Icc.convexComb s t, hf.comp (Icc.continuous_convexComb s t),
    hfi.comp hcomb, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, Icc.convexComb_zero]
  · simp only [Function.comp_apply, Icc.convexComb_one]
  · rintro x ⟨u, rfl⟩
    exact mem_range_self _

/-- A minimal locally connected continuum has an injective path between its
specified endpoints. -/
theorem exists_injective_path_between_points_of_minimal_continuum
    {K : Set ℂ} {a b : ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKlc : IsLocallyConnectedSet K) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hmin : ∀ H : Set ℂ, IsCompact H → IsPreconnected H → H ⊆ K →
      a ∈ H → b ∈ H → H = K) :
    ∃ p : unitInterval → ℂ, Continuous p ∧ Function.Injective p ∧
      p 0 = a ∧ p 1 = b ∧ range p ⊆ K := by
  obtain ⟨f, hf, hfi, hfr⟩ :=
    exists_injective_path_of_minimal_continuum hK hKc hKlc ha hb hab hmin
  obtain ⟨p, hp, hpi, hp0, hp1, hpr⟩ :=
    exists_injective_path_between_points_in_range hf hfi (hfr.symm ▸ ha) (hfr.symm ▸ hb) hab
  exact ⟨p, hp, hpi, hp0, hp1, hfr ▸ hpr⟩

end LatticeProb.Topology
