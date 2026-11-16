import LatticeProb.Topology.CircleCharacterization
import LatticeProb.Topology.NonCutContinuum

/-! # Minimal locally connected continua are arcs -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- A compact locally connected continuum which is minimal among compact
preconnected sets containing two distinct points is homeomorphic to an interval. -/
theorem nonempty_homeomorph_unitInterval_of_minimal_continuum
    {K : Set ℂ} {a b : ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKlc : IsLocallyConnectedSet K) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hmin : ∀ H : Set ℂ, IsCompact H → IsPreconnected H → H ⊆ K →
      a ∈ H → b ∈ H → H = K) : Nonempty (K ≃ₜ unitInterval) := by
  classical
  let A : K := ⟨a, ha⟩
  let B : K := ⟨b, hb⟩
  have hAB : A ≠ B := fun h => hab (congrArg Subtype.val h)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : ConnectedSpace K := Subtype.connectedSpace hKc
  let : Nontrivial K := ⟨⟨A, B, hAB⟩⟩
  have hends : ∀ x : K, IsPreconnected ({x}ᶜ : Set K) → x = A ∨ x = B := by
    intro x hx
    by_contra h
    push Not at h
    have hxa : (x : ℂ) ≠ a := fun e => h.1 (Subtype.ext e)
    have hxb : (x : ℂ) ≠ b := fun e => h.2 (Subtype.ext e)
    have hpre : IsPreconnected (K \ {(x : ℂ)}) :=
      (isPreconnected_compl_singleton_subtype_iff x).mp hx
    obtain ⟨H, hHc, hHp, hHs, haH, hbH⟩ :=
      exists_isCompact_isPreconnected_subset_diff hK hKlc hpre
        ⟨ha, by simpa only [mem_singleton_iff] using hxa.symm⟩
        ⟨hb, by simpa only [mem_singleton_iff] using hxb.symm⟩
    have hHK : H = K := hmin H hHc hHp (hHs.trans sdiff_subset) haH hbH
    have hxH : (x : ℂ) ∈ H := hHK.symm ▸ x.property
    exact (hHs hxH).2 (mem_singleton _)
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_ne_isPreconnected_compl_singleton (X := K)
  have hA : IsPreconnected ({A}ᶜ : Set K) := by
    rcases hends x hx with h | h <;> rcases hends y hy with h' | h'
    · exact (hxy (h.trans h'.symm)).elim
    · simpa only [h] using hx
    · simpa only [h'] using hy
    · exact (hxy (h.trans h'.symm)).elim
  have hB : IsPreconnected ({B}ᶜ : Set K) := by
    rcases hends x hx with h | h <;> rcases hends y hy with h' | h'
    · exact (hxy (h.trans h'.symm)).elim
    · simpa only [h'] using hy
    · simpa only [h] using hx
    · exact (hxy (h.trans h'.symm)).elim
  exact nonempty_homeomorph_unitInterval_of_isPreconnected_compl_singleton_iff hAB
    (fun x => ⟨hends x, fun h => h.elim (fun e => e ▸ hA) (fun e => e ▸ hB)⟩)

/-- Such a continuum is the range of a continuous injective path. -/
theorem exists_injective_path_of_minimal_continuum
    {K : Set ℂ} {a b : ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKlc : IsLocallyConnectedSet K) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b)
    (hmin : ∀ H : Set ℂ, IsCompact H → IsPreconnected H → H ⊆ K →
      a ∈ H → b ∈ H → H = K) :
    ∃ f : unitInterval → ℂ, Continuous f ∧ Function.Injective f ∧ range f = K := by
  obtain ⟨e⟩ := nonempty_homeomorph_unitInterval_of_minimal_continuum hK hKc hKlc ha hb hab hmin
  refine ⟨fun t => (e.symm t : ℂ), continuous_subtype_val.comp e.symm.continuous,
    Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact (e.symm t).property
  · intro hz
    exact ⟨e ⟨z, hz⟩, by simp⟩

end LatticeProb.Topology
