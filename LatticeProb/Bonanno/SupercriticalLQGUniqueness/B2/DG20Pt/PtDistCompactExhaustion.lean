/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCompactExhaustion at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTailParameters
import Mathlib.Topology.Compactness.SigmaCompact

 


set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_open_compact_exhaustion
    {U : Set ℂ} (hU : IsOpen U) :
    ∃ J : ℕ → Set ℂ,
      (∀ n, IsCompact (J n)) ∧ (∀ n, J n ⊆ U) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ n, K ⊆ J n := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E : CompactExhaustion U := CompactExhaustion.choice U
  let J : ℕ → Set ℂ := fun n => Subtype.val '' E n
  refine ⟨J, ?_, ?_, ?_⟩
  · intro n
    exact (E.isCompact n).image continuous_subtype_val
  · intro n x hx
    obtain ⟨u, _, rfl⟩ := hx
    exact u.property
  · intro K hK hKU
    let Ks : Set U := Subtype.val ⁻¹' K
    have hImage : Subtype.val '' Ks = K := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hx
        exact ⟨⟨x, hKU hx⟩, hx, rfl⟩
    have hKs : IsCompact Ks :=
      Subtype.isCompact_iff.mpr (by simpa only [hImage] using hK)
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hKs
    refine ⟨n, ?_⟩
    intro x hx
    have hxs : (⟨x, hKU hx⟩ : U) ∈ Ks := hx
    exact ⟨⟨x, hKU hx⟩, hn hxs, rfl⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
