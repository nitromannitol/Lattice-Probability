import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-! # Uniqueness of coded cell configurations -/

set_option autoImplicit false

namespace ReflectedGMS.GMS

namespace CellConfig

/-- The code determines a valid cell configuration. -/
theorem eq_of_code_eq {H H' : CellConfig} (hH : H.IsCellConfiguration)
    (hH' : H'.IsCellConfiguration) (hcode : H.code = H'.code) : H = H' := by
  have hslot : H.slot = H'.slot := congrArg Prod.fst hcode
  have hcond : H.codeCond = H'.codeCond := congrArg Prod.snd hcode
  have hcells : H.cells = H'.cells := by
    ext K
    constructor
    · intro hK
      have hs := slot_label hH ⟨K, hK⟩
      rw [hslot] at hs
      exact ((slot_eq_some_iff hH').mp hs).1
    · intro hK
      have hs := slot_label hH' ⟨K, hK⟩
      rw [← hslot] at hs
      exact ((slot_eq_some_iff hH).mp hs).1
  have hzero (G : CellConfig) (hG : G.IsCellConfiguration) (K K' : Cell)
      (hn : K ∉ G.cells ∨ K' ∉ G.cells) : G.c K K' = 0 := by
    apply le_antisymm _ (hG.c_nonneg K K')
    apply not_lt.mp
    intro hp
    have hm := hG.adj_mem K K' hp
    exact hn.elim (fun h => h hm.1) (fun h => h hm.2)
  have hc : H.c = H'.c := by
    funext K K'
    by_cases hK : K ∈ H.cells
    · by_cases hK' : K' ∈ H.cells
      · have hs := slot_label hH ⟨K, hK⟩
        have hs' := slot_label hH ⟨K', hK'⟩
        have ht := hs
        have ht' := hs'
        rw [hslot] at ht ht'
        calc
          H.c K K' = H.codeCond (label hH ⟨K, hK⟩) (label hH ⟨K', hK'⟩) :=
            (codeCond_of_some hs hs').symm
          _ = H'.codeCond (label hH ⟨K, hK⟩) (label hH ⟨K', hK'⟩) :=
            congrFun (congrFun hcond _) _
          _ = H'.c K K' := codeCond_of_some ht ht'
      · rw [hzero H hH K K' (Or.inr hK'),
          hzero H' hH' K K' (Or.inr (by rwa [← hcells]))]
    · rw [hzero H hH K K' (Or.inl hK),
        hzero H' hH' K K' (Or.inl (by rwa [← hcells]))]
  cases H
  cases H'
  cases hcells
  cases hc
  rfl

end CellConfig

/-- The canonical code map is injective on valid configurations. -/
theorem codeMap_injective : Function.Injective codeMap := by
  intro H H' h
  exact Subtype.ext (CellConfig.eq_of_code_eq H.2 H'.2 h)

end ReflectedGMS.GMS
