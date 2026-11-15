import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-! # Measurability of a conductance lower bound -/

set_option autoImplicit false

open MeasureTheory
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigWalk

/-- The event that every nonzero conductance is at least one is measurable. -/
theorem measurableSet_conductance_eq_zero_or_one_le :
    MeasurableSet {H : GMSSpace | ∀ K K' : Cell, H.1.c K K' = 0 ∨ 1 ≤ H.1.c K K'} := by
  have heq : {H : GMSSpace | ∀ K K' : Cell, H.1.c K K' = 0 ∨ 1 ≤ H.1.c K K'} =
      ⋂ n : ℕ, ⋂ m : ℕ,
        {H : GMSSpace | H.1.codeCond n m = 0 ∨ 1 ≤ H.1.codeCond n m} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h n m
      cases hn : H.1.slot n with
      | none => simp only [CellConfig.codeCond_of_none_left hn, true_or]
      | some K =>
        cases hm : H.1.slot m with
        | none => simp only [CellConfig.codeCond_of_none_right hm, true_or]
        | some K' => simpa only [CellConfig.codeCond_of_some hn hm] using h K K'
    · intro h K K'
      by_cases hk : K ∈ H.1.cells
      · by_cases hk' : K' ∈ H.1.cells
        · have hs := h (CellConfig.label H.2 ⟨K, hk⟩) (CellConfig.label H.2 ⟨K', hk'⟩)
          simpa only [CellConfig.codeCond_of_some (CellConfig.slot_label H.2 ⟨K, hk⟩)
            (CellConfig.slot_label H.2 ⟨K', hk'⟩)] using hs
        · left
          apply le_antisymm _ (H.2.c_nonneg K K')
          exact le_of_not_gt (fun hp => hk' (H.2.adj_mem K K' hp).2)
      · left
        apply le_antisymm _ (H.2.c_nonneg K K')
        exact le_of_not_gt (fun hp => hk (H.2.adj_mem K K' hp).1)
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
    (measurableSet_eq_fun (measurable_codeCond n m) measurable_const).union
      (measurableSet_le measurable_const (measurable_codeCond n m))

/-- An almost surely satisfied conductance gap passes to the pushforward law. -/
theorem ae_conductance_eq_zero_or_one_le_map
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → GMSSpace)
    (hF : AEMeasurable F μ)
    (hc : ∀ᵐ ω ∂μ, ∀ K K' : Cell, (F ω).1.c K K' = 0 ∨ 1 ≤ (F ω).1.c K K') :
    ∀ᵐ H ∂μ.map F, ∀ K K' : Cell, H.1.c K K' = 0 ∨ 1 ≤ H.1.c K K' :=
  (ae_map_iff hF measurableSet_conductance_eq_zero_or_one_le).2 hc

end LatticeProb.CellConfigWalk
