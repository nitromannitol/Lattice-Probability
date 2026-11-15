import LatticeProb.Prob.CellConfigRootedSlotMoment

/-! # Pointwise finiteness of rooted slot sums -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigCappedSquare

/-- Local finiteness and finite conductance rows make the sum over all cells
containing the origin finite, including at cell boundaries. -/
theorem originRowSum_lt_top (H : GMSSpace) : originRowSum id H < ∞ := by
  classical
  obtain ⟨U, hU, hfinU⟩ := H.2.locallyFinite (0 : Plane)
  have hT : {K : Cell | K ∈ H.1.cells ∧ (0 : Plane) ∈ (K : Set Plane)}.Finite :=
    hfinU.subset fun K hK => ⟨hK.1, 0, hK.2, mem_of_mem_nhds hU⟩
  let T : Set H.1.cells := {K | (0 : Plane) ∈ ((K : Cell) : Set Plane)}
  have hT' : T.Finite := (hT.preimage Subtype.val_injective.injOn).subset (by
    intro K hK
    exact ⟨K.2, hK⟩)
  let s : Finset ℕ := (hT'.image (CellConfig.label H.2)).toFinset
  unfold originRowSum
  rw [tsum_eq_sum (s := s)]
  · apply ENNReal.sum_lt_top.mpr
    intro n hn
    cases hs : H.1.slot n with
    | none => simp
    | some K =>
      have hK := (CellConfig.slot_eq_some_iff H.2).1 hs
      have heq : n = CellConfig.label H.2 ⟨K, hK.1⟩ :=
        Code.LeastInteriorLabel.unique hK.2 (CellConfig.leastInteriorLabel_label H.2 ⟨K, hK.1⟩)
      simp only [Option.elim]
      rw [heq, ← ofReal_pi_eq_slotRowMass H ⟨K, hK.1⟩]
      by_cases h0 : (0 : Plane) ∈ (K : Set Plane)
      · rw [originAreaRatio, Set.indicator_of_mem (show K ∈
          {L : Cell | (0 : Plane) ∈ (L : Set Plane)} from h0)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      · rw [originAreaRatio, Set.indicator_of_notMem (show K ∉
          {L : Cell | (0 : Plane) ∈ (L : Set Plane)} from h0)]
        simp
  · intro n hn
    cases hs : H.1.slot n with
    | none => simp
    | some K =>
      have hK := (CellConfig.slot_eq_some_iff H.2).1 hs
      have heq : n = CellConfig.label H.2 ⟨K, hK.1⟩ :=
        Code.LeastInteriorLabel.unique hK.2 (CellConfig.leastInteriorLabel_label H.2 ⟨K, hK.1⟩)
      have h0 : (0 : Plane) ∉ (K : Set Plane) := by
        intro h0
        apply hn
        change n ∈ (hT'.image (CellConfig.label H.2)).toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨⟨K, hK.1⟩, h0, heq.symm⟩
      change originAreaRatio K * slotRowMass id H n = 0
      rw [originAreaRatio, Set.indicator_of_notMem (show K ∉
        {L : Cell | (0 : Plane) ∈ (L : Set Plane)} from h0)]
      exact zero_mul _

end LatticeProb.CellConfigCappedSquare
