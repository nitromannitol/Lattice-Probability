import LatticeProb.ReflectedGMS.GMS.CellConfigBallBasis
import Mathlib.Topology.Compactness.Lindelof

/-! # Bases for subspaces of cell configurations -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- The traces of balls centered in a family form a basis of its subspace topology. -/
theorem isTopologicalBasis_dCC_support_balls (T : Set GMSSpace) :
    TopologicalSpace.IsTopologicalBasis
      {U : Set T | ∃ (K : T) (ε : ℝ≥0∞), 0 < ε ∧
        U = {H : T | CellConfig.dCC K.1.1 H.1.1 < ε}} := by
  let S : Set (Set GMSSpace) :=
    {U | ∃ (K : GMSSpace) (ε : ℝ≥0∞), 0 < ε ∧
      U = {H | CellConfig.dCC K.1 H.1 < ε}}
  have hB : TopologicalSpace.IsTopologicalBasis
      ((fun U : Set GMSSpace => (Subtype.val : T → GMSSpace) ⁻¹' U) '' S) :=
    isTopologicalBasis_dCC_balls.induced Subtype.val
  apply hB.isTopologicalBasis_of_exists_subset
  · rintro U ⟨K, ε, hε, rfl⟩
    exact (isTopologicalBasis_dCC_balls.isOpen ⟨K.1, ε, hε, rfl⟩).preimage
      continuous_subtype_val
  · rintro U ⟨V, ⟨J, ε, hε, rfl⟩, rfl⟩ K hK
    change CellConfig.dCC J.1 K.1.1 < ε at hK
    let δ := ε - CellConfig.dCC J.1 K.1.1
    have hδ : 0 < δ := tsub_pos_of_lt hK
    refine ⟨{H : T | CellConfig.dCC K.1.1 H.1.1 < δ}, ⟨K, δ, hδ, rfl⟩, ?_, ?_⟩
    · change CellConfig.dCC K.1.1 K.1.1 < δ
      rw [CellConfig.dCC_self]
      exact hδ
    · intro H hH
      change CellConfig.dCC J.1 H.1.1 < ε
      calc
        CellConfig.dCC J.1 H.1.1 ≤ CellConfig.dCC J.1 K.1.1 +
            CellConfig.dCC K.1.1 H.1.1 :=
          GeomTop.GMSTopology.dCC_triangle
            (GeomTop.GMSTopology.finite_restrict_ball J.2)
            (GeomTop.GMSTopology.finite_restrict_ball K.1.2) _
        _ < CellConfig.dCC J.1 K.1.1 + (ε - CellConfig.dCC J.1 K.1.1) :=
          ENNReal.add_lt_add_left hK.ne_top hH
        _ = ε := add_tsub_cancel_of_le hK.le

/-- In a second-countable family, countably many support-centered ball traces
form a basis for the subspace topology. -/
theorem exists_countable_dCC_support_basis (T : Set GMSSpace) [SecondCountableTopology T] :
    ∃ B : Set (Set T), B.Countable ∧
      (∀ U ∈ B, ∃ (K : T) (ε : ℝ≥0∞), 0 < ε ∧
        U = {H : T | CellConfig.dCC K.1.1 H.1.1 < ε}) ∧
      TopologicalSpace.IsTopologicalBasis B := by
  obtain ⟨B, hsub, hcount, hbasis⟩ := (isTopologicalBasis_dCC_support_balls T).exists_countable
  exact ⟨B, hcount, hsub, hbasis⟩

end ReflectedGMS.GMS
