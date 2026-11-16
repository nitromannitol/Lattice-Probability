import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyBounds
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurableLocal

/-! # A basis for the topology of cell configurations -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- The configuration-distance balls form a basis for the configuration topology. -/
theorem isTopologicalBasis_dCC_balls :
    TopologicalSpace.IsTopologicalBasis
      {U : Set GMSSpace | ∃ (H : GMSSpace) (ε : ℝ≥0∞), 0 < ε ∧
        U = {H' | CellConfig.dCC H.1 H'.1 < ε}} := by
  let S : Set (Set GMSSpace) :=
    {U | ∃ (H : GMSSpace) (ε : ℝ≥0∞), 0 < ε ∧
      U = {H' | CellConfig.dCC H.1 H'.1 < ε}}
  change TopologicalSpace.IsTopologicalBasis S
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨H₁, ε₁, hε₁, rfl⟩ _ ⟨H₂, ε₂, hε₂, rfl⟩ H ⟨h₁, h₂⟩
    let δ₁ := ε₁ - CellConfig.dCC H₁.1 H.1
    let δ₂ := ε₂ - CellConfig.dCC H₂.1 H.1
    have hδ₁ : 0 < δ₁ := tsub_pos_of_lt h₁
    have hδ₂ : 0 < δ₂ := tsub_pos_of_lt h₂
    refine ⟨{H' | CellConfig.dCC H.1 H'.1 < min δ₁ δ₂},
      ⟨H, min δ₁ δ₂, lt_min hδ₁ hδ₂, rfl⟩, ?_, ?_⟩
    · change CellConfig.dCC H.1 H.1 < min δ₁ δ₂
      rw [CellConfig.dCC_self]
      exact lt_min hδ₁ hδ₂
    · intro H' hH'
      constructor
      · calc
          CellConfig.dCC H₁.1 H'.1 ≤
              CellConfig.dCC H₁.1 H.1 + CellConfig.dCC H.1 H'.1 :=
            GeomTop.GMSTopology.dCC_triangle
              (GeomTop.GMSTopology.finite_restrict_ball H₁.2)
              (GeomTop.GMSTopology.finite_restrict_ball H.2) _
          _ < CellConfig.dCC H₁.1 H.1 + (ε₁ - CellConfig.dCC H₁.1 H.1) :=
            ENNReal.add_lt_add_left h₁.ne_top (lt_of_lt_of_le hH' (min_le_left _ _))
          _ = ε₁ := add_tsub_cancel_of_le h₁.le
      · calc
          CellConfig.dCC H₂.1 H'.1 ≤
              CellConfig.dCC H₂.1 H.1 + CellConfig.dCC H.1 H'.1 :=
            GeomTop.GMSTopology.dCC_triangle
              (GeomTop.GMSTopology.finite_restrict_ball H₂.2)
              (GeomTop.GMSTopology.finite_restrict_ball H.2) _
          _ < CellConfig.dCC H₂.1 H.1 + (ε₂ - CellConfig.dCC H₂.1 H.1) :=
            ENNReal.add_lt_add_left h₂.ne_top (lt_of_lt_of_le hH' (min_le_right _ _))
          _ = ε₂ := add_tsub_cancel_of_le h₂.le
  · rw [sUnion_eq_univ_iff]
    intro H
    refine ⟨{H' | CellConfig.dCC H.1 H'.1 < 1}, ⟨H, 1, zero_lt_one, rfl⟩, ?_⟩
    change CellConfig.dCC H.1 H.1 < 1
    rw [CellConfig.dCC_self]
    exact zero_lt_one

end ReflectedGMS.GMS
