import LatticeProb.Prob.CellConfigCellDiameterSublinear
import LatticeProb.Prob.CellConfigIntegerConductanceMoment

/-! # Rooted moments from the origin cell slot sum -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigCappedSquare

/-- Every cell configuration has a cell containing the origin. -/
theorem exists_cell_containing_zero (H : GMSSpace) :
    ∃ K : Cell, K ∈ H.1.cells ∧ (0 : Plane) ∈ (K : Set Plane) := by
  have h : (0 : Plane) ∈ ⋃ K ∈ H.1.cells, (K : Set Plane) := by
    rw [H.2.iUnion_eq_univ]
    exact Set.mem_univ _
  obtain ⟨K, hK, h0⟩ := Set.mem_iUnion₂.mp h
  exact ⟨K, hK, h0⟩

/-- The origin slot sum dominates the ordinary conductance moment of any cell
containing the origin, including when several cells contain it. -/
theorem rooted_conductance_le_originRowSum (H : GMSSpace) (K : Cell)
    (hK : K ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K : Set Plane)) :
    ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.pi K) ≤
      originRowSum id H := by
  let k : H.1.cells := ⟨K, hK⟩
  have hterm := ENNReal.le_tsum (f := fun n =>
    (H.1.slot n).elim 0 (fun L => originAreaRatio L * slotRowMass id H n))
      (CellConfig.label H.2 k)
  rw [CellConfig.slot_label H.2 k] at hterm
  simp only [Option.elim] at hterm
  rw [originAreaRatio, Set.indicator_of_mem (show K ∈
    {L : Cell | (0 : Plane) ∈ (L : Set Plane)} from h0),
    ← ofReal_pi_eq_slotRowMass H k] at hterm
  have hmul : ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K *
      H.1.pi K) = ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K) *
        ENNReal.ofReal (H.1.pi K) :=
    ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (show 0 ≤ CellConfig.area K from
      ENNReal.toReal_nonneg))
  rw [hmul]
  exact hterm

/-- Integrability of the origin slot sum supplies both GMS rooted moments when
all nonzero conductances are at least one. -/
theorem finiteExpectation_of_originRowSum (μ : Measure GMSSpace)
    (hc : ∀ᵐ H ∂μ, ∀ K K' : Cell, H.1.c K K' = 0 ∨ 1 ≤ H.1.c K K')
    (hfin : ∫⁻ H, originRowSum id H ∂μ < ∞) : FiniteExpectation μ := by
  classical
  let H₀ : GMSSpace → Cell := fun H => Classical.choose (exists_cell_containing_zero H)
  have hroot : ∀ H, H₀ H ∈ H.1.cells ∧ (0 : Plane) ∈ (H₀ H : Set Plane) :=
    fun H => Classical.choose_spec (exists_cell_containing_zero H)
  apply LatticeProb.CellConfigWalk.finiteExpectation_of_one_le_conductance μ H₀ hroot
  · filter_upwards [hc] with H hH K
    exact hH _ _
  · exact (lintegral_mono fun H => rooted_conductance_le_originRowSum H (H₀ H)
      (hroot H).1 (hroot H).2).trans_lt hfin

end LatticeProb.CellConfigCappedSquare
