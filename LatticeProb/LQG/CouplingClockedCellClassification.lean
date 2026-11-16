import LatticeProb.LQG.CouplingShiftedContactClassification
import LatticeProb.LQG.CoupledAreaClockCells

/-! # Contacts of cells under the signed area clock -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- On a common event, shifted reference cells are identified with their signed-clock
images on the cone curve, and the latter have the corresponding contact classification. -/
theorem ae_clocked_shifted_cell_contact_classification_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ,
      let clock := CellScaling.JointScalingO.clock γ
        (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) (η₀ ω)
      let cell := fun j : ℤ => η ω '' Icc
        (clock (ε * ((j : ℝ) - 1 + θ))) (clock (ε * ((j : ℝ) + θ)))
      (∀ j : ℤ, (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ) = cell j) ∧
      ∀ i j : ℤ, i < j →
        let S : Set ℂ := cell i ∩ cell j
        Cardinal.mk (ConnectedComponents S) ≤ 2 ∧
        (j = i + 1 → Cardinal.mk (ConnectedComponents S) ≤ 1) ∧
        ∀ x ∈ S, (∃ p : ℂ, connectedComponentIn S x = {p}) ∨
          ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
            range g = connectedComponentIn S x := by
  filter_upwards [LatticeProb.ae_shifted_cell_eq_image_area_clock D hγ,
    ae_shifted_cell_contact_classification_of_coupling D hdisk] with ω hcell hclass
  intro ε hε θ
  refine ⟨hcell ε hε θ, ?_⟩
  intro i j hij
  have hc := hclass ε hε θ i j hij (η₀ ω) (by simp)
  rw [hcell ε hε θ i, hcell ε hε θ j] at hc
  exact hc

end MatedCRTHarmonic.MoTInput
