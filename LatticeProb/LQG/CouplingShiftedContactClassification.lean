import LatticeProb.LQG.CouplingIntervalContacts
import LatticeProb.LQG.CouplingContactComponentShapes

/-! # Classification of contacts of coupled shifted cells -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- Under a common event of disk-shaped Lebesgue segments, the contacts of every
ordered pair of shifted cells of both coupled area curves have at most two components,
at most one for adjacent cells, and every component is a point or a Jordan arc. -/
theorem ae_shifted_cell_contact_classification_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ i j : ℤ, i < j →
      ∀ f ∈ ({η ω, η₀ ω} : Set C(ℝ, ℂ)),
        let S : Set ℂ := (LatticeProb.shiftedCompactCell f ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell f ε θ j : Set ℂ)
        Cardinal.mk (ConnectedComponents S) ≤ 2 ∧
        (j = i + 1 → Cardinal.mk (ConnectedComponents S) ≤ 1) ∧
        ∀ x ∈ S, (∃ p : ℂ, connectedComponentIn S x = {p}) ∨
          ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
            range g = connectedComponentIn S x := by
  filter_upwards [ae_shifted_cell_contact_bounds_of_coupling D hdisk,
    ae_shifted_cell_contact_component_shapes_of_coupling D hdisk] with ω hb hs
  intro ε hε θ i j hij f hf
  obtain ⟨hb₁, hb₂⟩ := hb ε hε θ i j hij
  obtain ⟨hs₁, hs₂⟩ := hs ε hε θ i j hij
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact ⟨hb₁.1, hb₁.2, hs₁⟩
  · exact ⟨hb₂.1, hb₂.2, hs₂⟩

end MatedCRTHarmonic.MoTInput
