import LatticeProb.LQG.CouplingIntervalContacts
import LatticeProb.LQG.CouplingContactComponentShapes
import LatticeProb.LQG.CoupledAreaTimeChange

/-! # Contact classification under the signed area clock -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- Under a common event of disk-shaped Lebesgue segments, the signed area clock
identifies all reference segments with cone-curve segments, and contacts of ordered
segments of either coupled curve have at most two components, at most one for
adjacent segments, each a point or a Jordan arc. -/
theorem ae_clocked_interval_contact_classification_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      (∀ t, CellScaling.JointScalingO.clock γ
        (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
        (η₀ ω) t = ψ t) ∧
      (∀ a b : ℝ, η₀ ω '' Icc a b = η ω '' Icc
        (CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) a)
        (CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) b)) ∧
      ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
        ∀ f ∈ ({η ω, η₀ ω} : Set C(ℝ, ℂ)),
          let S : Set ℂ := f '' Icc a b ∩ f '' Icc c d
          Cardinal.mk (ConnectedComponents S) ≤ 2 ∧
          (b = c → Cardinal.mk (ConnectedComponents S) ≤ 1) ∧
          ∀ x ∈ S, (∃ p : ℂ, connectedComponentIn S x = {p}) ∨
            ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
              range g = connectedComponentIn S x := by
  filter_upwards [LatticeProb.ae_coupled_area_clock D hγ,
    ae_interval_contact_bounds_of_coupling D hdisk,
    ae_interval_contact_component_shapes_of_coupling D hdisk] with ω hclock hb hs
  obtain ⟨ψ, hzero, hcurve, hclock⟩ := hclock
  refine ⟨ψ, hzero, hclock, ?_, ?_⟩
  · intro a b
    rw [hclock, hclock]
    rw [show (η₀ ω : ℝ → ℂ) = (η ω : ℝ → ℂ) ∘ ψ from funext hcurve,
      image_comp, ψ.image_Icc]
  · intro a b c d hab hbc hcd f hf
    obtain ⟨hb₁, hb₂⟩ := hb a b c d hab hbc hcd
    obtain ⟨hs₁, hs₂⟩ := hs a b c d hab hbc hcd
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact ⟨hb₁.1, hb₁.2, hs₁⟩
    · exact ⟨hb₂.1, hb₂.2, hs₂⟩

end MatedCRTHarmonic.MoTInput
