import LatticeProb.LQG.CouplingSharedSegmentFrontiers
import LatticeProb.Topology.CompactCurveRange
import LatticeProb.Topology.JordanDiskIntersectionBoundary

/-! # Contact component shapes for coupled curve segments -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

private theorem component_shape_of_disk_segments (f : ℝ → ℂ)
    (hdisk : ∀ a b : ℝ, a < b → Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b)))
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      f '' Icc a b ∩ f '' Icc c d = frontier (f '' Icc a b) ∩ frontier (f '' Icc c d)) :
    ∀ a b c d : ℝ, a < b → b ≤ c → c < d → ∀ x ∈ f '' Icc a b ∩ f '' Icc c d,
      (∃ p : ℂ, connectedComponentIn (f '' Icc a b ∩ f '' Icc c d) x = {p}) ∨
        ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
          range g = connectedComponentIn (f '' Icc a b ∩ f '' Icc c d) x := by
  intro a b c d hab hbc hcd x hx
  have hdis : Disjoint (interior (f '' Icc a b)) (interior (f '' Icc c d)) := by
    rw [disjoint_left]
    intro y hy hz
    have hi : y ∈ f '' Icc a b ∩ f '' Icc c d := ⟨interior_subset hy, interior_subset hz⟩
    rw [hfront a b c d hab hbc hcd] at hi
    exact hi.1.2 hy
  exact LatticeProb.connectedComponentIn_embedded_disks_inter_eq_singleton_or_arc
    (hdisk a b hab).some (hdisk c d hcd).some hdis hx

/-- Assuming a common event of disk-shaped Lebesgue segments, each contact component
of ordered segments of either coupled area curve is a point or a Jordan arc, simultaneously
for all real endpoints. -/
theorem ae_interval_contact_component_shapes_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      (∀ x ∈ η ω '' Icc a b ∩ η ω '' Icc c d,
        (∃ p : ℂ, connectedComponentIn (η ω '' Icc a b ∩ η ω '' Icc c d) x = {p}) ∨
          ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
            range g = connectedComponentIn (η ω '' Icc a b ∩ η ω '' Icc c d) x) ∧
      (∀ x ∈ η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d,
        (∃ p : ℂ, connectedComponentIn (η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d) x = {p}) ∨
          ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
            range g = connectedComponentIn (η₀ ω '' Icc a b ∩ η₀ ω '' Icc c d) x) := by
  filter_upwards [hdisk, D.areaParam, D.areaParam₀, ae_shared_frontiers_of_coupling D] with ω hd ha ha₀ hf
  obtain ⟨φ, _, hφ⟩ := ha.1
  obtain ⟨ψ, _, hψ⟩ := ha₀.1
  have hsegment (χ : ℝ ≃o ℝ) (f : C(ℝ, ℂ)) (h : ∀ t, f t = ηL ω (χ t)) :
      ∀ a b : ℝ, a < b → Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b)) := by
    intro a b hab
    rw [show (f : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ χ from funext h, image_comp, χ.image_Icc]
    exact hd (χ a) (χ b) (χ.strictMono hab)
  intro a b c d hab hbc hcd
  exact ⟨component_shape_of_disk_segments (η ω) (hsegment φ (η ω) hφ)
      (fun a b c d hab hbc hcd => (hf a b c d hab hbc hcd).2.1) a b c d hab hbc hcd,
    component_shape_of_disk_segments (η₀ ω) (hsegment ψ (η₀ ω) hψ)
      (fun a b c d hab hbc hcd => (hf a b c d hab hbc hcd).2.2) a b c d hab hbc hcd⟩


/-- Every contact component of ordered shifted cells of either coupled area curve
is a point or a Jordan arc, simultaneously for all positive meshes and phases. -/
theorem ae_shifted_cell_contact_component_shapes_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ i j : ℤ, i < j →
      (∀ x ∈ (LatticeProb.shiftedCompactCell (η ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ),
        (∃ p : ℂ, connectedComponentIn ((LatticeProb.shiftedCompactCell (η ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ)) x = {p}) ∨
        ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
          range g = connectedComponentIn ((LatticeProb.shiftedCompactCell (η ω) ε θ i : Set ℂ) ∩
            (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ)) x) ∧
      (∀ x ∈ (LatticeProb.shiftedCompactCell (η₀ ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ),
        (∃ p : ℂ, connectedComponentIn ((LatticeProb.shiftedCompactCell (η₀ ω) ε θ i : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ)) x = {p}) ∨
        ∃ g : unitInterval → ℂ, Continuous g ∧ Function.Injective g ∧
          range g = connectedComponentIn ((LatticeProb.shiftedCompactCell (η₀ ω) ε θ i : Set ℂ) ∩
            (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ)) x) := by
  filter_upwards [ae_interval_contact_component_shapes_of_coupling D hdisk] with ω h
  intro ε hε θ i j hij
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  have hlt (k : ℤ) : ε * ((k : ℝ) - 1 + θ) < ε * ((k : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hord : ε * ((i : ℝ) + θ) ≤ ε * ((j : ℝ) - 1 + θ) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  have hc (f : C(ℝ, ℂ)) (k : ℤ) : (LatticeProb.shiftedCompactCell f ε θ k : Set ℂ) =
      f '' Icc (ε * ((k : ℝ) - 1 + θ)) (ε * ((k : ℝ) + θ)) := by
    rw [LatticeProb.coe_shiftedCompactCell, uIcc_of_le (hlt k).le]
  rw [hc, hc, hc, hc]
  exact h _ _ _ _ (hlt i) hord (hlt j)

end MatedCRTHarmonic.MoTInput
