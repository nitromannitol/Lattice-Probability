import LatticeProb.LQG.CouplingRegularClosedSegments
import LatticeProb.Topology.CompactCurveRange

/-! # Disk segments under coupled area clocks -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- A common event of disk-shaped segments transfers to both coupled area clocks,
including every shifted cell for every positive mesh and real phase. -/
theorem ae_disk_segments_and_shifted_cells_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hdisk : ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b))) :
    ∀ᵐ ω ∂P,
      (∀ a b : ℝ, a < b →
        Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (η ω '' Icc a b)) ∧
        Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (η₀ ω '' Icc a b))) ∧
      (∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ j : ℤ,
        Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
          (LatticeProb.shiftedCompactCell (η ω) ε θ j : Set ℂ)) ∧
        Nonempty (closedBall (0 : ℂ) 1 ≃ₜ
          (LatticeProb.shiftedCompactCell (η₀ ω) ε θ j : Set ℂ))) := by
  filter_upwards [hdisk, D.areaParam, D.areaParam₀] with ω hd ha ha₀
  obtain ⟨φ, _, hφ⟩ := ha.1
  obtain ⟨ψ, _, hψ⟩ := ha₀.1
  have hi (χ : ℝ ≃o ℝ) (f : C(ℝ, ℂ)) (hf : ∀ t, f t = ηL ω (χ t))
      (a b : ℝ) : f '' Icc a b = ηL ω '' Icc (χ a) (χ b) := by
    rw [show (f : ℝ → ℂ) = (ηL ω : ℝ → ℂ) ∘ χ from funext hf,
      Set.image_comp, χ.image_Icc]
  have hseg : ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (η ω '' Icc a b)) ∧
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (η₀ ω '' Icc a b)) := by
    intro a b hab
    constructor
    · rw [hi φ (η ω) hφ a b]
      exact hd (φ a) (φ b) (φ.strictMono hab)
    · rw [hi ψ (η₀ ω) hψ a b]
      exact hd (ψ a) (ψ b) (ψ.strictMono hab)
  refine ⟨hseg, ?_⟩
  intro ε hε θ j
  have hlt : ε * ((j : ℝ) - 1 + θ) < ε * ((j : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hc (f : C(ℝ, ℂ)) : (LatticeProb.shiftedCompactCell f ε θ j : Set ℂ) =
      f '' Icc (ε * ((j : ℝ) - 1 + θ)) (ε * ((j : ℝ) + θ)) := by
    rw [LatticeProb.coe_shiftedCompactCell, uIcc_of_le hlt.le]
  rw [hc, hc]
  exact hseg _ _ hlt

end MatedCRTHarmonic.MoTInput
