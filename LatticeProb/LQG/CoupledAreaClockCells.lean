import LatticeProb.LQG.CoupledAreaTimeChange
import LatticeProb.Topology.CompactCurveRange

/-! # Cell images under the coupled area clock -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- An increasing change of time sends a shifted cell to the image of the
interval between its transformed endpoints. -/
theorem shifted_cell_eq_image_reparam
    {E : Type*} [TopologicalSpace E] (f g : C(ℝ, E)) (ψ : ℝ ≃o ℝ)
    (hfg : ∀ t, f t = g (ψ t)) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (j : ℤ) :
    (shiftedCompactCell f ε θ j : Set E) =
      g '' Icc (ψ (ε * ((j : ℝ) - 1 + θ))) (ψ (ε * ((j : ℝ) + θ))) := by
  have hends : ε * ((j : ℝ) - 1 + θ) ≤ ε * ((j : ℝ) + θ) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  rw [coe_shiftedCompactCell, uIcc_of_le hends]
  rw [show (f : ℝ → E) = (g : ℝ → E) ∘ ψ from funext hfg, image_comp, ψ.image_Icc]

/-- The signed area clock transports every shifted reference cell to an
interval image of the cone curve, on a common almost-everywhere event. -/
theorem ae_shifted_cell_eq_image_area_clock
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ j : ℤ,
      (shiftedCompactCell (η₀ ω) ε θ j : Set ℂ) =
        η ω '' Icc
          (CellScaling.JointScalingO.clock γ
            (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
            (η₀ ω) (ε * ((j : ℝ) - 1 + θ)))
          (CellScaling.JointScalingO.clock γ
            (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
            (η₀ ω) (ε * ((j : ℝ) + θ))) := by
  filter_upwards [ae_coupled_area_clock hC hγ] with ω hω
  obtain ⟨ψ, _, hcurve, hclock⟩ := hω
  intro ε hε θ j
  rw [hclock, hclock]
  exact shifted_cell_eq_image_reparam (η₀ ω) (η ω) ψ hcurve hε θ j

end LatticeProb
