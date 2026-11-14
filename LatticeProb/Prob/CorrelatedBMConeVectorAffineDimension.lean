import LatticeProb.Analysis.ConeVectorAffineDimension
import LatticeProb.Prob.CorrelatedBMConeJointExit

/-! # Affine interval bounds for Brownian cone-vector dimensions -/

set_option autoImplicit false

open Set Filter MeasureTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- On one full-measure event, affine interval dimension transfer holds for
both orientations, all intervals and all positive coordinate normalizations. -/
theorem ae_dimH_backwardConeVectors_interval_le_affine {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (e a b c f : ℝ), (e = 1 ∨ e = -1) → a < b → 0 < c → 0 < f →
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ a < z.1 ∧ z.2 < b} ≤
        dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
          (fun t => c * (X (a + (b - a) * t) - X a))
          (fun t => f * (Y (a + (b - a) * t) - Y a)) ∧
          0 < z.1 ∧ z.2 < 1} := by
  filter_upwards [ae_forall_strict_drop_time_orientation hμ] with ω hdrop
  intro e a b c f he hab hc hf
  apply dimH_backwardConeVectors_interval_le_affine _ _ hab hc hf
  intro s hs
  obtain ⟨r₀, hr₀, hx⟩ := hdrop 0 s e he
  obtain ⟨r₁, hr₁, hy⟩ := hdrop 1 s e he
  refine ⟨min r₀ r₁ - 1, by linarith [min_le_left r₀ r₁], ?_, ?_⟩
  · exact ⟨r₀, ⟨by linarith [min_le_left r₀ r₁], le_of_lt hr₀⟩, hx⟩
  · exact ⟨r₁, ⟨by linarith [min_le_right r₀ r₁], le_of_lt hr₁⟩, hy⟩

/-- The simultaneous interval estimate with Brownian square-root scaling. -/
theorem ae_dimH_backwardConeVectors_interval_le_sqrt_rescale {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (e a b : ℝ), (e = 1 ∨ e = -1) → a < b →
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ a < z.1 ∧ z.2 < b} ≤
        dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
          (fun t => (Real.sqrt (b - a))⁻¹ * (X (a + (b - a) * t) - X a))
          (fun t => (Real.sqrt (b - a))⁻¹ * (Y (a + (b - a) * t) - Y a)) ∧
          0 < z.1 ∧ z.2 < 1} := by
  filter_upwards [ae_dimH_backwardConeVectors_interval_le_affine hμ] with ω h
  intro e a b he hab
  exact h e a b _ _ he hab
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))

end LatticeProb.CorrelatedBM
