import LatticeProb.Analysis.ForwardConeVectorAffineDimension
import LatticeProb.Prob.CorrelatedBMConeJointExit

/-! # Affine interval bounds for Brownian forward cone-vector dimensions -/

set_option autoImplicit false

open Set Filter MeasureTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- On one full-measure event, affine interval dimension transfer holds for
both orientations, all intervals and all positive coordinate normalizations. -/
theorem ae_dimH_forwardConeVectors_interval_le_affine {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (e a b c f : ℝ), (e = 1 ∨ e = -1) → a < b → 0 < c → 0 < f →
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ a < z.2 ∧ z.1 < b} ≤
        dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
          (fun t => c * (X (b + (b - a) * t) - X b))
          (fun t => f * (Y (b + (b - a) * t) - Y b)) ∧
          -1 < z.2 ∧ z.1 < 0} := by
  filter_upwards [ae_forall_strict_drop_time_orientation hμ] with ω hdrop
  intro e a b c f he hab hc hf
  apply dimH_forwardConeVectors_interval_le_affine _ _ hab hc hf
  intro s hs
  have he' : -e = 1 ∨ -e = -1 := by
    rcases he with rfl | rfl <;> norm_num
  obtain ⟨r₀, hr₀, hx⟩ := hdrop 0 (-s) (-e) he'
  obtain ⟨r₁, hr₁, hy⟩ := hdrop 1 (-s) (-e) he'
  refine ⟨max (-r₀) (-r₁) + 1, by linarith [le_max_left (-r₀) (-r₁)], ?_, ?_⟩
  · refine ⟨-r₀, ⟨by linarith, by linarith [le_max_left (-r₀) (-r₁)]⟩, ?_⟩
    simpa only [neg_mul, mul_neg, neg_neg] using hx
  · refine ⟨-r₁, ⟨by linarith, by linarith [le_max_right (-r₀) (-r₁)]⟩, ?_⟩
    simpa only [neg_mul, mul_neg, neg_neg] using hy

/-- The simultaneous interval estimate with Brownian square-root scaling. -/
theorem ae_dimH_forwardConeVectors_interval_le_sqrt_rescale {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (e a b : ℝ), (e = 1 ∨ e = -1) → a < b →
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ a < z.2 ∧ z.1 < b} ≤
        dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
          (fun t => (Real.sqrt (b - a))⁻¹ * (X (b + (b - a) * t) - X b))
          (fun t => (Real.sqrt (b - a))⁻¹ * (Y (b + (b - a) * t) - Y b)) ∧
          -1 < z.2 ∧ z.1 < 0} := by
  filter_upwards [ae_dimH_forwardConeVectors_interval_le_affine hμ] with ω h
  intro e a b he hab
  exact h e a b _ _ he hab
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))

end LatticeProb.CorrelatedBM
