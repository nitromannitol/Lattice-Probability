import LatticeProb.Prob.CorrelatedBMForwardConeVectorAffineDimension

/-! # Global forward cone-vector dimension bounds -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A uniform bound on forward-oriented interval restrictions bounds the
Hausdorff dimension of an arbitrary set of time pairs. -/
theorem dimH_timePair_le_of_forward_intervals (S : Set (ℝ × ℝ)) (d : ℝ≥0∞)
    (h : ∀ n : ℕ, dimH {z : ℝ × ℝ |
      z ∈ S ∧ -((n : ℝ) + 1) < z.2 ∧ z.1 < (n : ℝ) + 1} ≤ d) :
    dimH S ≤ d := by
  have hS : S ⊆ ⋃ n : ℕ, {z : ℝ × ℝ |
      z ∈ S ∧ -((n : ℝ) + 1) < z.2 ∧ z.1 < (n : ℝ) + 1} := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max (-z.2) z.1)
    refine mem_iUnion.mpr ⟨n, hz, ?_, ?_⟩
    · linarith [le_max_left (-z.2) z.1]
    · linarith [le_max_right (-z.2) z.1]
  calc
    dimH S ≤ dimH (⋃ n : ℕ, {z : ℝ × ℝ |
      z ∈ S ∧ -((n : ℝ) + 1) < z.2 ∧ z.1 < (n : ℝ) + 1}) := dimH_mono hS
    _ = ⨆ n : ℕ, dimH {z : ℝ × ℝ |
      z ∈ S ∧ -((n : ℝ) + 1) < z.2 ∧ z.1 < (n : ℝ) + 1} := dimH_iUnion _
    _ ≤ d := iSup_le h

/-- A common almost-sure bound on the countably many normalized negative-unit
intervals gives the global bound for both time orientations. -/
theorem ae_dimH_forwardConeVectors_le_of_normalized_intervals
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (d : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (e : ℝ), (e = 1 ∨ e = -1) →
      let r : ℝ := (n : ℝ) + 1
      let X : ℝ → ℝ := fun t => lrCoord 0 (e * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (e * t) ω
      dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
        (fun t => (Real.sqrt (r - -r))⁻¹ * (X (r + (r - -r) * t) - X r))
        (fun t => (Real.sqrt (r - -r))⁻¹ * (Y (r + (r - -r) * t) - Y r)) ∧
        -1 < z.2 ∧ z.1 < 0} ≤ d) :
    ∀ᵐ ω ∂μ, ∀ e : ℝ, (e = 1 ∨ e = -1) →
      dimH (forwardConeVectors (fun t => lrCoord 0 (e * t) ω)
        (fun t => lrCoord 1 (e * t) ω)) ≤ d := by
  filter_upwards [ae_dimH_forwardConeVectors_interval_le_sqrt_rescale hμ, hbound] with ω htransfer hω
  intro e he
  apply dimH_timePair_le_of_forward_intervals
  intro n
  have hr : -((n : ℝ) + 1) < (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (htransfer e (-((n : ℝ) + 1)) ((n : ℝ) + 1) he hr).trans (hω n e he)

end LatticeProb.CorrelatedBM
