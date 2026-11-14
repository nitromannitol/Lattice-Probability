import LatticeProb.Walk.CellConfigExteriorHitBracket
import LatticeProb.Walk.CellConfigExitRestart

/-! # Simultaneous exit brackets for restarted cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A single full-measure event supplies the exit bracket for every restart,
representative selection, positive scale and bounded open convex domain. -/
theorem ae_exterior_hit_bracket_all_shifts (H : CellConfig)
    (hH : H.IsCellConfiguration) (hpos : ∀ C, 0 < H.holding C)
    [MeasurableSpace (ℕ → H.cells)] (μ : Measure (ℕ → H.cells))
    (hunb : ∀ᵐ ω ∂μ, H.JumpTimesUnbounded ω)
    (hadj : ∀ᵐ ω ∂μ, ∀ n, H.Adj (ω n) (ω (n + 1)))
    (hvisit : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ p : H.cells → Plane,
      (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
      ∀ U : Set Plane, Bornology.IsBounded U →
      hitTime {C : H.cells | (a : ℝ) • p C ∉ U} (fun n => ω (k + n)) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ p : H.cells → Plane,
      (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
      ∀ U : Set Plane, Bornology.IsBounded U → IsOpen U → Convex ℝ U →
      let ξ := fun n => ω (k + n)
      let T := hitTime {C : H.cells | (a : ℝ) • p C ∉ U}
      let τ := continuousExitTime U 0 (H.interpolatedWalk p a ξ)
      ((a : ℝ) • p (ξ 0) ∉ U → T ξ = 0 ∧ τ = 0) ∧
      ((a : ℝ) • p (ξ 0) ∈ U → ∃ n : ℕ,
        T ξ = (n + 1 : ℕ) ∧ τ ≠ ∞ ∧
        (a : ℝ) ^ 2 * H.jumpTime ξ n < (τ.toNNReal : ℝ) ∧
        (τ.toNNReal : ℝ) ≤ (a : ℝ) ^ 2 * H.jumpTime ξ (n + 1) ∧
        dist ((H.interpolatedWalk p a ξ) τ.toNNReal)
          ((a : ℝ) • p (stopState T ξ)) ≤
          (a : ℝ) * (Metric.diam ((ξ n).1 : Set Plane) +
            Metric.diam ((ξ (n + 1)).1 : Set Plane))) := by
  filter_upwards [hunb, hadj, hvisit] with ω hω ha hv
  intro k p hp a hscale U hbounded hopen hconv
  have hclock := jumpTimesUnbounded_shift H ω hpos hω k
  have hedge : ∀ n, H.Adj (ω (k + n)) (ω (k + (n + 1))) := by
    intro n
    simpa only [Nat.add_assoc] using ha (k + n)
  constructor
  · intro hout
    exact exterior_hitTime_and_exit_eq_zero H p (fun n => ω (k + n))
      hpos hclock hscale U hout
  · intro hin
    exact continuousExitTime_bracket_of_hitTime H hH p hp (fun n => ω (k + n))
      hpos hclock hedge hscale hopen hconv hin (hv k p hp a hscale U hbounded)

end LatticeProb.CellConfigInterpolation
end
