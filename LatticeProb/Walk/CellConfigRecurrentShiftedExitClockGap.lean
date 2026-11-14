import LatticeProb.Walk.CellConfigRecurrentShiftedFrontierExit

/-! # Exit clock gaps for restarted cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The exit clock lies within one scaled holding time of the first exterior
jump, simultaneously for all restarts and admissible domains. -/
theorem ae_frontier_exit_clock_gap_all_shifts_of_recurrent (H : CellConfig)
    (hH : H.IsCellConfiguration)
    (hne : ∀ C : H.cells, ∃ C' : H.cells, H.Adj C C')
    (hrec : H.Recurrent) {x : H.cells} {μ : Measure (ℕ → H.cells)}
    (hμ : H.IsSRWLaw x μ)
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
        0 ≤ (a : ℝ) ^ 2 * H.jumpTime ξ (n + 1) - (τ.toNNReal : ℝ) ∧
        (a : ℝ) ^ 2 * H.jumpTime ξ (n + 1) - (τ.toNNReal : ℝ) <
          (a : ℝ) ^ 2 * H.holding (ξ n) ∧
        (H.interpolatedWalk p a ξ) τ.toNNReal ∈ frontier U ∧
        dist ((H.interpolatedWalk p a ξ) τ.toNNReal)
          ((a : ℝ) • p (stopState T ξ)) ≤
          (a : ℝ) * (Metric.diam ((ξ n).1 : Set Plane) +
            Metric.diam ((ξ (n + 1)).1 : Set Plane))) := by
  filter_upwards [ae_frontier_exit_bracket_all_shifts_of_recurrent H hH hne hrec hμ
    hadj hvisit] with ω hω
  intro k p hp a ha U hbound hopen hconv
  obtain ⟨hout, hin⟩ := hω k p hp a ha U hbound hopen hconv
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hfrontier, hd⟩ := hin hstart
  refine ⟨n, hn, hf, hlo, hhi, sub_nonneg.mpr hhi, ?_, hfrontier, hd⟩
  rw [H.jumpTime_succ, mul_add]
  linarith

end LatticeProb.CellConfigInterpolation
end
