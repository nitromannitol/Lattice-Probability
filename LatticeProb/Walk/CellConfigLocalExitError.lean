import LatticeProb.Walk.CellConfigRecurrentShiftedExitClockGap

/-! # Local error bounds at the exit of a cell walk -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Bounds on holding times and adjacent cell diameters for interior
representatives control the clock and endpoint errors at each exit. -/
theorem ae_local_exit_error_all_shifts_of_recurrent (H : CellConfig)
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
      ∀ b d : ℝ,
      (∀ C, (a : ℝ) • p C ∈ U → H.holding C ≤ b) →
      (∀ C D, (a : ℝ) • p C ∈ U → H.Adj C D →
        Metric.diam (C.1 : Set Plane) + Metric.diam (D.1 : Set Plane) ≤ d) →
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
          (a : ℝ) ^ 2 * b ∧
        (H.interpolatedWalk p a ξ) τ.toNNReal ∈ frontier U ∧
        dist ((H.interpolatedWalk p a ξ) τ.toNNReal)
          ((a : ℝ) • p (stopState T ξ)) ≤ (a : ℝ) * d) := by
  filter_upwards [ae_frontier_exit_clock_gap_all_shifts_of_recurrent H hH hne hrec hμ
    hadj hvisit, hadj] with ω hω hstep
  intro k p hp a ha U hU hopen hconv b d hb hd
  obtain ⟨hout, hin⟩ := hω k p hp a ha U hU hopen hconv
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist⟩ := hin hstart
  have hinside : (a : ℝ) • p (ω (k + n)) ∈ U := by
    have h := (hitTime_eq_coe_iff.mp hn).2 n (Nat.lt_succ_self n)
    exact not_not.mp h
  have hpair : H.Adj (ω (k + n)) (ω (k + (n + 1))) := by
    simpa only [Nat.add_assoc] using hstep (k + n)
  refine ⟨n, hn, hf, hlo, hhi, hnonneg, ?_, hfront, ?_⟩
  · exact lt_of_lt_of_le hgap (mul_le_mul_of_nonneg_left (hb _ hinside) (sq_nonneg _))
  · exact le_trans hdist (mul_le_mul_of_nonneg_left (hd _ _ hinside hpair) a.coe_nonneg)

end LatticeProb.CellConfigInterpolation
end
