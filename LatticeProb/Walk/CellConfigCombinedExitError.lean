import LatticeProb.Walk.CellConfigLocalExitError
import LatticeProb.Walk.CellConfigRecurrentStoppedExit

/-! # Joint exit errors for interpolated cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The clock, endpoint and stopped path errors are controlled at the same
exterior edge, simultaneously over all shifts and admissible domains. -/
theorem ae_combined_exit_error_all_shifts_of_recurrent (H : CellConfig)
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
          ((a : ℝ) • p (stopState T ξ)) ≤ (a : ℝ) * d ∧
        ∀ t : ℝ≥0,
          dist ((H.interpolatedWalk p a ξ) (min t τ.toNNReal))
            ((H.interpolatedWalk p a ξ) (min t
              ⟨(a : ℝ) ^ 2 * H.jumpTime ξ (n + 1),
                mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg
                  (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne) (n + 1))⟩)) ≤
            2 * ((a : ℝ) * d)) := by
  filter_upwards [ae_local_exit_error_all_shifts_of_recurrent H hH hne hrec hμ hadj hvisit,
    ae_stopped_exit_comparison_all_shifts_of_recurrent H hH hne hrec hμ hadj hvisit] with
    ω hlocal hstopped
  intro k p hp a ha U hbound hopen hconv b d hb hd
  obtain ⟨hout, hin⟩ := hlocal k p hp a ha U hbound hopen hconv b d hb hd
  obtain ⟨_, hin'⟩ := hstopped k p hp a ha U hbound hopen hconv d hd
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist⟩ := hin hstart
  obtain ⟨m, hm, _, hpath⟩ := hin' hstart
  have hnm : n = m := by
    have h : (n + 1 : ℕ∞) = (m + 1 : ℕ∞) := hn.symm.trans hm
    exact Nat.succ.inj (ENat.natCast_inj.mp h)
  subst m
  exact ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist, hpath⟩

end LatticeProb.CellConfigInterpolation
end
