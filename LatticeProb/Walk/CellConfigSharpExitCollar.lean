import LatticeProb.Walk.CellConfigSharpCombinedExit
import LatticeProb.Walk.CellConfigStoppedExitCollar

/-! # Joint exit estimates and containment in a collar -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The sharp clock, endpoint and path bounds and the collar containment hold
simultaneously for the same exterior edge. -/
theorem ae_sharp_exit_error_and_collar_all_shifts_of_recurrent (H : CellConfig)
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
        (∀ t : ℝ≥0,
          dist ((H.interpolatedWalk p a ξ) (min t τ.toNNReal))
            ((H.interpolatedWalk p a ξ) (min t
              ⟨(a : ℝ) ^ 2 * H.jumpTime ξ (n + 1),
                mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg
                  (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne) (n + 1))⟩)) ≤
            (a : ℝ) * d) ∧
        ∀ t : ℝ≥0,
          H.interpolatedWalk p a ξ (min t
            ⟨(a : ℝ) ^ 2 * H.jumpTime ξ (n + 1),
              mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg
                (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne) (n + 1))⟩)
            ∈ Metric.cthickening ((a : ℝ) * d) U) := by
  have hpos : ∀ C, 0 < H.holding C :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hμ
  filter_upwards [ae_sharp_combined_exit_error_all_shifts_of_recurrent
    H hH hne hrec hμ hadj hvisit, hadj, hunb] with ω hsharp hstep hclock
  intro k p hp a ha U hbound hopen hconv b d hb hd
  obtain ⟨hout, hin⟩ := hsharp k p hp a ha U hbound hopen hconv b d hb hd
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist, hpaths⟩ := hin hstart
  refine ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist, hpaths, ?_⟩
  have hshift := jumpTimesUnbounded_shift H ω hpos hclock k
  have hstep' : ∀ j, H.Adj (ω (k + j)) (ω (k + (j + 1))) := by
    intro j
    simpa only [Nat.add_assoc] using hstep (k + j)
  have hdiam : ∀ j < n + 1, Metric.diam ((ω (k + j)).1 : Set Plane) +
      Metric.diam ((ω (k + (j + 1))).1 : Set Plane) ≤ d := by
    intro j hj
    have hinside : (a : ℝ) • p (ω (k + j)) ∈ U :=
      not_not.mp ((hitTime_eq_coe_iff.mp hn).2 j hj)
    exact hd _ _ hinside (hstep' j)
  intro t
  exact stopped_interpolatedWalk_mem_cthickening_of_exterior_hit H hH p hp
    (fun j => ω (k + j)) hpos hshift hstep' ha U n d hn hdiam t

end LatticeProb.CellConfigInterpolation
end
