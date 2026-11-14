import LatticeProb.Walk.CellConfigLocalExitError
import LatticeProb.Walk.CellConfigRecurrentStoppedExit
import LatticeProb.Walk.CellConfigEdgeOscillation

/-! # Sharp joint exit errors for interpolated cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- The clock, endpoint and stopped path errors are controlled at the same
exterior edge, simultaneously over all shifts and admissible domains. -/
theorem ae_sharp_combined_exit_error_all_shifts_of_recurrent (H : CellConfig)
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
            (a : ℝ) * d) := by
  have hpos : ∀ C, 0 < H.holding C :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hμ
  filter_upwards [ae_local_exit_error_all_shifts_of_recurrent H hH hne hrec hμ hadj hvisit,
    hadj, hunb] with ω hlocal hstep hclock
  intro k p hp a ha U hbound hopen hconv b d hb hd
  obtain ⟨hout, hin⟩ := hlocal k p hp a ha U hbound hopen hconv b d hb hd
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist⟩ := hin hstart
  have hinside : (a : ℝ) • p (ω (k + n)) ∈ U := by
    have h := (hitTime_eq_coe_iff.mp hn).2 n (Nat.lt_succ_self n)
    exact not_not.mp h
  have hedge : H.Adj (ω (k + n)) (ω (k + (n + 1))) := by
    simpa only [Nat.add_assoc] using hstep (k + n)
  have hshift := jumpTimesUnbounded_shift H ω hpos hclock k
  refine ⟨n, hn, hf, hlo, hhi, hnonneg, hgap, hfront, hdist, fun t => ?_⟩
  have hcmp := dist_stopped_interpolatedWalk_le_edge H p
    (fun j => ω (k + j)) hpos hshift ha n
    (continuousExitTime U 0 (H.interpolatedWalk p a (fun j => ω (k + j)))).toNNReal
    ⟨(a : ℝ) ^ 2 * H.jumpTime (fun j => ω (k + j)) (n + 1),
      mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩
    hlo.le hhi (hlo.le.trans hhi) le_rfl t
  exact hcmp.trans (mul_le_mul_of_nonneg_left
    ((dist_representatives_le H hH p hp hedge).trans (hd _ _ hinside hedge)) a.coe_nonneg)

end LatticeProb.CellConfigInterpolation
end
