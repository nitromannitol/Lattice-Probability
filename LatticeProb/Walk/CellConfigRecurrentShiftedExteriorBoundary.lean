import LatticeProb.Walk.CellConfigExteriorBoundary
import LatticeProb.Walk.CellConfigRecurrentShiftedExteriorBracket

/-! # Frontier proximity for restarted cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A recurrent cell walk has, simultaneously for every restart and admissible
representative selection, an exterior hit near the frontier of each bounded
open convex domain. -/
theorem ae_frontier_near_exterior_hit_all_shifts_of_recurrent (H : CellConfig)
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
        ∃ z ∈ frontier U, dist ((a : ℝ) • p (stopState T ξ)) z ≤
          (a : ℝ) * (Metric.diam ((ξ n).1 : Set Plane) +
            Metric.diam ((ξ (n + 1)).1 : Set Plane))) := by
  have hpos : ∀ C, 0 < H.holding C :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hμ
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
    exact exists_frontier_near_exterior_hit H hH p hp (fun n => ω (k + n))
      hpos hclock hedge hscale hopen hconv hin (hv k p hp a hscale U hbounded)

end LatticeProb.CellConfigInterpolation
end
