import LatticeProb.Walk.CellConfigRecurrentShiftedFrontierExit
import LatticeProb.Walk.CellConfigStoppedExitComparison

/-! # Stopped interpolated paths at exterior exits -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Simultaneously for all restarts, the path stopped on exiting an open convex
set and the path stopped at the first exterior representative are close,
under a local bound on adjacent cell diameters. -/
theorem ae_stopped_exit_comparison_all_shifts_of_recurrent (H : CellConfig)
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
      ∀ d : ℝ, (∀ C D, (a : ℝ) • p C ∈ U → H.Adj C D →
        Metric.diam (C.1 : Set Plane) + Metric.diam (D.1 : Set Plane) ≤ d) →
      let ξ := fun n => ω (k + n)
      let T := hitTime {C : H.cells | (a : ℝ) • p C ∉ U}
      let τ := continuousExitTime U 0 (H.interpolatedWalk p a ξ)
      ((a : ℝ) • p (ξ 0) ∉ U → T ξ = 0 ∧ τ = 0) ∧
      ((a : ℝ) • p (ξ 0) ∈ U → ∃ n : ℕ,
        T ξ = (n + 1 : ℕ) ∧ τ ≠ ∞ ∧
        ∀ t : ℝ≥0,
          dist ((H.interpolatedWalk p a ξ) (min t τ.toNNReal))
            ((H.interpolatedWalk p a ξ) (min t
              ⟨(a : ℝ) ^ 2 * H.jumpTime ξ (n + 1),
                mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg
                  (LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne) (n + 1))⟩)) ≤
            2 * ((a : ℝ) * d)) := by
  have hpos : ∀ C, 0 < H.holding C :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hμ
  filter_upwards [ae_frontier_exit_bracket_all_shifts_of_recurrent H hH hne hrec hμ
    hadj hvisit, hadj, hunb] with ω hbr hstep hclock
  intro k p hp a ha U hbound hopen hconv d hd
  obtain ⟨hout, hin⟩ := hbr k p hp a ha U hbound hopen hconv
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, _, _⟩ := hin hstart
  have hinside : (a : ℝ) • p (ω (k + n)) ∈ U := by
    have h := (hitTime_eq_coe_iff.mp hn).2 n (Nat.lt_succ_self n)
    exact not_not.mp h
  have hedge : H.Adj (ω (k + n)) (ω (k + (n + 1))) := by
    simpa only [Nat.add_assoc] using hstep (k + n)
  have hshift := jumpTimesUnbounded_shift H ω hpos hclock k
  refine ⟨n, hn, hf, fun t => ?_⟩
  have hcmp := dist_stopped_interpolatedWalk_le_of_same_edge H hH p hp
    (fun j => ω (k + j)) hpos hshift ha n hedge
    (continuousExitTime U 0 (H.interpolatedWalk p a (fun j => ω (k + j)))).toNNReal
    ⟨(a : ℝ) ^ 2 * H.jumpTime (fun j => ω (k + j)) (n + 1),
      mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩
    hlo.le hhi (hlo.le.trans hhi) le_rfl t
  exact le_trans hcmp (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hd _ _ hinside hedge) a.coe_nonneg) (by norm_num))

end LatticeProb.CellConfigInterpolation
end
