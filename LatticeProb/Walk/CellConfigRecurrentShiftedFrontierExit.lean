import LatticeProb.Walk.CellConfigRecurrentShiftedExteriorBracket
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties

/-! # Frontier exit points for restarted cell walks -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- For every restart and admissible domain, a recurrent cell walk started
inside exits at a frontier point close to its first exterior representative. -/
theorem ae_frontier_exit_bracket_all_shifts_of_recurrent (H : CellConfig)
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
        (H.interpolatedWalk p a ξ) τ.toNNReal ∈ frontier U ∧
        dist ((H.interpolatedWalk p a ξ) τ.toNNReal)
          ((a : ℝ) • p (stopState T ξ)) ≤
          (a : ℝ) * (Metric.diam ((ξ n).1 : Set Plane) +
            Metric.diam ((ξ (n + 1)).1 : Set Plane))) := by
  have hpos : ∀ C, 0 < H.holding C :=
    LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH hne
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hμ
  filter_upwards [ae_exterior_hit_bracket_all_shifts_of_recurrent H hH hne hrec hμ hadj hvisit,
    hunb] with ω hbr hω
  intro k p hp a ha U hbound hopen hconv
  obtain ⟨hout, hin⟩ := hbr k p hp a ha U hbound hopen hconv
  refine ⟨hout, ?_⟩
  intro hstart
  obtain ⟨n, hn, hf, hlo, hhi, hd⟩ := hin hstart
  refine ⟨n, hn, hf, hlo, hhi, ?_, hd⟩
  have hclock := jumpTimesUnbounded_shift H ω hpos hω k
  have hz : (⟨(a : ℝ) ^ 2 * H.jumpTime (fun n => ω (k + n)) 0,
      mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos 0)⟩ : ℝ≥0) = 0 := by
    apply Subtype.ext
    simp [CellConfig.jumpTime]
  have hw := interpolatedWalk_at_jumpTime H p (fun n => ω (k + n)) hpos hclock 0 ha
  rw [hz] at hw
  have hstart0 : (0 : Plane) + H.interpolatedWalk p a (fun n => ω (k + n)) 0 ∈ U := by
    simpa only [zero_add] using hw.symm ▸ hstart
  simpa only [zero_add] using continuousExitTime_mem_frontier hopen hstart0 hf

end LatticeProb.CellConfigInterpolation
end
