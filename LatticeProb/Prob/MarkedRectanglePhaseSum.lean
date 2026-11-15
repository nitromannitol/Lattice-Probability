import LatticeProb.Prob.MarkedRectanglePhaseFinite
import LatticeProb.Prob.TVFiniteSum

/-! Total variation bounds for finite sums of marked rectangle phase laws. -/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LatticeProb

/-- Finite mixtures of marked normalized rectangles have phase laws close to
independent uniform cube laws, with the sum of the individual errors. -/
theorem tvDist_sum_marked_rectangle_phase_le {E ι : Type*} [MeasurableSpace E]
    (s : Finset ι) (ρ : ι → Measure E) [∀ j, IsFiniteMeasure (ρ j)] (n : ℕ)
    (u v : ι → Fin n → ℝ) (huv : ∀ j ∈ s, ∀ i, u j i < v j i)
    {a : ℝ} (ha : 0 < a) (θ : E → (Fin n → ℝ)) (hθ : Measurable θ) :
    QuantumZipper.TV.tvDist
      (∑ j ∈ s, ((ρ j).prod ((∏ i, ENNReal.ofReal (v j i - u j i))⁻¹ •
          volume.restrict (Set.univ.pi fun i => Ico (u j i) (v j i)))).map
        (fun p => (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))))
      (∑ j ∈ s, (ρ j).prod (unitCubeMeasure (Fin n))) ≤
      ∑ j ∈ s, ((∑ i, (ENNReal.ofReal (v j i - u j i))⁻¹) * ENNReal.ofReal a⁻¹) *
        ρ j Set.univ := by
  classical
  refine (tvDist_finset_sum_le s _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  exact tvDist_map_marked_rectangle_phase_finite_le (ρ j) n (u j) (v j) (huv j hj) ha θ hθ

end LatticeProb
