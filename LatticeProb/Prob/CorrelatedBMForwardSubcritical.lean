import LatticeProb.Prob.CorrelatedBMForwardWedgeMeasure
import LatticeProb.Prob.BrownianWedgeSurvivalSubcritical
import LatticeProb.Prob.BrownianOccupationTrunc

/-! # Subcritical forward wedge survival -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A uniform subcritical power bound for a forward strict wedge barrier. -/
theorem forward_wedge_barrier_subcritical {θ p r : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hr : 0 < r) (hrp : r < p)
    (hpθ : p * θ < Real.pi) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {μ : Measure Path2}, IsCorrelatedBM2 (Real.sqrt 2) μ →
        ∀ (q : ℝ) (T : ℝ≥0), 0 < (T : ℝ) →
        let a := Real.sin (θ / 2)
        let b := Real.cos (θ / 2)
        let x := normalizedWedgeStart a q
        let J : EuclideanSpace ℝ (Fin 2) → ℂ := Complex.orthonormalBasisOneI.repr.symm
        x ∈ closure {y | ((J y).re, (J y).im) ∈ openSymmetricWedge a b} →
        μ.real (openSymmetricWedgeBarrier a b q T) ≤
          K * (‖x‖ / Real.sqrt (T : ℝ)) ^ r := by
  obtain ⟨K, hK, hbound⟩ := brownian_wedge_survival_subcritical hθ0 hθπ hr hrp hpθ
  refine ⟨K, hK, ?_⟩
  intro μ hμ q T hT
  dsimp only
  intro hx
  have ha : Real.sin (θ / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hB := (isBrownianSpace_normalizedForwardSpace hμ).const_add
    (normalizedWedgeStart (Real.sin (θ / 2)) q)
  have hb := hbound hB T hT hx
  rw [measureReal_def, measure_openSymmetricWedgeBarrier_eq_normalized_forward hμ _ _ _ ha T]
  exact hb

end LatticeProb.CorrelatedBM
