import LatticeProb.Prob.ConeVectorPairDimension
import LatticeProb.Prob.CorrelatedBMForwardConeGlobalSurvival
import LatticeProb.Prob.CorrelatedBMBackwardConeGlobalSurvival

/-! # Dimension of direct-excursion pairs from joint survival -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A joint survival estimate bounds the dimension of direct-excursion pairs. -/
theorem ae_dimH_direct_excursion_pairs_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C p : ℝ) (hC : 0 < C)
    (hslack : 2 < (β : ℝ) + (α : ℝ) * (p + 2))
    (hJ : ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
          ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ β := by
  have hf := ae_dimH_forwardConeVectors_le_of_joint_survival hμ α β hα hβ C p hC hslack hJ
  have hb := ae_dimH_backwardConeVectors_global_le_of_joint_survival hμ α β hα hβ C p hC hslack hJ
  apply ae_dimH_direct_excursion_pairs_le_of_coneVectors hμ
  · filter_upwards [hf] with ω hω
    simpa only [one_mul] using hω 1 (Or.inl rfl)
  · filter_upwards [hb] with ω hω
    simpa only [one_mul] using hω 1 (Or.inl rfl)
  · filter_upwards [hf] with ω hω
    simpa only [neg_one_mul] using hω (-1) (Or.inr rfl)
  · filter_upwards [hb] with ω hω
    simpa only [neg_one_mul] using hω (-1) (Or.inr rfl)

end LatticeProb.CorrelatedBM
