import LatticeProb.Prob.CorrelatedBMConeGridPower
import LatticeProb.Prob.CorrelatedBMJointWindowTransfer
import LatticeProb.Prob.CorrelatedBMConeSeparatedGridDimension

/-! # Cone-vector dimension from joint Brownian survival -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A uniform joint survival estimate bounds the dimension of separated backward
cone vectors, for either the original or time-reflected path. The survival
constant may depend on the window length. -/
theorem ae_dimH_backwardConeVectors_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C d q p direction : ℝ) (hC : 0 < C) (hd : 0 < d) (hq : 0 < q)
    (hdir : direction = 1 ∨ direction = -1)
    (hslack : 2 < (β : ℝ) + (α : ℝ) * (p + 2))
    (hJ : ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
          ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ,
      dimH {z : ℝ × ℝ |
        let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
        let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
        z ∈ backwardConeVectors X Y ∧ 0 < z.1 ∧ z.2 < 1 ∧
          d < z.2 - z.1 ∧ q < z.2 - coneFirstExitBackward X Y z.2} ≤ β := by
  apply ae_dimH_backwardConeVectors_le_of_separated_grid_cost hμ α β hα hβ
    C d q direction hC hd hq hdir
  intro k
  obtain ⟨h, hh, hH, hsep⟩ := exists_cone_window k d hd
  obtain ⟨B, hB, hbound⟩ := hJ h hh
  rcases hdir with rfl | rfl
  · apply exists_finite_one_grid_cost_bound_of_joint_power hμ C (α : ℝ) h d B p k β
      hC hh hH hsep hB hslack
    intro n b
    exact measure_jointBackwardBarrier_le hμ _ h hh.le _ (hbound n) b
  · apply exists_finite_neg_one_grid_cost_bound_of_joint_power hμ C (α : ℝ) h d B p k β
      hC hh hH hsep hB hslack
    intro n b
    exact measure_jointForwardBarrier_le hμ _ h hh.le _ (hbound n) b

end LatticeProb.CorrelatedBM
