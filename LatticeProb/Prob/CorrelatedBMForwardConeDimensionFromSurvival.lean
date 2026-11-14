import LatticeProb.Prob.CorrelatedBMForwardConeSeparatedGridDimension
import LatticeProb.Prob.CorrelatedBMConeDimensionFromSurvival

/-! # Forward cone-vector dimension from joint Brownian survival -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Joint survival bounds the separated forward cone-vector dimension on a
negative unit interval, for either orientation of the Brownian path. -/
theorem ae_dimH_forwardConeVectors_neg_unit_le_of_joint_survival
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β : ℝ≥0) (hα : (α : ℝ) < 1 / 2) (hβ : 0 < β)
    (C d p direction : ℝ) (hC : 0 < C) (hd : 0 < d)
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
        z ∈ forwardConeVectors X Y ∧ -1 < z.2 ∧ z.1 < 0 ∧
          d < z.1 - z.2} ≤ β := by
  have hbound := ae_dimH_reflected_forwardConeVectors_le_of_separated_grid_cost
    hμ α β hα hβ C d direction hC hd hdir (by
      intro k
      obtain ⟨h, hh, hH, hsep⟩ := exists_cone_window k d hd
      obtain ⟨B, hB, hJ⟩ := hJ h hh
      rcases hdir with rfl | rfl
      · apply exists_finite_neg_one_grid_cost_bound_of_joint_power hμ C (α : ℝ) h d B p k β
          hC hh hH hsep hB hslack
        intro n b
        exact measure_jointForwardBarrier_le hμ _ h hh.le _ (hJ n) b
      · simp only [neg_neg]
        apply exists_finite_one_grid_cost_bound_of_joint_power hμ C (α : ℝ) h d B p k β
          hC hh hH hsep hB hslack
        intro n b
        exact measure_jointBackwardBarrier_le hμ _ h hh.le _ (hJ n) b)
  filter_upwards [hbound] with ω hω
  have hn : LipschitzWith 1 (fun z : ℝ × ℝ => (-z.1, -z.2)) := by
    simpa only [max_self, Pi.neg_apply] using
      (LipschitzWith.prod_fst.neg.prodMk LipschitzWith.prod_snd.neg :
        LipschitzWith (max 1 1) (fun z : ℝ × ℝ => (-z.1, -z.2)))
  apply (dimH_mono ?_).trans ((hn.dimH_image_le _).trans hω)
  intro z hz
  refine ⟨(-z.1, -z.2), ?_, by simp only [neg_neg, Prod.mk.eta]⟩
  rcases hz with ⟨hv, hs, ha, hsep⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [neg_neg, Prod.mk.eta] using hv
  · simpa using ha
  · linarith
  · linarith

end LatticeProb.CorrelatedBM
