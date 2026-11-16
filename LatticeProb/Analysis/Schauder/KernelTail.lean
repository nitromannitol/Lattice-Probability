import LatticeProb.Analysis.Schauder.ChainDeriv
import LatticeProb.Analysis.Schauder.KernelDerivDom
import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# Nested directional derivatives of the heat kernel away from the origin

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d`, every derivative `D^n p_t` is, outside the
ball of radius `δ > 0`, dominated by a constant multiple of `p_{4t}`, uniformly in `t > 0`
(`KernelDerivDom.lean`).

The nested directional derivatives `∂_a ∂_b p_t`, `∂_e ∂_a ∂_b p_t` and `∂_{e'} ∂_e ∂_a ∂_b p_t`
are values of `D²p_t`, `D³p_t` and `D⁴p_t` on tuples of directions, so they are bounded by the norm
of the iterated derivative times the product of the norms of the directions
(`ChainDeriv.lean`). Taking `M` to be the sum of the three constants for `n = 2, 3, 4`, and using
that `a` and `b` are in the unit ball, the three nested derivatives are bounded by `M p_{4t}`,
`M ‖e‖ p_{4t}` and `M ‖e‖ ‖e'‖ p_{4t}` respectively, for `‖y‖ ≥ δ` and uniformly in `t > 0`.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- Away from the origin the second, third and fourth derivatives of `p_t` are dominated by
`p_{4t}`, uniformly in `t > 0` and in unit directions `a, b`. -/
theorem exists_heatKernel_chain_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → ∀ a b : Euc d, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∀ y, δ ≤ ‖y‖ →
        |dirDeriv a (dirDeriv b (heatKernel d t)) y| ≤ M * heatKernel d (4 * t) y) ∧
      (∀ y e, δ ≤ ‖y‖ → |dirDeriv e (dirDeriv a (dirDeriv b (heatKernel d t))) y| ≤
        M * ‖e‖ * heatKernel d (4 * t) y) ∧
      (∀ y e e', δ ≤ ‖y‖ →
        |dirDeriv e' (dirDeriv e (dirDeriv a (dirDeriv b (heatKernel d t)))) y| ≤
          M * ‖e‖ * ‖e'‖ * heatKernel d (4 * t) y) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_iteratedFDeriv_heatKernel_le_of_le_norm (d := d) 2 hδ
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_norm_iteratedFDeriv_heatKernel_le_of_le_norm (d := d) 3 hδ
  obtain ⟨C₄, hC₄0, hC₄⟩ := exists_norm_iteratedFDeriv_heatKernel_le_of_le_norm (d := d) 4 hδ
  refine ⟨C₂ + C₃ + C₄, by positivity, fun t ht a b ha hb => ?_⟩
  have hs : ContDiff ℝ (⊤ : ℕ∞) (heatKernel d t) := (contDiff_heatKernel t).of_le le_top
  have h2 : ContDiff ℝ 2 (heatKernel d t) := hs.of_le (WithTop.coe_le_coe.2 le_top)
  have h3 : ContDiff ℝ 3 (heatKernel d t) := hs.of_le (WithTop.coe_le_coe.2 le_top)
  have h4 : ContDiff ℝ 4 (heatKernel d t) := hs.of_le (WithTop.coe_le_coe.2 le_top)
  have hab : ‖a‖ * ‖b‖ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.2 ha) (norm_nonneg b)]
  have hp : ∀ y : Euc d, 0 ≤ heatKernel d (4 * t) y := fun y =>
    heatKernel_nonneg (by positivity) y
  refine ⟨fun y hy => ?_, fun y e hy => ?_, fun y e e' hy => ?_⟩
  · calc |dirDeriv a (dirDeriv b (heatKernel d t)) y|
        ≤ ‖iteratedFDeriv ℝ 2 (heatKernel d t) y‖ * (‖a‖ * ‖b‖) :=
          abs_dirDeriv_two_le h2 y a b
      _ ≤ (C₂ * heatKernel d (4 * t) y) * 1 :=
          mul_le_mul (hC₂ t ht y hy) hab (by positivity) (by have := hp y; positivity)
      _ ≤ (C₂ + C₃ + C₄) * heatKernel d (4 * t) y := by
          nlinarith [mul_nonneg (add_nonneg hC₃0 hC₄0) (hp y)]
  · have he : ‖e‖ * ‖a‖ * ‖b‖ ≤ ‖e‖ := by
      rw [mul_assoc]
      exact mul_le_of_le_one_right (norm_nonneg _) hab
    calc |dirDeriv e (dirDeriv a (dirDeriv b (heatKernel d t))) y|
        ≤ ‖iteratedFDeriv ℝ 3 (heatKernel d t) y‖ * (‖e‖ * ‖a‖ * ‖b‖) :=
          abs_dirDeriv_three_le h3 y e a b
      _ ≤ (C₃ * heatKernel d (4 * t) y) * ‖e‖ :=
          mul_le_mul (hC₃ t ht y hy) he (by positivity) (by have := hp y; positivity)
      _ ≤ (C₂ + C₃ + C₄) * ‖e‖ * heatKernel d (4 * t) y := by
          nlinarith [mul_nonneg (add_nonneg hC₂0 hC₄0) (mul_nonneg (norm_nonneg e) (hp y))]
  · have he : ‖e'‖ * ‖e‖ * ‖a‖ * ‖b‖ ≤ ‖e'‖ * ‖e‖ := by
      rw [mul_assoc (‖e'‖ * ‖e‖)]
      exact mul_le_of_le_one_right (by positivity) hab
    calc |dirDeriv e' (dirDeriv e (dirDeriv a (dirDeriv b (heatKernel d t)))) y|
        ≤ ‖iteratedFDeriv ℝ 4 (heatKernel d t) y‖ * (‖e'‖ * ‖e‖ * ‖a‖ * ‖b‖) :=
          abs_dirDeriv_four_le h4 y e' e a b
      _ ≤ (C₄ * heatKernel d (4 * t) y) * (‖e'‖ * ‖e‖) :=
          mul_le_mul (hC₄ t ht y hy) he (by positivity) (by have := hp y; positivity)
      _ ≤ (C₂ + C₃ + C₄) * ‖e‖ * ‖e'‖ * heatKernel d (4 * t) y := by
          nlinarith [mul_nonneg (add_nonneg hC₂0 hC₃0)
            (mul_nonneg (mul_nonneg (norm_nonneg e) (norm_nonneg e')) (hp y))]

end

end LatticeProb.Analysis.Schauder
