import LatticeProb.Analysis.Schauder.ChainDeriv
import LatticeProb.Analysis.Schauder.KernelDerivDom
import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.KernelIntegral
import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# Integrability of the third and fourth space derivatives of the heat kernel

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` and `t > 0`, the nested directional
derivatives `∂_a ∂_b ∂_c p_t` and `∂_a ∂_b ∂_c ∂_e p_t` are integrable.

The nested derivative is smooth, hence continuous and measurable. At each point it is bounded by
the norm of the corresponding iterated Fréchet derivative of `p_t` times the product of the norms
of the directions (`ChainDeriv.lean`). The domination `‖D^n p_t(y)‖ ≤ C (1/√t)^n p_{2t}(y)` of
`KernelDerivDom.lean` then bounds the nested derivative by a constant multiple of the doubled-time
heat kernel, which is integrable.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Third derivatives of the heat kernel are integrable. -/
theorem integrable_dirDeriv_three_heatKernel {t : ℝ} (ht : 0 < t) (a b c : Euc d) :
    Integrable (dirDeriv a (dirDeriv b (dirDeriv c (heatKernel d t)))) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (heatKernel d t) := (contDiff_heatKernel t).of_le le_top
  have hc : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv a (dirDeriv b (dirDeriv c (heatKernel d t)))) :=
    contDiff_dirDeriv (contDiff_dirDeriv (contDiff_dirDeriv hs c) b) a
  have h3 : ContDiff ℝ 3 (heatKernel d t) := hs.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_le (d := d) 3 0
  refine ((integrable_heatKernel (d := d) (by positivity : 0 < 2 * t)).const_mul
    (C * (1 / Real.sqrt t) ^ 3 * (‖a‖ * ‖b‖ * ‖c‖))).mono' hc.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  have h := hC t ht y
  simp only [pow_zero, mul_one] at h
  calc |dirDeriv a (dirDeriv b (dirDeriv c (heatKernel d t))) y|
      ≤ ‖iteratedFDeriv ℝ 3 (heatKernel d t) y‖ * (‖a‖ * ‖b‖ * ‖c‖) :=
        abs_dirDeriv_three_le h3 y a b c
    _ ≤ C * (1 / Real.sqrt t) ^ 3 * heatKernel d (2 * t) y * (‖a‖ * ‖b‖ * ‖c‖) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = C * (1 / Real.sqrt t) ^ 3 * (‖a‖ * ‖b‖ * ‖c‖) * heatKernel d (2 * t) y := by ring

/-- Fourth derivatives of the heat kernel are integrable. -/
theorem integrable_dirDeriv_four_heatKernel {t : ℝ} (ht : 0 < t) (a b c e : Euc d) :
    Integrable (dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e (heatKernel d t))))) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (heatKernel d t) := (contDiff_heatKernel t).of_le le_top
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e (heatKernel d t))))) :=
    contDiff_dirDeriv (contDiff_dirDeriv (contDiff_dirDeriv (contDiff_dirDeriv hs e) c) b) a
  have h4 : ContDiff ℝ 4 (heatKernel d t) := hs.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_le (d := d) 4 0
  refine ((integrable_heatKernel (d := d) (by positivity : 0 < 2 * t)).const_mul
    (C * (1 / Real.sqrt t) ^ 4 * (‖a‖ * ‖b‖ * ‖c‖ * ‖e‖))).mono'
    hc.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  have h := hC t ht y
  simp only [pow_zero, mul_one] at h
  calc |dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e (heatKernel d t)))) y|
      ≤ ‖iteratedFDeriv ℝ 4 (heatKernel d t) y‖ * (‖a‖ * ‖b‖ * ‖c‖ * ‖e‖) :=
        abs_dirDeriv_four_le h4 y a b c e
    _ ≤ C * (1 / Real.sqrt t) ^ 4 * heatKernel d (2 * t) y * (‖a‖ * ‖b‖ * ‖c‖ * ‖e‖) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = C * (1 / Real.sqrt t) ^ 4 * (‖a‖ * ‖b‖ * ‖c‖ * ‖e‖) * heatKernel d (2 * t) y := by
        ring

end

end LatticeProb.Analysis.Schauder
