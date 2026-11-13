import LatticeProb.LQG.DimensionLFPPExponent
import LatticeProb.Bonanno.HigherDimLQGContinuity.Param.Prop18
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Exponent
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CircleCorollary

/-!
# The kernel-independent distance exponent at `ξ_γ = γ / d_γ`

For `ξ > 0`, `HigherDimLQGMetric.distExp 2 ξ` is the kernel-independent LFPP distance exponent
`Q(ξ)`: for every admissible kernel and every white noise, the LFPP distances of the band
regularization `H_{ε,1}` at parameter `ξ` have exponent `1 - ξ Q(ξ)`. Ding and Gwynne
(arXiv:1807.01072, Theorem 1.5) identify the circle-average LFPP exponent at `ξ_γ = γ / d_γ` as
`1 - ξ_γ Q_γ` with `Q_γ = 2/γ + γ/2`. The two regularizations have the same LFPP exponent
(coupled realization of the white noise and the whole-plane GFF), so

* `distExp_two_xiGamma`: `Q(ξ_γ) = Q_γ` for `γ ∈ (0, 2)`;
* `xiOfGamma_two_eq_xiGamma`: the inverse parametrization `Ξ(γ)` (the subcritical `ξ` with
  `Q(ξ) = 2/γ + γ/2`) equals `ξ_γ`;
* `distExp_two_eq_Q_iff`: for `ξ > 0`, `Q(ξ) = Q_γ` if and only if `ξ = ξ_γ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace LatticeProb.LQG

/-- **The distance exponent at `ξ_γ`.** For `γ ∈ (0, 2)`, the kernel-independent LFPP distance
exponent at `ξ_γ = γ / d_γ` is `Q_γ = 2/γ + γ/2`. Proof: on a coupled realization of a white noise,
its band regularization `H_{ε,1}` and the circle averages of the associated whole-plane GFF, the band
exponent `1 - ξ_γ Q(ξ_γ)` and the circle-average exponent `1 - ξ_γ Q_γ` (Ding-Gwynne Theorem 1.5)
are LFPP exponents of the same family, and an LFPP exponent is unique. -/
theorem distExp_two_xiGamma {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    HigherDimLQGMetric.distExp 2 (LQGMetric.xiGamma γ) = LQGMetric.Q γ := by
  have hξ : 0 < LQGMetric.xiGamma γ := LQGMetric.DG.xiGamma_pos hγ
  have hκ := HigherDimLFPP.isLFPPKernel_bumpKernel 2
  obtain ⟨Ω₀, _, P₀, W, H, h₀, hW, hH, hh⟩ := HigherDimLFPP.exists_coupledRealization hκ
  have : IsProbabilityMeasure P₀ := hW.isProbabilityMeasure
  have h1 : HigherDimLFPP.IsLFPPExponent H P₀ (LQGMetric.xiGamma γ)
      (1 - LQGMetric.xiGamma γ * HigherDimLQGMetric.distExp 2 (LQGMetric.xiGamma γ)) :=
    HigherDimLQGMetric.distExp_isDistanceExponent le_rfl hξ _ hκ Ω₀ P₀ W hW H hH
  have hG₀ := HigherDimLFPP.isGFFCircleAverage_of_isCircleVersion hκ hW hh
  have h2 : HigherDimLFPP.IsLFPPExponent H P₀ (LQGMetric.xiGamma γ)
      (1 - LQGMetric.xiGamma γ * LQGMetric.Q γ) :=
    (HigherDimLFPP.isLFPPExponent_iff_coupled hκ hW hH hh _ _).2
      (isLFPPExponent_xiGamma hγ hγ2 hG₀)
  have heq := HigherDimLQGMetric.isLFPPExponent_unique h1 h2
  exact mul_left_cancel₀ hξ.ne' (by linarith)

/-- In dimension two the critical value `√(2d)` of the parametrization is `2`. -/
theorem sqrt_two_mul_two : Real.sqrt (2 * ((2 : ℕ) : ℝ)) = 2 := by
  rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `G(γ) = 2/γ + γ/2` in dimension two is `Q_γ`. -/
theorem gammaQ_two_eq_Q (γ : ℝ) : HigherDimLQGContinuity.gammaQ 2 γ = LQGMetric.Q γ := by
  simp only [HigherDimLQGContinuity.gammaQ, LQGMetric.Q, Nat.cast_ofNat]

/-- The inverse parametrization `Ξ(γ)` of the distance exponent equals `ξ_γ = γ / d_γ` for
`γ ∈ (0, 2)`. -/
theorem xiOfGamma_two_eq_xiGamma {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    HigherDimLQGContinuity.xiOfGamma 2 γ = LQGMetric.xiGamma γ := by
  have hγ' : γ ∈ Ioo 0 (Real.sqrt (2 * ((2 : ℕ) : ℝ))) := by
    rw [sqrt_two_mul_two]; exact ⟨hγ, hγ2⟩
  exact ((HigherDimLQGContinuity.distExp_eq_gammaQ_iff le_rfl hγ' (LQGMetric.DG.xiGamma_pos hγ)).1
    ((distExp_two_xiGamma hγ hγ2).trans (gammaQ_two_eq_Q γ).symm)).symm

/-- **Characterization of `ξ_γ` by the distance exponent.** For `γ ∈ (0, 2)` and `ξ > 0`, the
kernel-independent LFPP distance exponent at `ξ` equals `Q_γ = 2/γ + γ/2` if and only if
`ξ = ξ_γ = γ / d_γ`. -/
theorem distExp_two_eq_Q_iff {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ξ : ℝ} (hξ : 0 < ξ) :
    HigherDimLQGMetric.distExp 2 ξ = LQGMetric.Q γ ↔ ξ = LQGMetric.xiGamma γ := by
  have hγ' : γ ∈ Ioo 0 (Real.sqrt (2 * ((2 : ℕ) : ℝ))) := by
    rw [sqrt_two_mul_two]; exact ⟨hγ, hγ2⟩
  rw [← gammaQ_two_eq_Q, HigherDimLQGContinuity.distExp_eq_gammaQ_iff le_rfl hγ' hξ,
    xiOfGamma_two_eq_xiGamma hγ hγ2]

end LatticeProb.LQG
