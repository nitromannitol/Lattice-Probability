/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentLim at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: the measurability argument of tendsto_integral_of_L1' (dropped from its signature) removed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentCirc
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentExp

/-!
# The limit `r → 0` of the circle step at a fixed point (P2-GMCID, D67)

`tendsto_coarse_circle`: with `K₂^{(k)} = K^{(δ²,∞)}_{∂B(z, 2^{-k})}` and `κ_z = K^{(δ²,∞)}_z`
(so that `√π W(κ_z) = h̃_δ(z)`), for every measurable `B` and constant `h`,

  `e^{γ²/2 (h − π‖K₂^{(k)}‖²)} ∫_B e^{γ√π W(K₂^{(k)})} → e^{γ²/2 (h − π‖κ_z‖²)} ∫_B e^{γ√π W(κ_z)}`.

This is "when `n` is finite and `ε → 0` … the right hand side converges … by continuity of `h^n`"
(Berestycki arXiv:1506.09113, §4, l. 686–687), from `norm_measKerL2_sub_tildeKer_le` (DZZ Lemma
2.5 averaged over the circle) and the `L¹` continuity `tendsto_eLpNorm_exp_wn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma tendsto_coarseKer_circle (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : ∀ᶠ k in atTop, foldedCircle z (radius k) (closedBall z (radius k))ᶜ = 0) :
    Tendsto (fun k => measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))) atTop
      (𝓝 (wndKernelL2 openSquare (Ioi (δ ^ 2)) z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k => Real.sqrt (28 * radius k / (Real.pi * δ))) atTop (𝓝 0) := by
    rw [← Real.sqrt_zero]
    refine (Real.continuous_sqrt.tendsto _).comp ?_
    have hr : Tendsto (fun k => radius k) atTop (𝓝 0) := by
      unfold radius
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using ((hr.const_mul 28).div_const (Real.pi * δ))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [hz] with k hk
  exact (norm_measKerL2_sub_tildeKer_le hW hδ _ hk).2

theorem tendsto_coarse_circle (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : ∀ᶠ k in atTop, foldedCircle z (radius k) (closedBall z (radius k))ᶜ = 0)
    (γ h : ℝ) (B : Set Ω) :
    Tendsto (fun k => Real.exp (γ ^ 2 / 2 * (h - Real.pi *
        ‖measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))‖ ^ 2)) *
        ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
          W (measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))) ω)) ∂P) atTop
      (𝓝 (Real.exp (γ ^ 2 / 2 * (h - Real.pi * ‖wndKernelL2 openSquare (Ioi (δ ^ 2)) z‖ ^ 2)) *
        ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
          W (wndKernelL2 openSquare (Ioi (δ ^ 2)) z) ω)) ∂P)) := by
  have hK := tendsto_coarseKer_circle hW hδ hz
  refine Tendsto.mul ?_ ?_
  · refine (Real.continuous_exp.tendsto _).comp ?_
    exact ((((continuous_norm.tendsto _).comp hK).pow 2).const_mul Real.pi |>.const_sub h).const_mul _
  · set a := γ * Real.sqrt Real.pi
    have e : ∀ g : WNSpace, (fun ω => Real.exp (γ * (Real.sqrt Real.pi * W g ω))) =
        fun ω => Real.exp (a * W g ω) := fun g => by funext ω; rw [← mul_assoc]
    simp_rw [e]
    have hL := tendsto_eLpNorm_exp_wn hW a hK
    refine tendsto_integral_of_L1' _
      (Eventually.of_forall fun k => (integrable_exp_wn hW a _).restrict) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun _ => zero_le)
      fun k => eLpNorm_mono_measure _ Measure.restrict_le_self

end GMCIdent
end LQGMetric
