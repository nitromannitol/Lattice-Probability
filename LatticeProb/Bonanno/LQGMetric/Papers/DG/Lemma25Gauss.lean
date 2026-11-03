/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Lemma25Gauss at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Exponential moments of circle averages (input to DG Lemma 2.5)

Ding–Gwynne, arXiv:1807.01072, proof of Lemma 2.5 (DG:760–763): "By the calculations in
[DS11, Section 3.1], the circle average `h′_δ(u)` is … centered Gaussian with variance at most
`log δ⁻¹ + O_δ(1)` (with the `O_δ(1)` uniform over all `u ∈ U`), so
`E[e^{√(ξ̃² − ξ²) h′_δ(P(t))}]` … is bounded above by a deterministic constant times
`δ^{−(ξ̃² − ξ²)/2}`." (Sign of the exponent: `E[e^{s X}] = e^{s² Var/2} ≤ C δ^{−s²/2}`.)
The variance formula is LQGDimension's `Osc37.gffCircleCov_formula`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open LQGDimension.Osc37 in
/-- `Var h_δ(z) ≤ log δ⁻¹ + 2 log 4` for `δ ∈ (0,1]` and `|z| ≤ 3`. -/
lemma gffCircleCov_self_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 3) :
    LQGDimension.gffCircleCov δ z δ z ≤ -Real.log δ + 2 * Real.log 4 := by
  rw [gffCircleCov_formula hδ]
  have hb : betaAvg δ z ≤ Real.log 4 := by
    apply Real.circleAverage_mono_on_of_le_circle (circleIntegrable_logMaxOne _ _)
    intro y hy
    rw [mem_sphere_iff_norm, abs_of_pos hδ] at hy
    have : ‖y‖ ≤ 4 := by
      calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 4 := by rw [hy]; linarith
    exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le this (by norm_num))
  have ha := aAvg_nonneg δ z z
  linarith

/-- `E[e^{s h_δ(z)}] = e^{s² Var h_δ(z) / 2}` (as a lower Lebesgue integral). -/
lemma lintegral_exp_circleAvg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hc : ℝ → ℂ → Ω → ℝ} (hG : LQGDimension.IsGFFCircleAverage hc P) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * hc δ z ω)) ∂P =
      ENNReal.ofReal (Real.exp (LQGDimension.gffCircleCov δ z δ z * s ^ 2 / 2)) := by
  have := hG.isProbabilityMeasure
  have hX : HasGaussianLaw (hc δ z) P :=
    (LQGDimension.SegLaw.isGaussianProcess_slice hG hδ).hasGaussianLaw_eval z
  have hmap := hX.map_eq_gaussianReal
  have hmean : P[hc δ z] = 0 := hG.integral_eq_zero δ hδ z
  have hvar : Var[hc δ z; P] = LQGDimension.gffCircleCov δ z δ z := by
    rw [← covariance_self hX.aemeasurable, hG.covariance_eq δ hδ δ hδ z z]
  have hv0 : 0 ≤ Var[hc δ z; P] := variance_nonneg _ _
  rw [hmean, hvar] at hmap
  have hv : ((LQGDimension.gffCircleCov δ z δ z).toNNReal : ℝ) = LQGDimension.gffCircleCov δ z δ z :=
    Real.coe_toNNReal _ (hvar ▸ hv0)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * hc δ z ω)) ∂P
      = ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂(P.map (hc δ z)) :=
        (lintegral_map' (ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.measurable.comp (measurable_const_mul s))).aemeasurable
          hX.aemeasurable).symm
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (s * x))
          ∂(gaussianReal 0 (LQGDimension.gffCircleCov δ z δ z).toNNReal) := by rw [hmap]
    _ = ENNReal.ofReal (∫ x, Real.exp (s * x)
          ∂(gaussianReal 0 (LQGDimension.gffCircleCov δ z δ z).toNNReal)) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
          (ae_of_all _ fun x => (Real.exp_pos _).le)).symm
    _ = _ := by
        congr 1
        have := congrFun (mgf_fun_id_gaussianReal (μ := 0)
          (v := (LQGDimension.gffCircleCov δ z δ z).toNNReal)) s
        rw [mgf] at this
        rw [this, hv]
        ring_nf

end DG
end LQGMetric
