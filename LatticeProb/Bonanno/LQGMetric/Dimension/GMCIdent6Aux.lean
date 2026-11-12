/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Aux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Sq

/-!
# Auxiliary facts for the moment bounds of `M̃_{γ,δ}` (P2-GMCID6)

* `lintegral_affine` : `∫ H(a + L y) dy = L^{-2} ∫ H` (Lebesgue measure under `y ↦ a + L y`);
* `setLIntegral_le_square`, `square_le_setLIntegral` : comparison of `∫_U F` with
  `L² ∫_{[0,1)²} F(a + L y) dy` when `U ⊆ a + L[0,1)²`, resp. `a + L[0,1)² ⊆ U`;
* `ae_tendsto_fineInt` : a.s. `∫ f · fineDens_{n+m} dz → ∫ f dM̃_{γ,δ}` for `f ∈ C_c(𝕍)`
  (the vague convergence `ae_isVagueLimitOn_bandMeas'` and `integral_bandMeas_ae_eq`,
  as in the proof of `lintegral_tildeM_le`);
* `ae_ofReal_fineInt_eq` : a.s. `fineInt f = ∫ f · fineDens dz` is a finite Lebesgue integral
  (its mean is `∫ f dz`, `lintegral_fineDens`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open WhiteNoise DGMC GMCIdent GMCIdent4 GMCIdent5

/-- change of variables under `y ↦ a + L y` -/
lemma lintegral_affine (H : ℂ → ℝ≥0∞) (hH : Measurable H) (a : ℂ) {L : ℝ} (hL : 0 < L) :
    ∫⁻ y, H (a + (L : ℂ) * y) = ENNReal.ofReal ((L ^ 2)⁻¹) * ∫⁻ z, H z := by
  have hφ : (fun y : ℂ => a + (L : ℂ) * y) = (fun z => a + z) ∘ (fun t => L • t) := by
    funext t; simp [Complex.real_smul]
  have hmap : Measure.map (fun y : ℂ => a + (L : ℂ) * y) (volume : Measure ℂ) =
      ENNReal.ofReal |(L ^ Module.finrank ℝ ℂ)⁻¹| • volume := by
    rw [hφ, ← Measure.map_map (measurable_const_add a) (measurable_const_smul L),
      Measure.map_addHaar_smul volume hL.ne', Measure.map_smul,
      Measure.IsAddLeftInvariant.map_add_left_eq_self]
    exact (measurable_const_add a).aemeasurable
  have hm : Measurable fun y : ℂ => a + (L : ℂ) * y := by fun_prop
  rw [← lintegral_map hH hm, hmap, lintegral_smul_measure, smul_eq_mul,
    Complex.finrank_real_complex, abs_of_pos (by positivity)]

lemma ofReal_sq_mul_inv_sq {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal (L ^ 2) * ENNReal.ofReal ((L ^ 2)⁻¹) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]

lemma setLIntegral_le_square (F : ℂ → ℝ≥0∞) (hF : Measurable F) {U : Set ℂ}
    (hU : MeasurableSet U) (a : ℂ) {L : ℝ} (hL : 0 < L)
    (hUQ : ∀ y, a + (L : ℂ) * y ∈ U → y ∈ cell0) :
    ∫⁻ z in U, F z ≤ ENNReal.ofReal (L ^ 2) * ∫⁻ y in cell0, F (a + (L : ℂ) * y) := by
  rw [← lintegral_indicator hU, ← one_mul (∫⁻ z, U.indicator F z), ← ofReal_sq_mul_inv_sq hL,
    mul_assoc, ← lintegral_affine _ (hF.indicator hU) a hL, ← lintegral_indicator measurableSet_cell0]
  gcongr with y
  by_cases hy : a + (L : ℂ) * y ∈ U
  · rw [indicator_of_mem hy, indicator_of_mem (hUQ y hy)]
  · rw [indicator_of_notMem hy]; exact zero_le

lemma square_le_setLIntegral (F : ℂ → ℝ≥0∞) (hF : Measurable F) {U : Set ℂ}
    (hU : MeasurableSet U) (a : ℂ) {L : ℝ} (hL : 0 < L)
    (hQU : ∀ y ∈ cell0, a + (L : ℂ) * y ∈ U) :
    ENNReal.ofReal (L ^ 2) * ∫⁻ y in cell0, F (a + (L : ℂ) * y) ≤ ∫⁻ z in U, F z := by
  rw [← lintegral_indicator hU, ← one_mul (∫⁻ z, U.indicator F z), ← ofReal_sq_mul_inv_sq hL,
    mul_assoc, ← lintegral_affine _ (hF.indicator hU) a hL, ← lintegral_indicator measurableSet_cell0]
  gcongr with y
  by_cases hy : y ∈ cell0
  · rw [indicator_of_mem hy, indicator_of_mem (hQU y hy)]
  · rw [indicator_of_notMem hy]; exact zero_le

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- a.s. convergence of the band approximations of `∫ f dM̃` -/
lemma ae_tendsto_fineInt (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (m : ℕ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ openSquare) :
    ∀ᵐ ω ∂P', Tendsto (fun k => fineInt W γ m (k + m) f ω) atTop
      (𝓝 (∫ z, f z ∂(tildeM hW γ m ω))) := by
  filter_upwards [ae_isVagueLimitOn_bandMeas' hW hγ hγ2 m, ae_all_iff.2 fun k =>
    integral_bandMeas_ae_eq hW γ (Nat.le_add_left m k) f] with ω h hk
  have ht := (tendsto_add_atTop_iff_nat m).2 (h.2.2 _ hf hfc hfU)
  simp_rw [hk] at ht
  exact ht


end GMCIdent6
end LQGMetric
