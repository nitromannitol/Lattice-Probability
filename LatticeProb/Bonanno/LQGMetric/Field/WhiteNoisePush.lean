/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoisePush at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise

/-!
# Conformal pushforward of space-time white noise: the change of variables (task P2-DDDFL6)

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 541–543), following
Dubédat–Falconet (arXiv:1809.02607, `LiouvilleMetricStarScale.tex` l. 385–395), couple two white
noises through the space-time map `(y, t) ↦ (F(y), t |F'(y)|²)` of `U × (0,∞)` onto
`V × (0,∞)` (`F : U → V` conformal): `W̃(dF(y), d(t|F'(y)|²)) = |F'(y)|² W(dy, dt)`, "both
sides have variance `‖ω‖²`". The variance identity is the change of variables

  `∫_U ∫_0^∞ ω(F(y), t|F'(y)|²)² |F'(y)|⁴ dt dy = ∫_V ∫_0^∞ ω(y', t')² dt' dy'`,

i.e. the Jacobian of the map is `|F'|² (time) · |F'|² (space) = |F'|⁴`. We prove it in the
`ℝ≥0∞`-valued form for every measurable `g` (`lintegral_pushMap`): Tonelli, the time scaling
`t ↦ t c` (mathlib `Real.map_volume_mul_right`) and the conformal change of variables in space
(QuantumZipper `lintegral_comp_holo`, Jacobian `‖F'‖²`). Time comes first (convention WN-1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace WNPush

/-- The space-time map `(t, y) ↦ (t |F'(y)|², F(y))` (DDDF l. 541: `y' = F(y)`,
`t' = t |F'(y)|²`), time first. -/
def pushMap (F : ℂ → ℂ) (p : ℝ × ℂ) : ℝ × ℂ := (p.1 * ‖deriv F p.2‖ ^ 2, F p.2)

/-- Time scaling on `(0, ∞)`: `∫_0^∞ h(tc) dt = c⁻¹ ∫_0^∞ h(s) ds`. -/
lemma lintegral_Ioi_comp_mul {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ t in Ioi 0, h (t * c) = ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioi 0, h s := by
  have e : (Ioi (0 : ℝ)).indicator (fun t => h (t * c)) =
      fun t => (Ioi (0 : ℝ)).indicator h (t * c) := by
    funext t
    by_cases ht : 0 < t
    · simp [indicator_of_mem, ht, mul_pos ht hc]
    · have : ¬ 0 < t * c := by
        intro h'
        exact ht (by nlinarith)
      simp [indicator_of_notMem, ht, this]
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi, e,
    ← lintegral_map (hh.indicator measurableSet_Ioi) (measurable_mul_const c),
    Real.map_volume_mul_right hc.ne', lintegral_smul_measure, abs_of_pos (inv_pos.2 hc)]
  rfl

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- **Change of variables for the conformal space-time map** (DDDF l. 541–543: "both sides have
variance `‖ω‖²`"): for measurable `g ≥ 0`,
`∫_{(0,∞)×U} |F'(y)|⁴ g(t|F'(y)|², F(y)) dt dy = ∫_{(0,∞)×F(U)} g`. -/
theorem lintegral_pushMap (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (hd : ∀ y ∈ U, deriv F y ≠ 0) {g : ℝ × ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in Ioi 0 ×ˢ U, ENNReal.ofReal (‖deriv F p.2‖ ^ 4) * g (pushMap F p) =
      ∫⁻ q in Ioi 0 ×ˢ (F '' U), g q := by
  have hFm : AEMeasurable F (volume.restrict U) := hF.continuousOn.aemeasurable hU.measurableSet
  have hdm : Measurable (deriv F) := measurable_deriv F
  have hn : Measurable fun p : ℝ × ℂ => ‖deriv F p.2‖ := (hdm.comp measurable_snd).norm
  have hF2 : AEMeasurable (fun p : ℝ × ℂ => F p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict U)) :=
    hFm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    lintegral_prod_symm _ ?m1, lintegral_prod_symm _ hg.aemeasurable]
  case m1 =>
    exact (hn.pow_const 4).ennreal_ofReal.aemeasurable.mul
      (hg.comp_aemeasurable ((measurable_fst.mul (hn.pow_const 2)).aemeasurable.prodMk hF2))
  have key : ∀ y ∈ U, ∫⁻ t in Ioi 0, ENNReal.ofReal (‖deriv F y‖ ^ 4) * g (pushMap F (t, y))
      = ENNReal.ofReal (‖deriv F y‖ ^ 2) * ∫⁻ s in Ioi 0, g (s, F y) := by
    intro y hy
    have hc : 0 < ‖deriv F y‖ ^ 2 := pow_pos (norm_pos_iff.2 (hd y hy)) 2
    have hgy : Measurable fun s : ℝ => g (s, F y) := hg.comp (measurable_id.prodMk measurable_const)
    simp only [pushMap]
    rw [lintegral_const_mul (f := fun t => g (t * ‖deriv F y‖ ^ 2, F y)) _
        (hgy.comp (measurable_mul_const _)),
      lintegral_Ioi_comp_mul hc hgy, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  refine (setLIntegral_congr_fun hU.measurableSet key).trans ?_
  exact (QuantumZipper.lintegral_comp_holo hU hF hinj hd hU.measurableSet subset_rfl
    (fun w => ∫⁻ s in Ioi 0, g (s, w))).symm

end WNPush
end LQGMetric
