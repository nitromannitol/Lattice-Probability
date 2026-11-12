/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatBound at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatCK
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 10: consequences used by DZZ (task P2-KILLED, D-KHK1)

* `integral_killedHeat_mul_killedHeat`: `∫ p_A(t; u, w) p_A(t; v, w) dw = p_A(2t; u, v)`
  (Chapman–Kolmogorov + symmetry), the identity behind DZZ (eq-cov-tildeh),
  `LBM_LGDarXiv.tex` l. 437–441.
* `bridgeStay_le_of_subset_ball`, `killedHeat_le_of_subset_ball`: for `A ⊆ B(c, R)`,
  `q_A(2a; z, w) ≤ R²/a` and `p_A(2a; z, w) ≤ R²/(4π a²)`: the bridge must be in `B(c, R)` at its
  midpoint, whose law has density `≤ (2π a/2)⁻¹`. Own elementary argument (the polynomial decay
  makes `∫^∞ p_A(s; z, w) ds` finite for bounded `A`, as DZZ use for `δ' = ∞`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

/-- `∫ p_A(t; u, w) p_A(t; v, w) dw = p_A(2t; u, v)` (DZZ eq-cov-tildeh). -/
theorem integral_killedHeat_mul_killedHeat {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0)
    (u v : ℂ) :
    ∫ w, killedHeat A t u w * killedHeat A t v w = killedHeat A (t + t) u v := by
  rw [killedHeat_chapmanKolmogorov hA ht ht]
  congr 1
  funext w
  rw [killedHeat_symm hA t v w]

lemma heatKernel_le_inv (v : ℝ) (hv : 0 ≤ v) (z w : ℂ) :
    heatKernel v z w ≤ (2 * Real.pi * v)⁻¹ := by
  unfold heatKernel
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

/-- For `A ⊆ B(c, R)`: `q_A(2a; z, w) ≤ R²/a`. -/
theorem bridgeStay_le_of_subset_ball {A : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {a : ℝ≥0} (ha : a ≠ 0) (z w : ℂ) :
    bridgeStay A (a + a) z w ≤ R ^ 2 / a := by
  have haa : a + a ≠ 0 := by positivity
  have hβ := isPlanarBridge_stdBridge haa
  have hXm : AEMeasurable (fun ω ↦ stdBridge (a + a) a ω) P2 := by
    have e : (fun ω ↦ stdBridge (a + a) a ω) =
        toC ∘ (fun ω b ↦ coordProc (stdBridge (a + a)) (b, a) ω) :=
      funext fun ω ↦ (toC_coordProc (stdBridge (a + a)) a ω).symm
    rw [e]
    exact measurable_toC.comp_aemeasurable (.of_eval fun b ↦ hβ.gauss.aemeasurable _)
  set S : Set ℂ := (fun y ↦ midPt a a z w + y) ⁻¹' Metric.ball c R with hS
  have hSm : MeasurableSet S := measurableSet_ball.preimage (measurable_const_add _)
  have hsub : bridgeEvent A (a + a) z w (stdBridge (a + a)) ⊆
      (fun ω ↦ stdBridge (a + a) a ω) ⁻¹' S := fun ω hω ↦ hAR (hω a le_self_add)
  have hv : ((a * a / (a + a) : ℝ≥0) : ℝ) = a / 2 := by
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    push_cast
    field_simp
    ring
  have hbound : P2 ((fun ω ↦ stdBridge (a + a) a ω) ⁻¹' S) ≤
      ENNReal.ofReal ((2 * Real.pi * (a / 2))⁻¹) * volume (Metric.ball c R) := by
    rw [← Measure.map_apply_of_aemeasurable hXm hSm, map_mid_eq hβ ha ha,
      withDensity_apply _ hSm]
    calc ∫⁻ y in S, ENNReal.ofReal (heatKernel ((a * a / (a + a) : ℝ≥0) : ℝ) 0 y)
        ≤ ∫⁻ _ in S, ENNReal.ofReal ((2 * Real.pi * (a / 2))⁻¹) := by
          refine setLIntegral_mono measurable_const fun y _ ↦ ENNReal.ofReal_le_ofReal ?_
          rw [← hv]
          exact heatKernel_le_inv _ (NNReal.coe_nonneg _) 0 y
      _ = ENNReal.ofReal ((2 * Real.pi * (a / 2))⁻¹) * volume S := setLIntegral_const _ _
      _ = ENNReal.ofReal ((2 * Real.pi * (a / 2))⁻¹) * volume (Metric.ball c R) := by
          rw [hS, measure_preimage_add]
  unfold bridgeStay
  have ha0 : (0 : ℝ) < a := lt_of_le_of_ne (NNReal.coe_nonneg a) (Ne.symm (by exact_mod_cast ha))
  calc (P2 (bridgeEvent A (a + a) z w (stdBridge (a + a)))).toReal
      ≤ (ENNReal.ofReal ((2 * Real.pi * (a / 2))⁻¹) * volume (Metric.ball c R)).toReal :=
        ENNReal.toReal_mono (by rw [Complex.volume_ball]; finiteness)
          ((measure_mono hsub).trans hbound)
    _ = R ^ 2 / a := by
        rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hR,
          ENNReal.coe_toReal, NNReal.coe_real_pi]
        field_simp

/-- For `A ⊆ B(c, R)`: `p_A(2a; z, w) ≤ R² / (4π a²)`. -/
theorem killedHeat_le_of_subset_ball {A : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {a : ℝ≥0} (ha : a ≠ 0) (z w : ℂ) :
    killedHeat A (a + a) z w ≤ R ^ 2 / (4 * Real.pi * (a : ℝ) ^ 2) := by
  have ha0 : (0 : ℝ) < a := lt_of_le_of_ne (NNReal.coe_nonneg a) (Ne.symm (by exact_mod_cast ha))
  unfold killedHeat
  calc heatKernel ((a + a : ℝ≥0) : ℝ) z w * bridgeStay A (a + a) z w
      ≤ (2 * Real.pi * ((a + a : ℝ≥0) : ℝ))⁻¹ * (R ^ 2 / a) :=
        mul_le_mul (heatKernel_le_inv _ (NNReal.coe_nonneg _) z w)
          (bridgeStay_le_of_subset_ball hR hAR ha z w) (bridgeStay_nonneg _ _ _ _)
          (by positivity)
    _ = R ^ 2 / (4 * Real.pi * (a : ℝ) ^ 2) := by
        push_cast
        field_simp
        ring

/-- For `A ⊆ B(c, R)` and `s > 0`: `p_A(s; z, w) ≤ (R²/π) s⁻²`. -/
theorem killedHeat_le_rpow {A : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    killedHeat A s.toNNReal z w ≤ R ^ 2 / Real.pi * s ^ (-2 : ℝ) := by
  set a : ℝ≥0 := s.toNNReal / 2 with ha
  have haa : a + a = s.toNNReal := add_halves _
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact div_ne_zero (by simpa using hs) two_ne_zero
  have hacoe : (a : ℝ) = s / 2 := by
    rw [ha, NNReal.coe_div, Real.coe_toNNReal _ hs.le]
    norm_num
  have h := killedHeat_le_of_subset_ball hR hAR ha0 z w
  rw [haa, hacoe] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.rpow_neg hs.le, Real.rpow_two]
  field_simp
  ring

/-- **Time-integrability at `∞`** (the white-noise kernels of DZZ with `δ' = ∞`): for bounded
`A` and `c₀ > 0`, `∫_{c₀}^∞ p_A(s; z, w) ds < ∞` (here as a lower Lebesgue integral). -/
theorem lintegral_killedHeat_Ioi_lt_top {A : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) (z w : ℂ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∫⁻ s in Set.Ioi c₀, ENNReal.ofReal (killedHeat A s.toNNReal z w) < ∞ := by
  have hint : IntegrableOn (fun s : ℝ ↦ R ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Set.Ioi c₀) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc₀).const_mul _
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun s hs ↦
    ENNReal.ofReal_le_ofReal (killedHeat_le_rpow hR hAR (hc₀.trans hs) z w)) ?_
  exact hint.lintegral_lt_top

end KilledHeat
end LQGMetric
