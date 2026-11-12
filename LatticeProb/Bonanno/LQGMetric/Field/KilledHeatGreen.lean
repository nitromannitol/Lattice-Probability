/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatGreen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatMeas
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KILLED, D-KHK1)

DZZ (`LBM_LGDarXiv.tex` l. 400–403, eq. (eq:Green_fxn)) and Berestycki–Powell (arXiv:2404.16642
§1.2) write the Dirichlet Green function as `G_A(z, w) = π ∫₀^∞ p_A(s; z, w) ds` (our
normalization: `G_A(z,w) = −log|z − w| + O(1)`). Here: the definition `killedGreen`, the
integrability of `s ↦ p_A(s; z, w)` on `(0, ∞)` for bounded `A` and `z ≠ w`
(`integrableOn_killedHeat`; `p_A ≤ p_s ≤ (π|z−w|²)⁻¹` near `0`, `p_A ≤ R²/(π s²)` at `∞`), and
symmetry. The identification with `QuantumZipper.zeroGFFTestCov` (decision D39) remains open
(handoff/P2-KILLED.md item 1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

/-- The killed Green function `G_A(z, w) = π ∫₀^∞ p_A(s; z, w) ds`. -/
def killedGreen (A : Set ℂ) (z w : ℂ) : ℝ :=
  Real.pi * ∫ s in Set.Ioi (0 : ℝ), killedHeat A s.toNNReal z w

lemma heatKernel_le_inv_sq (s : ℝ) (hs : 0 < s) {z w : ℂ} (hzw : z ≠ w) :
    heatKernel s z w ≤ (Real.pi * ‖z - w‖ ^ 2)⁻¹ := by
  have hr : 0 < ‖z - w‖ ^ 2 := by
    have : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    positivity
  unfold heatKernel
  have hx : 0 < ‖z - w‖ ^ 2 / (2 * s) := by positivity
  have hexp : Real.exp (-(‖z - w‖ ^ 2 / (2 * s))) ≤ (‖z - w‖ ^ 2 / (2 * s))⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hx (by linarith [Real.add_one_le_exp (‖z - w‖ ^ 2 / (2 * s))])
  rw [neg_div]
  have hπ : 0 < Real.pi := Real.pi_pos
  calc (2 * Real.pi * s)⁻¹ * Real.exp (-(‖z - w‖ ^ 2 / (2 * s)))
      ≤ (2 * Real.pi * s)⁻¹ * (‖z - w‖ ^ 2 / (2 * s))⁻¹ :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.pi * ‖z - w‖ ^ 2)⁻¹ := by
        rw [inv_div]
        field_simp

/-- `s ↦ p_A(s; z, w)` is integrable on `(0, ∞)` for bounded open `A` and `z ≠ w`. -/
theorem integrableOn_killedHeat {A : Set ℂ} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball c R) {z w : ℂ} (hzw : z ≠ w) :
    IntegrableOn (fun s : ℝ ↦ killedHeat A s.toNNReal z w) (Set.Ioi 0) := by
  have hf : Measurable fun s : ℝ ↦ ((s.toNNReal, z, w) : ℝ≥0 × ℂ × ℂ) :=
    measurable_real_toNNReal.prodMk measurable_const
  have hmeas : Measurable fun s : ℝ ↦ killedHeat A s.toNNReal z w :=
    Measurable.comp (g := fun x : ℝ≥0 × ℂ × ℂ ↦ killedHeat A x.1 x.2.1 x.2.2)
      (measurable_killedHeat hA) hf
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_const (C := (Real.pi * ‖z - w‖ ^ 2)⁻¹)
      (by simp)).mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
    refine (killedHeat_le_heatKernel _ _ _ _).trans ?_
    rw [Real.coe_toNNReal _ hs.1.le]
    exact heatKernel_le_inv_sq s hs.1 hzw
  · refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
      (R ^ 2 / Real.pi)).mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (killedHeat_nonneg _ _ _ _)]
    exact killedHeat_le_rpow hR hAR (zero_lt_one.trans hs) z w

lemma killedGreen_nonneg (A : Set ℂ) (z w : ℂ) : 0 ≤ killedGreen A z w :=
  mul_nonneg Real.pi_pos.le (setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ killedHeat_nonneg _ _ _ _)

end KilledHeat
end LQGMetric
