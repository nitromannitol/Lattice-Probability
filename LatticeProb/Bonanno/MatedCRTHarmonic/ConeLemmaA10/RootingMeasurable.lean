/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LimitPassage
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Measurability of the DMS14 A.10 rooting map

The cylinder measurable space on `DistC` reduces measurability to test pairings. The exact
pairing of the logarithmic rooting shift is a translate of the smooth logarithmic potential of
the test function, so it is continuous in the root. This gives joint measurability of adding the
shift to a distribution and of the subsequent unit-circle normalization used in DMS14 A.10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Topology

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.MarkovGermVer

/-- Exact cylinder pairing formula for the DMS14 logarithmic rooting shift. -/
theorem logRootingShift_pairing (γ : ℝ) (z : ℂ) (φ : TestC) :
    logRootingShift γ z φ = γ *
      (logPot φ z - Real.circleAverage (logPot φ) 0 1) := by
  have hA : Integrable fun w : ℂ => φ w * (-Real.log ‖w - z‖) :=
    (CircleAvg.integrable_log_mul_test φ z).congr (ae_of_all _ fun w => by
      change -Real.log ‖z - w‖ * φ w = φ w * -Real.log ‖w - z‖
      rw [norm_sub_rev]
      ring)
  have hB : Integrable fun w : ℂ => φ w * (-Real.log (max ‖w‖ (1 : ℝ))) :=
    ((CircleAvg.integrable_test_mul φ
      ⟨fun w => Real.log (max ‖w‖ (1 : ℝ)), continuous_log_max_norm_one⟩).neg).congr
        (ae_of_all _ fun w => by simp)
  have hpot : logPot φ z = ∫ w, φ w * (-Real.log ‖w - z‖) := by
    unfold logPot
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      change -Real.log ‖z - w‖ * φ w = φ w * -Real.log ‖w - z‖
      rw [norm_sub_rev]
      ring
  rw [logRootingShift_apply, circleAverage_logPot_zero_one, hpot]
  have heq : (fun w : ℂ => φ w * logRootingShiftFun γ z w) =
      fun w => γ * (φ w * (-Real.log ‖w - z‖) -
        φ w * (-Real.log (max ‖w‖ (1 : ℝ)))) := by
    funext w
    simp only [logRootingShiftFun]
    ring
  rw [heq, integral_const_mul, integral_sub hA hB]

/-- The deterministic rooting shift is measurable in its root for the cylinder measurable space
on distributions. -/
theorem measurable_logRootingShift (γ : ℝ) :
    Measurable (logRootingShift γ) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  simp_rw [logRootingShift_pairing]
  exact measurable_const.mul
    ((contDiff_logPot φ).continuous.measurable.sub measurable_const)

/-- Joint measurability of the field and root map used before the final normalization in DMS14
Lemma A.10. -/
theorem measurable_add_logRootingShift (γ : ℝ) :
    Measurable fun p : DistC × ℂ => p.1 + logRootingShift γ p.2 := by
  refine measurable_distOn_iff.2 fun φ => ?_
  change Measurable fun p : DistC × ℂ => p.1 φ + logRootingShift γ p.2 φ
  exact ((measurable_distOn_apply φ).comp measurable_fst).add
    ((measurable_distOn_apply φ).comp
      ((measurable_logRootingShift γ).comp measurable_snd))

/-- Joint measurability of the exact normalized field-rooting map from DMS14 Lemma A.10. -/
theorem measurable_normalizedRootingMap (γ : ℝ) :
    Measurable fun p : DistC × ℂ =>
      addConst (p.1 + logRootingShift γ p.2)
        (-circleAvg (p.1 + logRootingShift γ p.2) 1 0) := by
  let F : DistC × ℂ → DistC := fun p => p.1 + logRootingShift γ p.2
  have hF : Measurable F := measurable_add_logRootingShift γ
  have hc : Measurable fun p => -circleAvg (F p) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hF).neg
  refine measurable_distOn_iff.2 fun φ => ?_
  simp only [GFFInv.addConst_apply]
  exact ((measurable_distOn_apply φ).comp hF).add (hc.const_mul _)

end MatedCRTHarmonic.ConeLemmaA10

