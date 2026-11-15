import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeCirc

/-! # Locality of radial replacement -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Radial replacements whose paths agree at nonnegative times have the same
pairings against tests supported in the closed unit disk. -/
theorem replField_apply_eq_of_agree_nonneg
    {Ω : Type*} (X : Ω → DistC) (W V : Ω → C(ℝ, ℝ)) (ω : Ω)
    (hW : LocallyIntegrable (radialW (W ω)) volume)
    (hV : LocallyIntegrable (radialW (V ω)) volume)
    (hpaths : ∀ t : ℝ, 0 ≤ t → W ω t = V ω t)
    (φ : TestC) (hφ : ∀ z : ℂ, 1 < ‖z‖ → φ z = 0) :
    replField X W ω φ = replField X V ω φ := by
  rw [replField_apply, replField_apply]
  congr 1
  rw [pairW, pairW, ConeCirc.ofFunC_apply' hW, ConeCirc.ofFunC_apply' hV]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : ‖z‖ ≤ 1
  · have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hz)
    rw [radialW, radialW, hpaths _ ht]
  · rw [hφ z (lt_of_not_ge hz), zero_mul, zero_mul]

end LatticeProb.LQG
