import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeRadialPath

/-! # Cone and radial replacement pairings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic
open MatedCRTHarmonic.CellScaling

namespace LatticeProb.LQG

/-- A cone and a radial replacement with the same inner radial path differ
on the unit disk by the logarithmic singularity. -/
theorem coneFieldOf_apply_eq_replField_add_log
    (γ : ℝ) (X : DistC) (b b' : ℝ≥0 → ℝ) (w : C(ℝ, ℝ))
    (hA : LocallyIntegrable (fun z : ℂ =>
      coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hw : LocallyIntegrable (radialW w) volume)
    (hpath : ∀ t : ℝ, 0 ≤ t → w t = b t.toNNReal)
    (φ : TestC) (hφ : ∀ z : ℂ, 1 < ‖z‖ → φ z = 0) :
    coneFieldOf γ X b b' φ =
      replField (fun _ : Unit => X) (fun _ => w) () φ +
        ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  let g : ℂ → ℝ := fun z => coneRadial γ γ b b' (-Real.log ‖z‖) - radialW w z
  have hg : LocallyIntegrable g volume := hA.sub hw
  have hdec : coneFieldOf γ X b b' =
      replField (fun _ : Unit => X) (fun _ => w) () + MoTPort.ofFunC g := by
    show lateralPart X + CellScaling.ofFunC (fun z => coneRadial γ γ b b' (-Real.log ‖z‖)) =
      lateralPartC X + MoTPort.ofFunC (radialW w) + MoTPort.ofFunC g
    rw [add_assoc, MoTPort.ofFunC, MoTPort.ofFunC, ← Distribution.ofFun_add
      (by rw [TopologicalSpace.Opens.coe_top]; exact hw.locallyIntegrableOn Set.univ)
      (by simpa using hg.locallyIntegrableOn Set.univ)]
    congr 2
    funext z
    simp only [g, Pi.add_apply]
    ring
  rw [hdec, add_apply, ConeCirc.ofFunC_apply' hg]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : ‖z‖ ≤ 1
  · have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hz)
    simp only [g, radialW, coneRadial_of_nonneg γ γ b b' ht, hpath _ ht]
    ring
  · rw [hφ z (lt_of_not_ge hz), zero_mul, zero_mul]

end LatticeProb.LQG
