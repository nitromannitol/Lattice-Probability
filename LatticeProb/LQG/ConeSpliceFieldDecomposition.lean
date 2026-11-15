import LatticeProb.LQG.ConeReplacementPairing

/-! # Cone and radial replacement field decomposition -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling

namespace LatticeProb.LQG

/-- A cone field is the radial replacement of its base field plus the
locally integrable difference of their radial profiles. -/
theorem coneFieldOf_eq_replField_add_radial_difference
    (γ : ℝ) (X : DistC) (b b' : ℝ≥0 → ℝ) (w : C(ℝ, ℝ))
    (hA : LocallyIntegrable (fun z : ℂ =>
      coneRadial γ γ b b' (-Real.log ‖z‖)) volume)
    (hw : LocallyIntegrable (radialW w) volume) :
    coneFieldOf γ X b b' =
      replField (fun _ : Unit => X) (fun _ => w) () +
        MoTPort.ofFunC (fun z : ℂ =>
          coneRadial γ γ b b' (-Real.log ‖z‖) - radialW w z) := by
  let g : ℂ → ℝ := fun z => coneRadial γ γ b b' (-Real.log ‖z‖) - radialW w z
  have hg : LocallyIntegrable g volume := hA.sub hw
  show lateralPart X + CellScaling.ofFunC (fun z => coneRadial γ γ b b' (-Real.log ‖z‖)) =
    lateralPartC X + MoTPort.ofFunC (radialW w) + MoTPort.ofFunC g
  rw [add_assoc, MoTPort.ofFunC, MoTPort.ofFunC, ← Distribution.ofFun_add
    (by rw [TopologicalSpace.Opens.coe_top]; exact hw.locallyIntegrableOn Set.univ)
    (by simpa using hg.locallyIntegrableOn Set.univ)]
  congr 2
  funext z
  simp only [g, Pi.add_apply]
  ring

end LatticeProb.LQG
