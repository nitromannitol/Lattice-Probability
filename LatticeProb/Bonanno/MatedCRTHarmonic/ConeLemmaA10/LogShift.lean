/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.LogShift at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3

/-!
# The deterministic logarithmic shift in DMS14 Lemma A.10

This file constructs the distribution associated with the exact whole-plane rooting shift

`w ↦ -γ log ‖w - z‖ + γ log (max ‖w‖ 1)`

and proves that its classical average on the unit circle is zero when `z` lies in the open unit
disk. The logarithmic mean-value formula and local integrability of `log ‖·‖` are reused from
`QuantumZipper`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped Distributions

namespace MatedCRTHarmonic.ConeLemmaA10

/-- The exact deterministic field shift in the whole-plane clause of DMS14 Lemma A.10. -/
def logRootingShiftFun (γ : ℝ) (z w : ℂ) : ℝ :=
  -γ * Real.log ‖w - z‖ + γ * Real.log (max ‖w‖ (1 : ℝ))

lemma locallyIntegrable_log_norm_sub (z : ℂ) :
    LocallyIntegrable (fun w : ℂ => Real.log ‖w - z‖) volume := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addLeft (-z)
  have he : Measure.map e volume = volume :=
    (measurePreserving_add_left volume (-z)).map_eq
  have h := (locallyIntegrable_map_homeomorph e
    (f := fun w : ℂ => Real.log ‖w‖) (μ := volume)).mp (by
      rw [he]
      exact QuantumZipper.K3.locallyIntegrable_log_norm)
  simpa [e, Function.comp_def, sub_eq_add_neg, add_comm] using h

lemma continuous_log_max_norm_one :
    Continuous (fun w : ℂ => Real.log (max ‖w‖ (1 : ℝ))) := by
  exact (continuous_norm.max continuous_const).log fun w =>
    (lt_of_lt_of_le one_pos (le_max_right ‖w‖ (1 : ℝ))).ne'

lemma locallyIntegrable_logRootingShiftFun (γ : ℝ) (z : ℂ) :
    LocallyIntegrable (logRootingShiftFun γ z) volume := by
  have h₁ : LocallyIntegrable (fun w : ℂ => -γ * Real.log ‖w - z‖) volume := by
    exact ((locallyIntegrable_log_norm_sub z).smul (-γ)).congr
      (ae_of_all _ fun w => by simp)
  have h₂ : LocallyIntegrable
      (fun w : ℂ => γ * Real.log (max ‖w‖ (1 : ℝ))) volume := by
    exact (continuous_log_max_norm_one.locallyIntegrable.smul γ).congr
      (ae_of_all _ fun w => by simp)
  exact (h₁.add h₂).congr (ae_of_all _ fun _ => rfl)

/-- The rooting shift as a distribution on the plane. -/
def logRootingShift (γ : ℝ) (z : ℂ) : LQGMetric.DistC :=
  Distribution.ofFun ⊤ (logRootingShiftFun γ z) volume ⊤

/-- The distributional shift acts on a test function by integration against the exact
logarithmic function used in DMS14 Lemma A.10. -/
theorem logRootingShift_apply (γ : ℝ) (z : ℂ) (φ : LQGMetric.TestC) :
    logRootingShift γ z φ = ∫ w, φ w * logRootingShiftFun γ z w ∂volume := by
  rw [logRootingShift, Distribution.ofFun_apply]
  · simp only [smul_eq_mul]
  · simpa [locallyIntegrableOn_univ] using locallyIntegrable_logRootingShiftFun γ z

lemma integrable_log_max_norm_one_circle :
    Integrable (fun w : ℂ => Real.log (max ‖w‖ (1 : ℝ)))
      (QuantumZipper.circleUnif 0 1) := by
  refine (QuantumZipper.CircleMV.integrable_log_norm_sub_circleUnif 0 0 1).congr ?_
  filter_upwards [QuantumZipper.CircleMV.ae_circleUnif 0 1] with w hw
  simp only [sub_zero, abs_one] at hw
  simp [hw]

lemma integral_log_max_norm_one_circle :
    ∫ w : ℂ, Real.log (max ‖w‖ (1 : ℝ)) ∂(QuantumZipper.circleUnif 0 1) = 0 := by
  calc
    ∫ w : ℂ, Real.log (max ‖w‖ (1 : ℝ)) ∂(QuantumZipper.circleUnif 0 1) =
        ∫ w : ℂ, Real.log ‖w - 0‖ ∂(QuantumZipper.circleUnif 0 1) := by
          refine integral_congr_ae ?_
          filter_upwards [QuantumZipper.CircleMV.ae_circleUnif 0 1] with w hw
          simp only [sub_zero, abs_one] at hw
          simp [hw]
    _ = Real.log (max (1 : ℝ) ‖(0 : ℂ) - 0‖) :=
      QuantumZipper.integral_log_norm_sub_circleUnif 0 0 one_pos
    _ = 0 := by simp

/-- For a root in the open unit disk, the exact DMS14 logarithmic shift already has zero average
on the unit circle. Thus the final resetting of its own additive constant does nothing. -/
theorem integral_logRootingShiftFun_circle_eq_zero {γ : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ∫ w, logRootingShiftFun γ z w ∂(QuantumZipper.circleUnif 0 1) = 0 := by
  have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hlog := QuantumZipper.CircleMV.integrable_log_norm_sub_circleUnif 0 z 1
  change (∫ w, (-γ * Real.log ‖w - z‖ +
    γ * Real.log (max ‖w‖ (1 : ℝ))) ∂(QuantumZipper.circleUnif 0 1)) = 0
  rw [integral_add (hlog.const_mul (-γ))
    (integrable_log_max_norm_one_circle.const_mul γ), integral_const_mul,
    integral_const_mul, QuantumZipper.integral_log_norm_sub_circleUnif 0 z one_pos,
    integral_log_max_norm_one_circle]
  have hmax : max (1 : ℝ) ‖(0 : ℂ) - z‖ = 1 := by
    rw [zero_sub, norm_neg, max_eq_left hz'.le]
  rw [hmax]
  simp

end MatedCRTHarmonic.ConeLemmaA10

