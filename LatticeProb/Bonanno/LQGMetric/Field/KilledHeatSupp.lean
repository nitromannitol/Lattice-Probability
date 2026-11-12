/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSupp at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatRefl2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`killedHeat_eq_zero_of_not_mem_left/right`: `p_A(t; z, w) = 0` if `z ∉ A` or `w ∉ A` (`t > 0`,
`A` open): the bridge starts at `z` (a planar bridge vanishes a.s. at time `0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma ae_coordProc_zero {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) (b : Bool) : ∀ᵐ ω ∂P, coordProc X (b, 0) ω = 0 := by
  have hG := hX.gauss.hasGaussianLaw_eval (b, 0)
  have hc : bridgeCov t (b, 0) (b, 0) = 0 := by simp [bridgeCov]
  have hlaw : HasLaw (coordProc X (b, 0)) (gaussianReal 0 0) P := by
    refine ⟨hX.gauss.aemeasurable _, ?_⟩
    rw [hG.map_eq_gaussianReal, hX.mean, ← covariance_self (hX.gauss.aemeasurable _),
      hX.cov _ _ zero_le zero_le, hc]
    simp
  rw [gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac

lemma ae_eq_zero_start {t : ℝ≥0} {X : ℝ≥0 → Ω → ℂ} {P : Measure Ω}
    (hX : IsPlanarBridge t X P) : ∀ᵐ ω ∂P, X 0 ω = 0 := by
  filter_upwards [ae_coordProc_zero hX false, ae_coordProc_zero hX true] with ω h0 h1
  apply Complex.ext
  · simpa [coordProc] using h0
  · simpa [coordProc] using h1

theorem bridgeStay_eq_zero_of_not_mem {A : Set ℂ} {t : ℝ≥0} (ht : t ≠ 0) {z : ℂ} (hz : z ∉ A)
    (w : ℂ) : bridgeStay A t z w = 0 := by
  have h0 : P2 (bridgeEvent A t z w (stdBridge t)) = 0 := by
    refine measure_mono_null (t := {ω | stdBridge t 0 ω ≠ 0}) (fun ω hω h ↦ hz ?_) ?_
    · have := hω 0 zero_le
      simpa [bridgePath, h] using this
    · exact ae_iff.mp (ae_eq_zero_start (isPlanarBridge_stdBridge ht))
  rw [bridgeStay, h0, ENNReal.toReal_zero]

/-- `p_A(t; z, w) = 0` for `z ∉ A`. -/
theorem killedHeat_eq_zero_of_not_mem_left {A : Set ℂ} {t : ℝ≥0} (ht : t ≠ 0) {z : ℂ}
    (hz : z ∉ A) (w : ℂ) : killedHeat A t z w = 0 := by
  rw [killedHeat, bridgeStay_eq_zero_of_not_mem ht hz w, mul_zero]

/-- `p_A(t; z, w) = 0` for `w ∉ A` (`A` open). -/
theorem killedHeat_eq_zero_of_not_mem_right {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0)
    (z : ℂ) {w : ℂ} (hw : w ∉ A) : killedHeat A t z w = 0 := by
  rw [killedHeat_symm hA, killedHeat_eq_zero_of_not_mem_left ht hw]

end KilledHeat
end LQGMetric
