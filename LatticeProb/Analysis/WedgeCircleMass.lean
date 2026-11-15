import LatticeProb.Analysis.WedgeArcIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Total mass of angular and surface measures on the unit circle -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Angular measure of a full turn has total mass `2π`. -/
theorem wedgeArcMeasure_full_univ :
    wedgeArcMeasure (2 * Real.pi) univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [wedgeArcMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc]
  congr 1
  ring

/-- Surface measure of the complex unit circle has total mass `2π`. -/
theorem complex_toSphere_univ :
    (volume : Measure ℂ).toSphere univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, Complex.finrank_real_complex, Complex.volume_ball]
  simp only [Nat.cast_ofNat, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

end LatticeProb
