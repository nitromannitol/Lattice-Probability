import Mathlib

/-! # Exponential scales for bounded sets -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- An attained positive radial maximum selects an exponential scale that the
set escapes, while controlling its diameter and the scale's location. -/
theorem exists_radial_exponential_scale {X : Type*} [MetricSpace X]
    (E : Set X) (z : X) {L R U : ℝ} (hL : 0 < L)
    (hLR : L ≤ R) (hRU : R ≤ U)
    (hball : E ⊆ closedBall z R) (hmax : ∃ x ∈ E, dist x z = R) :
    ∃ k : ℤ, Real.log L - 1 < (k : ℝ) ∧ (k : ℝ) ≤ Real.log U ∧
      ¬ E ⊆ ball z (Real.exp k) ∧
      diam E < 2 * Real.exp ((k : ℝ) + 1) := by
  have hR : 0 < R := hL.trans_le hLR
  let k : ℤ := ⌊Real.log R⌋
  have hklo : (k : ℝ) ≤ Real.log R := Int.floor_le _
  have hkhi : Real.log R < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hscale : Real.exp (k : ℝ) ≤ R := by
    calc
      Real.exp (k : ℝ) ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hklo
      _ = R := Real.exp_log hR
  have hscale' : R < Real.exp ((k : ℝ) + 1) := by
    calc
      R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ < Real.exp ((k : ℝ) + 1) := Real.exp_lt_exp.mpr hkhi
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · have h := Real.log_le_log hL hLR
    linarith
  · exact hklo.trans (Real.log_le_log hR hRU)
  · obtain ⟨x, hx, hxR⟩ := hmax
    intro hsub
    have hxball : dist x z < Real.exp (k : ℝ) := hsub hx
    linarith
  · have hd := diam_le_of_subset_closedBall hR.le hball
    linarith

end LatticeProb
