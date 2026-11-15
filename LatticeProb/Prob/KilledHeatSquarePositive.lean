import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqKer

/-! # Positive total mass of the killed heat kernel on a square -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open LQGMetric.HeatSq LQGMetric.KilledHeat

namespace LQGMetric.KilledHeatSq

/-- The first Dirichlet mode is positive at each interior point of a square. -/
theorem sqMode_one_one_pos {a L : ℝ} (hL : 0 < L) {z : ℂ}
    (hz : z ∈ sqOpen a L) : 0 < sqMode a L (1, 1) z := by
  have hr : 0 < z.re - a := by
    have := hz.1
    linarith
  have hi : 0 < z.im - a := by
    have := hz.2.2.1
    linarith
  have hrl : z.re - a < L := by
    have := hz.2.1
    linarith
  have hil : z.im - a < L := by
    have := hz.2.2.2
    linarith
  have hs (u : ℝ) (hu : 0 < u) (huL : u < L) : 0 < Real.sin (Real.pi * u / L) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hL]
      nlinarith [Real.pi_pos]
  simpa [sqMode, sinMode] using mul_pos (hs _ hr hrl) (hs _ hi hil)

/-- The killed heat kernel of a square has positive total mass at every interior start. -/
theorem lintegral_killedHeat_sqOpen_pos {a L : ℝ} (hL : 0 < L) {z : ℂ}
    (hz : z ∈ sqOpen a L) {t : ℝ≥0} (ht : t ≠ 0) :
    0 < ∫⁻ w, ENNReal.ofReal (killedHeat (sqOpen a L) t z w) := by
  have hmode := integral_killedHeat_sqMode hL (1, 1) hz ht
  have hpos : 0 < sqDecay L t (1, 1) * sqMode a L (1, 1) z :=
    mul_pos (sqDecay_pos _ _ _) (sqMode_one_one_pos hL hz)
  by_contra h
  have hzint : (∫⁻ w, ENNReal.ofReal (killedHeat (sqOpen a L) t z w)) = 0 :=
    le_antisymm (not_lt.mp h) zero_le
  have hae : ∀ᵐ w, ENNReal.ofReal (killedHeat (sqOpen a L) t z w) = 0 :=
    (lintegral_eq_zero_iff ((measurable_killedHeat_right (isOpen_sqOpen a L) ht z).ennreal_ofReal)).mp hzint
  have hzero : ∀ᵐ w, killedHeat (sqOpen a L) t z w * sqMode a L (1, 1) w = 0 := by
    filter_upwards [hae] with w hw
    have hk : killedHeat (sqOpen a L) t z w = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hw) (killedHeat_nonneg _ _ _ _)
    simp [hk]
  have : (∫ w, killedHeat (sqOpen a L) t z w * sqMode a L (1, 1) w) = 0 :=
    integral_eq_zero_of_ae hzero
  linarith

end LQGMetric.KilledHeatSq
