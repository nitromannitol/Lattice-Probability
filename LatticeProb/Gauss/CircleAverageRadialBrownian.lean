import LatticeProb.Gauss.CircleAverageCovariance
import LatticeProb.Gauss.CircleAverageIncrement
import LatticeProb.Prob.BrownianSupTail

/-!
# Circle averages of the whole-plane GFF as a Brownian motion in the logarithmic radius

For a whole-plane Gaussian free field `h`, a centre `z` and a radius `ρ > 0`, the process
`t ↦ h_{ρ e^{-t}}(z) - h_ρ(z)`, `t ≥ 0`, is a standard Brownian motion with almost surely
continuous paths.  Combined with the sharp tail of the running maximum of Brownian motion this gives

    `P {∃ r ∈ [ρ e^{-T}, ρ], a ≤ |h_r(z) - h_ρ(z)|} ≤ 2 exp (-a² / (2 T))`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Gauss

/-- The circle average process of centre `z` in the logarithmic radius, started from the circle of
radius `ρ`: `t ↦ h_{ρ e^{-t}}(z) - h_ρ(z)`. -/
def radialCircleProcess {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (ρ : ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  hcirc ω (ρ * Real.exp (-(t : ℝ))) z - hcirc ω ρ z

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Variance of a radial increment at a fixed centre.** For `s, s' > 0`,
`Var[h_s(z) - h_{s'}(z)] = |log s - log s'|`. -/
theorem variance_circle_sub_same_center (hh : IsWholePlaneGFF P hC hcirc) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') (z : ℂ) :
    Var[fun ω => hcirc ω s z - hcirc ω s' z; P] = |Real.log s - Real.log s'| := by
  rw [hh.variance_circle_sub_eq hs hs' z z]
  simp only [circlePairPotential_self_center hs.le, circlePairPotential_self_center hs'.le]
  rcases le_total s s' with h | h
  · have hl : Real.log s ≤ Real.log s' := Real.log_le_log hs h
    rw [max_eq_left h, max_eq_right h, max_self s, max_self s', abs_of_nonpos (by linarith)]
    ring
  · have hl : Real.log s' ≤ Real.log s := Real.log_le_log hs' h
    rw [max_eq_right h, max_eq_left h, max_self s, max_self s', abs_of_nonneg (by linarith)]
    ring

theorem measurable_radialCircleProcess (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ)
    (t : ℝ≥0) : Measurable (radialCircleProcess hcirc ρ z t) :=
  (hh.measurable_circle _ z (mul_pos hρ (Real.exp_pos _))).sub (hh.measurable_circle ρ z hρ)

/-- **The circle averages at a fixed centre form a Brownian motion in the logarithmic radius.** -/
theorem isPreBrownianReal_radialCircleProcess (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) : IsPreBrownianReal (radialCircleProcess hcirc ρ z) P := by
  have hP := hh.isProbabilityMeasure
  have hpos : ∀ t : ℝ≥0, 0 < ρ * Real.exp (-(t : ℝ)) := fun t => mul_pos hρ (Real.exp_pos _)
  have hG : IsGaussianProcess (radialCircleProcess hcirc ρ z) P :=
    GaussIndep.isGaussianProcess_of_mem_span hh.isGaussianProcess fun t =>
      hh.circle_sub_mem_span (hpos t) hρ z z
  refine hG.isPreBrownianReal_of_covariance (fun t => hh.integral_circle_sub (hpos t) hρ z z) ?_
  intro s t hst
  have hlog : ∀ u : ℝ≥0, Real.log (ρ * Real.exp (-(u : ℝ))) = Real.log ρ - u := fun u => by
    rw [Real.log_mul hρ.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have m1 := hh.memLp_two_circle_sub (hpos s) hρ z z
  have m2 := hh.memLp_two_circle_sub (hpos t) hρ z z
  have v1 := hh.variance_circle_sub_same_center (hpos s) hρ z
  have v2 := hh.variance_circle_sub_same_center (hpos t) hρ z
  have v3 := hh.variance_circle_sub_same_center (hpos s) (hpos t) z
  rw [hlog s, hlog t] at v3
  rw [hlog s] at v1
  rw [hlog t] at v2
  have hst' : (s : ℝ) ≤ t := hst
  rw [show Real.log ρ - s - Real.log ρ = -(s : ℝ) by ring, abs_neg, abs_of_nonneg (NNReal.coe_nonneg s)] at v1
  rw [show Real.log ρ - t - Real.log ρ = -(t : ℝ) by ring, abs_neg, abs_of_nonneg (NNReal.coe_nonneg t)] at v2
  rw [show Real.log ρ - s - (Real.log ρ - t) = (t : ℝ) - s by ring,
    abs_of_nonneg (by linarith)] at v3
  have hsub := variance_sub m1 m2
  have e : (fun ω => hcirc ω (ρ * Real.exp (-(s : ℝ))) z - hcirc ω ρ z) -
      (fun ω => hcirc ω (ρ * Real.exp (-(t : ℝ))) z - hcirc ω ρ z) =
      fun ω => hcirc ω (ρ * Real.exp (-(s : ℝ))) z - hcirc ω (ρ * Real.exp (-(t : ℝ))) z := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  rw [e, v3, v1, v2] at hsub
  change cov[fun ω => hcirc ω (ρ * Real.exp (-(s : ℝ))) z - hcirc ω ρ z,
    fun ω => hcirc ω (ρ * Real.exp (-(t : ℝ))) z - hcirc ω ρ z; P] = s
  linarith

theorem ae_continuous_radialCircleProcess (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) : ∀ᵐ ω ∂P, Continuous fun t => radialCircleProcess hcirc ρ z t ω := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω
  have hf : Continuous fun t : ℝ≥0 => ((ρ * Real.exp (-(t : ℝ)), z) : ℝ × ℂ) := by fun_prop
  have hmap : ∀ t : ℝ≥0, ((ρ * Real.exp (-(t : ℝ)), z) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) :=
    fun t => ⟨mul_pos hρ (Real.exp_pos _), mem_univ _⟩
  exact (hω.comp_continuous hf hmap).sub continuous_const

/-- **Radial supremum bound for circle averages.** For `ρ, T, a > 0`,
`P {∃ r ∈ [ρ e^{-T}, ρ], a ≤ |h_r(z) - h_ρ(z)|} ≤ 2 exp (-a² / (2 T))`. -/
theorem measure_exists_circle_sub_ge_le (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    P {ω | ∃ r ∈ Icc (ρ * Real.exp (-T)) ρ, a ≤ |hcirc ω r z - hcirc ω ρ z|} ≤
      2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
  refine le_trans (measure_mono fun ω hω => ?_)
    (measure_exists_le_abs_ge_le_exp (hh.isPreBrownianReal_radialCircleProcess hρ z)
      (hh.measurable_radialCircleProcess hρ z) (hh.ae_continuous_radialCircleProcess hρ z) hT ha)
  obtain ⟨r, ⟨hr1, hr2⟩, har⟩ := hω
  have hrpos : 0 < r := lt_of_lt_of_le (mul_pos hρ (Real.exp_pos _)) hr1
  have hq : 0 < ρ / r := div_pos hρ hrpos
  have hq1 : 1 ≤ ρ / r := (one_le_div hrpos).2 hr2
  have hqT : ρ / r ≤ Real.exp T := by
    rw [div_le_iff₀ hrpos, mul_comm]
    calc ρ = ρ * Real.exp (-T) * Real.exp T := by rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ r * Real.exp T := mul_le_mul_of_nonneg_right hr1 (Real.exp_pos _).le
  have hlog0 : 0 ≤ Real.log (ρ / r) := Real.log_nonneg hq1
  refine ⟨Real.toNNReal (Real.log (ρ / r)), ?_, ?_⟩
  · rw [Real.coe_toNNReal _ hlog0]
    calc Real.log (ρ / r) ≤ Real.log (Real.exp T) := Real.log_le_log hq hqT
      _ = T := Real.log_exp T
  · have e : ρ * Real.exp (-((Real.toNNReal (Real.log (ρ / r)) : ℝ≥0) : ℝ)) = r := by
      rw [Real.coe_toNNReal _ hlog0, Real.exp_neg, Real.exp_log hq]
      field_simp
    show a ≤ |hcirc ω (ρ * Real.exp (-((Real.toNNReal (Real.log (ρ / r)) : ℝ≥0) : ℝ))) z - hcirc ω ρ z|
    rw [e]
    exact har

end IsWholePlaneGFF

end LatticeProb.Gauss
