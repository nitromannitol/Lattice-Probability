import LatticeProb.Prob.CorrelatedBMWedgeArc
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-! # A harmonic power on a symmetric wedge -/

set_option autoImplicit false

open Set InnerProductSpace

namespace LatticeProb

/-- The real part of a principal complex power is harmonic away from the
nonpositive real axis. -/
theorem harmonicAt_re_cpow {p : ℝ} {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HarmonicAt (fun w : ℂ => (w ^ (p : ℂ)).re) z := by
  exact ((analyticAt_id.cpow analyticAt_const hz).harmonicAt_re)

/-- The real part of a real complex power in polar coordinates. -/
theorem re_cpow_eq_rpow_mul_cos_arg {p : ℝ} {z : ℂ} (hz : z ≠ 0) :
    (z ^ (p : ℂ)).re = ‖z‖ ^ p * Real.cos (p * z.arg) := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, Complex.log_re, Complex.log_im]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
  rw [mul_comm z.arg p]

/-- The principal power profile is harmonic and positive in an open
symmetric wedge of opening less than π. -/
theorem wedge_re_cpow_harmonic_pos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    {z : ℂ} (hz : (z.re, z.im) ∈
      LatticeProb.CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))) :
    HarmonicAt (fun w : ℂ => (w ^ ((Real.pi / θ : ℝ) : ℂ)).re) z ∧
      0 < (z ^ ((Real.pi / θ : ℝ) : ℂ)).re := by
  obtain ⟨hne, ha⟩ := (LatticeProb.CorrelatedBM.mem_openSymmetricWedge_iff_arg hθ0 hθπ z).1 hz
  have hzre : 0 < z.re := by
    apply (Complex.abs_arg_lt_pi_div_two_iff.mp ?_).resolve_right hne
    apply abs_lt.mpr
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  have hslit : z ∈ Complex.slitPlane := Or.inl hzre
  constructor
  · exact harmonicAt_re_cpow hslit
  · rw [re_cpow_eq_rpow_mul_cos_arg hne]
    apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hne) _)
    apply Real.cos_pos_of_mem_Ioo
    have hp : 0 < Real.pi / θ := div_pos Real.pi_pos hθ0
    have he : (Real.pi / θ) * (θ / 2) = Real.pi / 2 := by field_simp
    constructor
    · have hh := mul_lt_mul_of_pos_left ha.1 hp
      rw [show (Real.pi / θ) * (-θ / 2) = -(Real.pi / 2) by rw [← he]; ring] at hh
      exact hh
    · have hh := mul_lt_mul_of_pos_left ha.2 hp
      rw [he] at hh
      exact hh


/-- Along the positive axis the profile is the corresponding real power. -/
theorem re_cpow_ofReal {p r : ℝ} (hr : 0 ≤ r) :
    (((r : ℂ) ^ (p : ℂ)).re) = r ^ p := by
  rw [← Complex.ofReal_cpow hr]
  exact Complex.ofReal_re _

/-- The profile vanishes at the wedge vertex for a positive exponent. -/
theorem re_zero_cpow_of_pos {p : ℝ} (hp : 0 < p) :
    (((0 : ℂ) ^ (p : ℂ)).re) = 0 := by
  rw [Complex.zero_cpow (by exact_mod_cast ne_of_gt hp)]
  exact Complex.zero_re

/-- The power profile vanishes on the two nonzero boundary rays. -/
theorem wedge_re_cpow_eq_zero_of_arg {θ : ℝ} (hθ : 0 < θ) {z : ℂ}
    (hz : z ≠ 0) (ha : z.arg = θ / 2 ∨ z.arg = -θ / 2) :
    (z ^ ((Real.pi / θ : ℝ) : ℂ)).re = 0 := by
  rw [re_cpow_eq_rpow_mul_cos_arg hz]
  have he : Real.pi / θ * (θ / 2) = Real.pi / 2 := by field_simp
  rcases ha with ha | ha
  · rw [ha, he, Real.cos_pi_div_two, mul_zero]
  · rw [ha, show Real.pi / θ * (-θ / 2) = -(Real.pi / 2) by rw [← he]; ring,
      Real.cos_neg, Real.cos_pi_div_two, mul_zero]

end LatticeProb
