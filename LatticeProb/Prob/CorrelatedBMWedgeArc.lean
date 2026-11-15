import LatticeProb.Prob.CorrelatedBMWedgeExit
import LatticeProb.Prob.CorrelatedBMWedgeAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Angular description of a symmetric open wedge -/

set_option autoImplicit false

open Set

namespace LatticeProb.CorrelatedBM

/-- For an opening below π, the linear open wedge is the cone over the
corresponding open arc. The vertex is excluded. -/
theorem mem_openSymmetricWedge_iff_arg {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (z : ℂ) :
    (z.re, z.im) ∈ openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2)) ↔
      z ≠ 0 ∧ z.arg ∈ Ioo (-θ / 2) (θ / 2) := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have htan : Real.tan (θ / 2) = Real.sin (θ / 2) / Real.cos (θ / 2) :=
    Real.tan_eq_sin_div_cos (θ / 2)
  have harctan : Real.arctan (Real.tan (θ / 2)) = θ / 2 :=
    Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith)
  have hangle (hz : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
    have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    have hh := (abs_lt.mp harg)
    rw [← Complex.tan_arg z, Real.arctan_tan hh.1 hh.2]
  have hcore (hz : 0 < z.re) :
      |Real.cos (θ / 2) * z.im| < Real.sin (θ / 2) * z.re ↔
        z.arg ∈ Ioo (-θ / 2) (θ / 2) := by
    rw [hangle hz]
    have hl : -Real.tan (θ / 2) < z.im / z.re ↔
        -θ / 2 < Real.arctan (z.im / z.re) := by
      rw [← Real.arctan_lt_arctan_iff, Real.arctan_neg, harctan]
      ring
    have hu : z.im / z.re < Real.tan (θ / 2) ↔
        Real.arctan (z.im / z.re) < θ / 2 := by
      rw [← Real.arctan_lt_arctan_iff, harctan]
    change |Real.cos (θ / 2) * z.im| < Real.sin (θ / 2) * z.re ↔
      -θ / 2 < Real.arctan (z.im / z.re) ∧ Real.arctan (z.im / z.re) < θ / 2
    rw [← hl, ← hu, abs_lt, htan]
    have heq : Real.sin (θ / 2) / Real.cos (θ / 2) * z.re =
        (Real.sin (θ / 2) * z.re) / Real.cos (θ / 2) := by ring
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor
      · apply (lt_div_iff₀ hz).2
        rw [neg_mul, heq, ← neg_div]
        exact (div_lt_iff₀ hc).2 (by nlinarith)
      · apply (div_lt_iff₀ hz).2
        rw [heq]
        exact (lt_div_iff₀ hc).2 (by nlinarith)
    · rintro ⟨h₁, h₂⟩
      have h₁' := (lt_div_iff₀ hz).1 h₁
      have h₂' := (div_lt_iff₀ hz).1 h₂
      rw [neg_mul, heq, ← neg_div] at h₁'
      rw [heq] at h₂'
      have h₁'' := (div_lt_iff₀ hc).1 h₁'
      have h₂'' := (lt_div_iff₀ hc).1 h₂'
      constructor <;> nlinarith
  constructor
  · intro h
    change |Real.cos (θ / 2) * z.im| < Real.sin (θ / 2) * z.re at h
    have hz : 0 < z.re := (mul_pos_iff_of_pos_left hs).1 (lt_of_le_of_lt (abs_nonneg _) h)
    have hne : z ≠ 0 := by intro hz0; simp [hz0] at hz
    exact ⟨hne, (hcore hz).1 h⟩
  · rintro ⟨hne, harg⟩
    have hbound : |z.arg| < Real.pi / 2 := by
      apply abs_lt.mpr
      constructor <;> linarith [harg.1, harg.2]
    have hz : 0 < z.re := ((Complex.abs_arg_lt_pi_div_two_iff.mp hbound).resolve_right hne)
    exact (hcore hz).2 harg

end LatticeProb.CorrelatedBM
