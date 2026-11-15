import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Parameters for a Brownian scale-count bound -/

set_option autoImplicit false
open scoped NNReal

namespace LatticeProb.LQG

/-- A logarithmic time cutoff turns the Brownian exponential bound into a
power of the smaller scale. The exponent can be tuned through `ell`. -/
theorem exists_scale_tail_parameters {γ d ell b : ℝ}
    (hγ : 0 < γ) (hd : 0 < d) (hell : 0 < ell) (hb : 0 < b) (hb1 : b < 1) :
    ∃ (u : ℝ) (T : ℝ≥0), 0 < u ∧ 0 < T ∧
      (T : ℝ) = (γ⁻¹ * Real.log 1 - γ⁻¹ * Real.log b) / d + u ∧
      Real.exp (-((d * u) ^ 2 / (2 * T))) =
        b ^ (d * ell ^ 2 / (2 * γ * (1 + ell))) := by
  have hlog : Real.log b < 0 := Real.log_neg hb hb1
  let A : ℝ := -Real.log b / (γ * d)
  have hA : 0 < A := div_pos (neg_pos.mpr hlog) (mul_pos hγ hd)
  let u : ℝ := ell * A
  let T : ℝ≥0 := ⟨(1 + ell) * A, (mul_pos (by linarith) hA).le⟩
  have hu : 0 < u := mul_pos hell hA
  have hT : 0 < (T : ℝ) := mul_pos (by linarith) hA
  refine ⟨u, T, hu, ?_, ?_, ?_⟩
  · exact_mod_cast hT
  · change (1 + ell) * A = (γ⁻¹ * Real.log 1 - γ⁻¹ * Real.log b) / d + ell * A
    dsimp [A]
    rw [Real.log_one]
    field_simp [ne_of_gt hγ, ne_of_gt hd]
    ring
  · change Real.exp (-((d * (ell * A)) ^ 2 / (2 * ((1 + ell) * A)))) = _
    rw [Real.rpow_def_of_pos hb]
    congr 1
    field_simp [ne_of_gt hA, ne_of_gt hγ, ne_of_gt hd,
      ne_of_gt (show 0 < 1 + ell by linarith)]
    dsimp [A]
    field_simp [ne_of_gt hγ, ne_of_gt hd]

end LatticeProb.LQG
