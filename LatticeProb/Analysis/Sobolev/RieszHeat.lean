import LatticeProb.Analysis.Sobolev.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Riesz-heat integral

For `0 < β < d` and `t > 0`, the function `z ↦ ‖z‖ ^ (-β) h_t(z)` on `ℝ^d`, where
`h_t(z) = (4πt)^{-d/2} exp(-‖z‖² / (4t))` is the heat kernel, is integrable, and its integral is
`C t^{-β/2}` for a constant `C ≥ 0` independent of `t`.

The integrand is radial. In polar coordinates (`integral_fun_norm_addHaar`) its integral is
`d |B₁| (4πt)^{-d/2} ∫₀^∞ y^{d-1-β} exp(-y²/(4t)) dy`. The radial integral converges because
`d - 1 - β > -1`, and it equals `(4t)^{(d-β)/2} Γ((d-β)/2) / 2` by the Gamma integral.
-/

open MeasureTheory Set Real

namespace LatticeProb.Sobolev

/-- **The Riesz-heat integral.** For `0 < β < d` there is `C ≥ 0` such that, for every `t > 0`,
`z ↦ ‖z‖ ^ (-β) (4πt)^{-d/2} exp(-‖z‖²/(4t))` is integrable on `ℝ^d` with integral at most
`C t^{-β/2}`. -/
theorem rieszHeat_bound : ∀ (d : ℕ) (β : ℝ), 0 < β → β < d → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
    Integrable (fun z : Space d => ‖z‖ ^ (-β) *
      ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t)))) ∧
    ∫ z : Space d, ‖z‖ ^ (-β) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t)))
      ≤ C * t ^ (-β / 2) := by
  intro d β hβ hβd
  have hd1 : 1 ≤ d := by
    have h0 : (0 : ℝ) < d := by linarith
    exact_mod_cast h0
  have hdim : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  have : Nontrivial (Space d) := Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hq : -1 < (d : ℝ) - 1 - β := by linarith
  have hdβ : 0 < ((d : ℝ) - β) / 2 := by linarith
  set V : ℝ := (volume : Measure (Space d)).real (Metric.ball 0 1) with hV
  refine ⟨d * V * ((4 * π) ^ (-(d : ℝ) / 2) * (4 : ℝ) ^ (((d : ℝ) - β) / 2) * (1 / 2) *
    Gamma (((d : ℝ) - β) / 2)), ?_, ?_⟩
  · have hV0 : 0 ≤ V := measureReal_nonneg
    have hΓ := Gamma_pos_of_pos hdβ
    have h1 : 0 ≤ (4 * π) ^ (-(d : ℝ) / 2) := rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (4 : ℝ) ^ (((d : ℝ) - β) / 2) := rpow_nonneg (by norm_num) _
    have := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (by norm_num : (0 : ℝ) ≤ 1 / 2)) hΓ.le
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hV0) this
  intro t ht
  set A : ℝ := (4 * π * t) ^ (-(d : ℝ) / 2) with hA
  have hb : 0 < 1 / (4 * t) := by positivity
  have key : EqOn (fun y : ℝ => A * (y ^ ((d : ℝ) - 1 - β) * exp (-(1 / (4 * t)) * y ^ 2)))
      (fun y : ℝ => y ^ (d - 1) • (y ^ (-β) * (A * exp (-y ^ 2 / (4 * t))))) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    try simp only
    rw [smul_eq_mul, ← rpow_natCast y (d - 1), Nat.cast_sub hd1, Nat.cast_one]
    have hsplit : y ^ ((d : ℝ) - 1 - β) = y ^ ((d : ℝ) - 1) * y ^ (-β) := by
      rw [← rpow_add hy, sub_eq_add_neg ((d : ℝ) - 1) β]
    have he : -y ^ 2 / (4 * t) = -(1 / (4 * t)) * y ^ 2 := by ring
    rw [hsplit, he]
    ring
  have hrad : IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (Space d) - 1) • (y ^ (-β) * (A * exp (-y ^ 2 / (4 * t)))))
      (Ioi 0) := by
    rw [hdim]
    exact IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_sq hb hq) A)
      key measurableSet_Ioi
  refine ⟨(integrable_fun_norm_addHaar (volume : Measure (Space d))
    (f := fun y : ℝ => y ^ (-β) * (A * exp (-y ^ 2 / (4 * t))))).2 hrad, le_of_eq ?_⟩
  have hpolar := integral_fun_norm_addHaar (volume : Measure (Space d))
    (fun y : ℝ => y ^ (-β) * (A * exp (-y ^ 2 / (4 * t))))
  try simp only at hpolar
  rw [hpolar, hdim, ← hV, setIntegral_congr_fun measurableSet_Ioi key.symm, integral_const_mul]
  have hG := integral_rpow_mul_exp_neg_mul_rpow two_pos hq hb
  simp only [rpow_two] at hG
  rw [hG]
  have hAeq : A = (4 * π) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) := by
    rw [hA]
    exact mul_rpow (by positivity) ht.le
  have hbeq : (1 / (4 * t)) ^ (-((d : ℝ) - 1 - β + 1) / 2)
      = (4 : ℝ) ^ (((d : ℝ) - β) / 2) * t ^ (((d : ℝ) - β) / 2) := by
    rw [show -((d : ℝ) - 1 - β + 1) / 2 = -(((d : ℝ) - β) / 2) by ring, one_div,
      inv_rpow (by positivity), rpow_neg (by positivity), inv_inv, mul_rpow (by norm_num) ht.le]
  have htt : t ^ (-β / 2) = t ^ (-(d : ℝ) / 2) * t ^ (((d : ℝ) - β) / 2) := by
    rw [← rpow_add ht]
    congr 1
    ring
  rw [hAeq, hbeq, htt, show ((d : ℝ) - 1 - β + 1) / 2 = ((d : ℝ) - β) / 2 by ring, smul_eq_mul,
    nsmul_eq_mul]
  ring

end LatticeProb.Sobolev
