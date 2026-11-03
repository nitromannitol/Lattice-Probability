/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3C at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3B

/-!
# Germ step for unbounded `V`: a radial Hardy inequality (task P2-MKD3)

* `ray_cs`: `(∫_a^b φ)² ≤ log (b/a) ∫_a^b t φ(t)² dt` (Cauchy–Schwarz with weight `1/t`);
* `ray_sq_le`: along a ray, `(g(ρe^{iθ}) − g(se^{iθ}))² ≤ log (ρ/s) ∫_s^ρ t ‖∇g(te^{iθ})‖² dt`.

These are the one-dimensional inputs of the logarithmic Hardy inequality behind the uniform
bound for log-cutoff truncations (`mem_range_cmIso_of_orth_trunc`). Own elementary proofs (FTC
along rays + Cauchy–Schwarz, as in QZ `BubbleHardy.lean` `interval_cauchy_schwarz_sq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace LQGMetric
namespace MarkovGermVer

/-- Cauchy–Schwarz with weight `1/t` on `[a, b] ⊆ (0, ∞)` -/
theorem ray_cs {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, φ t) ^ 2 ≤ Real.log (b / a) * ∫ t in a..b, t * φ t ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  set T := Real.log (b / a) with hT
  set m := ∫ t in a..b, φ t
  set S := ∫ t in a..b, t * φ t ^ 2
  have hTint : ∫ t in a..b, t⁻¹ = T := integral_inv_of_pos ha hb
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
    rw [uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
    (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne').intervalIntegrable
  have hi1 : IntervalIntegrable (fun t => t * φ t ^ 2) volume a b :=
    ((continuous_id.mul (hφ.pow 2))).intervalIntegrable a b
  have hi2 : IntervalIntegrable φ volume a b := hφ.intervalIntegrable a b
  have h0 : 0 ≤ ∫ t in a..b, t * (T * φ t - m * t⁻¹) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t ht =>
      mul_nonneg (ha.le.trans ht.1) (sq_nonneg _)
  have e : ∫ t in a..b, t * (T * φ t - m * t⁻¹) ^ 2 =
      ∫ t in a..b, (T ^ 2 * (t * φ t ^ 2) - (2 * T * m) * φ t + m ^ 2 * t⁻¹) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have := (hpos t ht).ne'
    field_simp; ring
  rw [e, intervalIntegral.integral_add ((hi1.const_mul _).sub (hi2.const_mul _))
      (hinv.const_mul _),
    intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hTint] at h0
  have hT0 : 0 ≤ T := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have h1 : 0 ≤ T * (T * S - m ^ 2) := by nlinarith
  rcases eq_or_lt_of_le hT0 with h | h
  · -- `T = 0` forces `a = b`
    have hba : b = a := by
      have h' : b / a = 1 := by
        have := Real.eq_one_of_pos_of_log_eq_zero (div_pos hb ha) h.symm
        exact this
      field_simp at h'; linarith
    have hm0 : m = 0 := by simp [m, hba]
    rw [hm0, ← h]; simp
  · have h2 : 0 ≤ T * S - m ^ 2 := (mul_nonneg_iff_of_pos_left h).mp h1
    nlinarith

/-- FTC along a ray plus `ray_cs` -/
theorem ray_sq_le {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (θ : ℝ) {s ρ : ℝ} (hs : 0 < s)
    (hsρ : s ≤ ρ) :
    (g (circleMap 0 ρ θ) - g (circleMap 0 s θ)) ^ 2 ≤
      Real.log (ρ / s) * ∫ t in s..ρ, t * ‖fderiv ℝ g (circleMap 0 t θ)‖ ^ 2 := by
  set u : ℂ := Complex.exp (θ * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hcm : ∀ t : ℝ, circleMap 0 t θ = (t : ℂ) * u := fun t => by simp [circleMap, u]
  have hcd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => circleMap 0 t θ) u t := fun t => by
    simp only [hcm]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u
  have hcc : Continuous fun t : ℝ => circleMap 0 t θ := by
    simp only [hcm]; fun_prop
  set φ' : ℝ → ℝ := fun t => fderiv ℝ g (circleMap 0 t θ) u
  have hφ'c : Continuous φ' :=
    ((hg.continuous_fderiv one_ne_zero).comp hcc).clm_apply continuous_const
  have hder : ∀ t, HasDerivAt (fun t => g (circleMap 0 t θ)) (φ' t) t := fun t =>
    ((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hcd t)
  have hftc : ∫ t in s..ρ, φ' t = g (circleMap 0 ρ θ) - g (circleMap 0 s θ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      (hφ'c.intervalIntegrable _ _)
  rw [← hftc]
  refine (ray_cs hφ'c hs hsρ).trans (mul_le_mul_of_nonneg_left ?_
    (Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)))
  have hA : Continuous fun t : ℝ => t * φ' t ^ 2 := continuous_id.mul (hφ'c.pow 2)
  have hB : Continuous fun t : ℝ => t * ‖fderiv ℝ g (circleMap 0 t θ)‖ ^ 2 :=
    continuous_id.mul (((hg.continuous_fderiv one_ne_zero).comp hcc).norm.pow 2)
  refine intervalIntegral.integral_mono_on hsρ (hA.intervalIntegrable _ _)
    (hB.intervalIntegrable _ _) fun t ht => ?_
  have ht0 : 0 ≤ t := hs.le.trans ht.1
  refine mul_le_mul_of_nonneg_left ?_ ht0
  have : |φ' t| ≤ ‖fderiv ℝ g (circleMap 0 t θ)‖ := by
    have := (fderiv ℝ g (circleMap 0 t θ)).le_opNorm u
    rw [hu, mul_one, Real.norm_eq_abs] at this; exact this
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

end MarkovGermVer
end LQGMetric
