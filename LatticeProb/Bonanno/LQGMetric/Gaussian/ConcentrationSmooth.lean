/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.ConcentrationSmooth at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sharp sub-Gaussian MGF bound for smooth bounded functions of a standard Gaussian vector

Source: R. J. Adler, J. E. Taylor, *Random Fields and Geometry* (Springer 2007), Lemma 2.1.5
(p. 54–55): if `h` is smooth with Lipschitz constant `L` and `E h(X) = 0`, then
`E e^{t h(X)} ≤ e^{t² L²/2}`. Proof as there: by the covariance identity (Lemma 2.1.4,
`GaussConc.integral_mul_sub_eq_cov`) with `g = e^{t h}`, `E[h e^{t h}] ≤ t L² E[e^{t h}]`, i.e.
`(log H)' ≤ t L²` for `H(t) = E e^{t h}`; we integrate it in the form
`t ↦ H(t) e^{-t²L²/2}` is antitone on `[0, ∞)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace LQGMetric

namespace GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {f : E → ℝ} {f' : E → E} {C L : ℝ}

/-- `exp (t f)` is again bounded `C¹` with bounded gradient. -/
lemma SmoothBdd.exp_mul (hf : SmoothBdd f f' C L) {t : ℝ} (ht : 0 ≤ t) :
    SmoothBdd (fun x => exp (t * f x)) (fun x => (t * exp (t * f x)) • f' x)
      (exp (t * C)) (t * exp (t * C) * L) where
  hasGrad x := by
    have h := ((hf.hasFDerivAt x).const_mul t).exp
    rw [smul_smul] at h
    rw [hasGradientAt_iff_hasFDerivAt, map_smulₛₗ, conj_trivial, mul_comm]
    exact h
  cont' := ((continuous_const.mul (continuous_const.mul hf.continuous).rexp)).smul hf.cont'
  bdd x := by
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hf.bdd x)) ht)
  bdd' x := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    · exact (le_abs_self _).trans (hf.bdd x)
    · exact hf.bdd' x

/-- `-f` is again bounded `C¹` with bounded gradient. -/
lemma SmoothBdd.neg (hf : SmoothBdd f f' C L) : SmoothBdd (fun x => -f x) (fun x => -f' x) C L where
  hasGrad x := by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hf.hasFDerivAt x).neg
  cont' := hf.cont'.neg
  bdd x := by rw [abs_neg]; exact hf.bdd x
  bdd' x := by rw [norm_neg]; exact hf.bdd' x

lemma SmoothBdd.integrable_exp (hf : SmoothBdd f f' C L) (t : ℝ) :
    Integrable (fun x => exp (t * f x)) (stdGaussian E) :=
  Integrable.of_bound ((continuous_const.mul hf.continuous).rexp).aestronglyMeasurable
    (exp (|t| * C)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.2 ((le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.bdd x) (abs_nonneg _))))

/-- The derivative inequality `E[f e^{t f}] ≤ t L² E[e^{t f}]` (Adler–Taylor, proof of
Lemma 2.1.5). -/
lemma integral_mul_exp_le (hf : SmoothBdd f f' C L) (h0 : ∫ x, f x ∂(stdGaussian E) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, f x * exp (t * f x) ∂(stdGaussian E) ≤
      t * L ^ 2 * ∫ x, exp (t * f x) ∂(stdGaussian E) := by
  set μ := stdGaussian E
  have hg := hf.exp_mul ht
  have hcov := integral_mul_sub_eq_cov hf hg
  rw [h0, zero_mul, sub_zero] at hcov
  rw [hcov]
  set K := t * L ^ 2 * ∫ x, exp (t * f x) ∂μ
  have hK : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun x => (exp_pos _).le)
  have hL := hf.C'_nonneg
  have hinner : ∀ θ : ℝ, ∫ p, ⟪f' (Real.sin θ • p.1 + Real.cos θ • p.2),
      (t * exp (t * f p.1)) • f' p.1⟫ ∂(μ.prod μ) ≤ K := by
    intro θ
    have hi : Integrable (fun p : E × E => t * L ^ 2 * exp (t * f p.1)) (μ.prod μ) :=
      ((hf.integrable_exp t).comp_fst μ).const_mul _
    calc _ ≤ ∫ p, t * L ^ 2 * exp (t * f p.1) ∂(μ.prod μ) := by
          refine integral_mono (Integrable.of_bound ((hf.cont'.comp (by fun_prop)).inner
            (hg.cont'.comp continuous_fst)).aestronglyMeasurable (L * (t * exp (t * C) * L))
            (ae_of_all _ fun p => (abs_real_inner_le_norm _ _).trans
              (mul_le_mul (hf.bdd' _) (hg.bdd' _) (norm_nonneg _) hL))) hi fun p => ?_
          · rw [real_inner_smul_right]
            have h1 : ⟪f' (Real.sin θ • p.1 + Real.cos θ • p.2), f' p.1⟫ ≤ L ^ 2 :=
              (real_inner_le_norm _ _).trans (by
                rw [sq]; exact mul_le_mul (hf.bdd' _) (hf.bdd' _) (norm_nonneg _) hL)
            have h2 : 0 ≤ t * exp (t * f p.1) := by positivity
            nlinarith
      _ = K := by
          rw [integral_prod_fst_stdGaussian (h := fun x => t * L ^ 2 * exp (t * f x))
            ((hf.integrable_exp t).const_mul _), integral_const_mul]
  by_cases hint : IntervalIntegrable (fun θ => Real.cos θ * ∫ p, ⟪f' (Real.sin θ • p.1 +
      Real.cos θ • p.2), (t * exp (t * f p.1)) • f' p.1⟫ ∂(μ.prod μ)) volume 0 (π / 2)
  · calc _ ≤ ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ * K := by
          refine intervalIntegral.integral_mono_on (by positivity) hint
            ((by fun_prop : Continuous fun θ => Real.cos θ * K).intervalIntegrable _ _) fun θ hθ => ?_
          have : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,
            Real.pi_pos], hθ.2⟩
          exact mul_le_mul_of_nonneg_left (hinner θ) this
      _ = K := by
          rw [intervalIntegral.integral_mul_const, integral_cos]
          simp
  · rw [intervalIntegral.integral_undef hint]
    exact hK

/-- Sharp sub-Gaussian MGF bound for `t ≥ 0` (Adler–Taylor, Lemma 2.1.5). -/
lemma mgf_le_of_nonneg (hf : SmoothBdd f f' C L) (h0 : ∫ x, f x ∂(stdGaussian E) = 0) {t : ℝ}
    (ht : 0 ≤ t) : mgf f (stdGaussian E) t ≤ exp (t ^ 2 * L ^ 2 / 2) := by
  set μ := stdGaussian E
  have hset : integrableExpSet f μ = univ := eq_univ_of_forall fun s => hf.integrable_exp s
  have hH : ∀ s, HasDerivAt (mgf f μ) (∫ x, f x * exp (s * f x) ∂μ) s := fun s =>
    hasDerivAt_mgf (by rw [hset, interior_univ]; exact mem_univ s)
  set φ : ℝ → ℝ := fun s => mgf f μ s * exp (-(s ^ 2 * L ^ 2 / 2)) with hφdef
  have hφ : ∀ s, HasDerivAt φ ((∫ x, f x * exp (s * f x) ∂μ) * exp (-(s ^ 2 * L ^ 2 / 2)) +
      mgf f μ s * (exp (-(s ^ 2 * L ^ 2 / 2)) * (-(s * L ^ 2)))) s := by
    intro s
    refine (hH s).mul ?_
    have h2 : HasDerivAt (fun s : ℝ => -(s ^ 2 * L ^ 2 / 2)) (-(s * L ^ 2)) s := by
      have := (((hasDerivAt_pow 2 s).mul_const (L ^ 2)).div_const 2).neg
      refine this.congr_deriv ?_
      push_cast
      ring
    exact h2.exp
  have hanti : AntitoneOn φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun s _ => (hφ s).continuousAt.continuousWithinAt)
      (fun s _ => (hφ s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hφ s).deriv]
    have h1 := integral_mul_exp_le hf h0 (le_of_lt hs)
    have hmgf : mgf f μ s = ∫ x, exp (s * f x) ∂μ := rfl
    have he := exp_pos (-(s ^ 2 * L ^ 2 / 2))
    have h3 := mul_le_mul_of_nonneg_right h1 he.le
    rw [hmgf]
    nlinarith
  have h := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only [hφdef, mgf_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, zero_div, neg_zero, exp_zero, mul_one] at h
  rw [exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)] at h
  exact h

/-- **Sharp sub-Gaussian MGF bound** (Adler–Taylor, Lemma 2.1.5): for a bounded `C¹` function
`f` with `‖∇f‖ ≤ L` and `E f = 0` under the standard Gaussian, `E e^{t f} ≤ e^{t² L²/2}` for
all real `t`. -/
theorem mgf_le_of_smoothBdd (hf : SmoothBdd f f' C L) (h0 : ∫ x, f x ∂(stdGaussian E) = 0)
    (t : ℝ) : mgf f (stdGaussian E) t ≤ exp (t ^ 2 * L ^ 2 / 2) := by
  rcases le_total 0 t with ht | ht
  · exact mgf_le_of_nonneg hf h0 ht
  · have h0' : ∫ x, -f x ∂(stdGaussian E) = 0 := by rw [integral_neg, h0, neg_zero]
    have h := mgf_le_of_nonneg hf.neg h0' (neg_nonneg.2 ht)
    have e : mgf (fun x => -f x) (stdGaussian E) (-t) = mgf f (stdGaussian E) t := by
      simp [mgf]
    rwa [e, neg_sq] at h

end GaussConc

end LQGMetric
