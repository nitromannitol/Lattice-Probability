/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.PittCore at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.SteinIBP
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pitt's inequality for the standard Gaussian: the smooth core

Let `γ` be the standard Gaussian measure of a finite-dimensional real inner product space `E`,
and `F, G : E → ℝ` bounded `C¹` functions with bounded continuous gradients `F', G'` such that
`⟪F' x, G' y⟫ ≥ 0` for all `x, y`. Then `E[F] E[G] ≤ E[F G]`
(`LQGMetric.Pitt.integral_mul_le_integral_mul_stdGaussian`).

This is the Gaussian interpolation argument of L. D. Pitt, *Positively correlated normal variables
are associated*, Ann. Probab. 10 (1982) 496–499 (the interpolation between `(X, X)` and two
independent copies `(X, Y)`), written with the rotation `(x, y) ↦ (cos θ x + sin θ y,
-sin θ x + cos θ y)` of `γ ⊗ γ`: with
`φ(θ) = E[F(x) G(cos θ x + sin θ y)]`, `φ(0) = E[F G]` and `φ(π/2) = E[F] E[G]`, and after the
rotation and Gaussian integration by parts in the second variable,
`φ'(θ) = - sin θ E[⟪F'(cos θ u - sin θ w), G'(u)⟫] ≤ 0`.

Reused: mathlib's rotation invariance `ProbabilityTheory.IsGaussian.map_rotation_eq_self` and
LQGDimension's Stein lemma `LQGDimension.SteinIBP.integral_inner_mul_stdGaussian`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGMetric

namespace Pitt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasDerivAt_rotCurve (x y : E) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos t • x + Real.sin t • y)
      (-Real.sin θ • x + Real.cos θ • y) θ := by
  have h1 := (Real.hasDerivAt_cos θ).smul_const x
  have h2 := (Real.hasDerivAt_sin θ).smul_const y
  exact h1.add h2

lemma integrable_norm_fst_add_snd :
    Integrable (fun p : E × E => ‖p.1‖ + ‖p.2‖) ((stdGaussian E).prod (stdGaussian E)) := by
  have h : Integrable (fun x : E => ‖x‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  exact (h.comp_fst _).add (h.comp_snd _)

/-- **Pitt's inequality, smooth core.** -/
theorem integral_mul_le_integral_mul_stdGaussian {F G : E → ℝ} {F' G' : E → E}
    {CF CG CF' CG' : ℝ}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (F' x)) x) (hG : ∀ x, HasFDerivAt G (innerSL ℝ (G' x)) x)
    (hF'c : Continuous F') (hG'c : Continuous G')
    (hFb : ∀ x, |F x| ≤ CF) (hGb : ∀ x, |G x| ≤ CG)
    (hF'b : ∀ x, ‖F' x‖ ≤ CF') (hG'b : ∀ x, ‖G' x‖ ≤ CG')
    (hpos : ∀ x y, 0 ≤ ⟪F' x, G' y⟫) :
    (∫ x, F x ∂stdGaussian E) * (∫ x, G x ∂stdGaussian E) ≤
      ∫ x, F x * G x ∂stdGaussian E := by
  set γ := stdGaussian E with hγ
  set ν := γ.prod γ with hν
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hFb 0)
  have hCG' : 0 ≤ CG' := (norm_nonneg _).trans (hG'b 0)
  -- the interpolation
  set Φ : ℝ → E × E → ℝ := fun θ p => F p.1 * G (Real.cos θ • p.1 + Real.sin θ • p.2) with hΦ
  set D : ℝ → E × E → ℝ := fun θ p =>
    F p.1 * ⟪G' (Real.cos θ • p.1 + Real.sin θ • p.2), -Real.sin θ • p.1 + Real.cos θ • p.2⟫
    with hD
  have hΦc : ∀ θ, Continuous (Φ θ) := fun θ => by
    simp only [hΦ]; fun_prop
  have hDc : ∀ θ, Continuous (D θ) := fun θ => by
    simp only [hD]
    exact (hFc.comp continuous_fst).mul ((hG'c.comp (by fun_prop)).inner (by fun_prop))
  have hΦint : ∀ θ, Integrable (Φ θ) ν := fun θ =>
    Integrable.of_bound (hΦc θ).aestronglyMeasurable (CF * CG) (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb _) (hGb _) (abs_nonneg _) hCF)
  have hDbound : ∀ θ p, ‖D θ p‖ ≤ CF * CG' * (‖p.1‖ + ‖p.2‖) := fun θ p => by
    simp only [hD, Real.norm_eq_abs, abs_mul]
    have h1 : |⟪G' (Real.cos θ • p.1 + Real.sin θ • p.2), -Real.sin θ • p.1 + Real.cos θ • p.2⟫|
        ≤ CG' * (‖p.1‖ + ‖p.2‖) := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hG'b _) ?_ (norm_nonneg _) hCG')
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
    calc |F p.1| * |_| ≤ CF * (CG' * (‖p.1‖ + ‖p.2‖)) :=
          mul_le_mul (hFb _) h1 (abs_nonneg _) hCF
      _ = _ := by ring
  have hderiv : ∀ θ, HasDerivAt (fun t => ∫ p, Φ t p ∂ν) (∫ p, D θ p ∂ν) θ := fun θ => by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (Eventually.of_forall fun t => (hΦc t).aestronglyMeasurable) (hΦint θ)
      (hDc θ).aestronglyMeasurable (ae_of_all _ fun p t _ => hDbound t p)
      (integrable_norm_fst_add_snd.const_mul (CF * CG'))
      (ae_of_all _ fun p t _ => ?_)).2
    have hc := (hG (Real.cos t • p.1 + Real.sin t • p.2)).comp_hasDerivAt t
      (hasDerivAt_rotCurve p.1 p.2 t)
    simpa [hΦ, hD, Function.comp_def] using hc.const_mul (F p.1)
  -- the sign of the derivative
  have hDneg : ∀ θ ∈ Icc (0 : ℝ) π, ∫ p, D θ p ∂ν ≤ 0 := by
    intro θ hθ
    set c := Real.cos θ
    set s := Real.sin θ
    have hs : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    set K : E × E → ℝ := fun q => F (c • q.1 - s • q.2) * ⟪G' q.1, q.2⟫ with hK
    have hKc : Continuous K := by
      simp only [hK]
      exact (hFc.comp (by fun_prop)).mul ((hG'c.comp continuous_fst).inner continuous_snd)
    have hDK : D θ = K ∘ ContinuousLinearMap.rotation θ := by
      funext p
      simp only [hD, hK, Function.comp_apply, ContinuousLinearMap.rotation_apply]
      congr 2
      have : c • (c • p.1 + s • p.2) - s • (-s • p.1 + c • p.2) = (c ^ 2 + s ^ 2) • p.1 := by
        module
      rw [this, Real.cos_sq_add_sin_sq, one_smul]
    have hrot : ν.map (ContinuousLinearMap.rotation θ) = ν :=
      IsGaussian.map_rotation_eq_self (μ := γ) integral_id_stdGaussian θ
    have hKint : Integrable K ν := by
      refine (integrable_norm_fst_add_snd.const_mul (CF * CG')).mono' hKc.aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |F (c • q.1 - s • q.2)| * |⟪G' q.1, q.2⟫| ≤ CF * (CG' * ‖q.2‖) :=
            mul_le_mul (hFb _) ((abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right (hG'b _) (norm_nonneg _))) (abs_nonneg _) hCF
        _ ≤ CF * CG' * (‖q.1‖ + ‖q.2‖) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
              (mul_nonneg hCF hCG')
    have hDK' : ∫ p, D θ p ∂ν = ∫ q, K q ∂ν := by
      rw [hDK]
      show ∫ p, K (ContinuousLinearMap.rotation θ p) ∂ν = _
      rw [← integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
        (by rw [hrot]; exact hKc.aestronglyMeasurable), hrot]
    rw [hDK', integral_prod K hKint]
    refine integral_nonpos fun u => ?_
    have hstein := LQGDimension.SteinIBP.integral_inner_mul_stdGaussian (E := E)
      (G := fun w => F (c • u - s • w)) (G' := fun w => -s • F' (c • u - s • w))
      (C := CF) (C' := s * CF') (fun x e t => ?_) (hFc.comp (by fun_prop))
      (continuous_const.smul (hF'c.comp (by fun_prop))) (fun x => hFb _)
      (fun x => by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs]
                   exact mul_le_mul_of_nonneg_left (hF'b _) hs) (G' u)
    · have h1 : ∫ w, K (u, w) ∂γ = ∫ w, ⟪G' u, w⟫ * F (c • u - s • w) ∂γ := by
        simp only [hK]; exact integral_congr_ae (ae_of_all _ fun w => mul_comm _ _)
      rw [h1, hstein]
      refine integral_nonpos fun w => ?_
      simp only [inner_smul_left, RCLike.conj_to_real]
      rw [neg_mul]
      exact neg_nonpos.2 (mul_nonneg hs (hpos _ _))
    · have hcurve : HasDerivAt (fun r : ℝ => c • u - s • (x + r • e)) (-(s • e)) t := by
        have := (((hasDerivAt_id t).smul_const e).const_add x).const_smul s
        simpa using this.const_sub (c • u)
      have hc := (hF (c • u - s • (x + t • e))).comp_hasDerivAt t hcurve
      have heq : (innerSL ℝ (F' (c • u - s • (x + t • e)))) (-(s • e)) =
          ⟪-s • F' (c • u - s • (x + t • e)), e⟫ := by
        rw [innerSL_apply_apply]; simp [inner_smul_left, inner_smul_right]
      rw [heq] at hc
      exact hc
  -- monotonicity of the interpolation
  have hanti : AntitoneOn (fun t => ∫ p, Φ t p ∂ν) (Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hderiv t).deriv]
    exact hDneg t ⟨ht.1.le, ht.2.le.trans (by linarith [Real.pi_pos])⟩
  have hle := hanti ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)
  simp only [hΦ, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_smul, zero_smul, add_zero, zero_add] at hle
  rw [integral_prod_mul (fun x => F x) (fun y => G y)] at hle
  rw [integral_fun_fst (fun x => F x * G x)] at hle
  simpa using hle

end Pitt

end LQGMetric
