/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.PittSmooth at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector

/-!
# Pitt's inequality for `C¹` Lipschitz monotone functions of a Gaussian vector

`LQGMetric.Pitt.integral_mul_le_of_contDiff`: for `X : Ω → (ι → ℝ)` with Gaussian law and
nonnegative covariances, and bounded, Lipschitz, monotone `C¹` functions `f, g`,
`E[f(X)] E[g(X)] ≤ E[f(X) g(X)]`.  This is the smooth case of L. D. Pitt, *Positively correlated
normal variables are associated*, Ann. Probab. 10 (1982) 496–499, obtained from the smooth core
`LQGMetric.Pitt.integral_mul_le_integral_mul_stdGaussian` through the Gram representation
`LQGMetric.Pitt.exists_gram_map_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace Pitt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_comp_gram {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (m : ι → ℝ) (v : ι → E)
    (x : E) :
    HasFDerivAt (fun x => f (m + gramCLM v x))
      (innerSL ℝ (∑ i, fderiv ℝ f (m + gramCLM v x) (unitVec i) • v i)) x := by
  have h1 : HasFDerivAt (fun x => m + gramCLM v x) (gramCLM v) x :=
    (gramCLM v).hasFDerivAt.const_add m
  have h2 := ((hf.differentiable one_ne_zero) (m + gramCLM v x)).hasFDerivAt.comp x h1
  rwa [dual_comp_gramCLM] at h2

lemma fderiv_unitVec_nonneg {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hfm : Monotone f)
    (y : ι → ℝ) (i : ι) : 0 ≤ fderiv ℝ f y (unitVec i) := by
  have hl : HasDerivAt (fun t : ℝ => y + t • unitVec i) (unitVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVec i)).const_add y
  have hd := ((hf.differentiable one_ne_zero) y).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by simp)
  refine hd.nonneg_of_monotone fun s t hst => hfm ?_
  exact add_le_add_right (smul_le_smul_of_nonneg_right hst (unitVec_nonneg i)) y

lemma norm_gradient_comp_gram_le {f : (ι → ℝ) → ℝ} {K : ℝ≥0} (hfL : LipschitzWith K f)
    (y : ι → ℝ) (v : ι → E) :
    ‖∑ i, fderiv ℝ f y (unitVec i) • v i‖ ≤ ∑ i, (K : ℝ) * ‖v i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖fderiv ℝ f y (unitVec i)‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVec i‖ := (fderiv ℝ f y).le_opNorm _
    _ ≤ K * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hfL) (norm_unitVec_le i)
        (norm_nonneg _) K.2
    _ = K := mul_one _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Pitt's inequality for smooth monotone functions** of a Gaussian vector with nonnegative
covariances. -/
theorem integral_mul_le_of_contDiff {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {f g : (ι → ℝ) → ℝ} {Cf Cg : ℝ} {Kf Kg : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfm : Monotone f) (hgm : Monotone g)
    (hfb : ∀ y, |f y| ≤ Cf) (hgb : ∀ y, |g y| ≤ Cg)
    (hfL : LipschitzWith Kf f) (hgL : LipschitzWith Kg g) :
    (∫ ω, f (X ω) ∂P) * (∫ ω, g (X ω) ∂P) ≤ ∫ ω, f (X ω) * g (X ω) ∂P := by
  obtain ⟨v, hv, hlaw⟩ := exists_gram_map_eq hX
  set γ := stdGaussian (EuclideanSpace ℝ ι)
  set m : ι → ℝ := fun i => ∫ ω, X ω i ∂P
  have htrans : ∀ h : (ι → ℝ) → ℝ, Continuous h →
      ∫ ω, h (X ω) ∂P = ∫ x, h (m + gramCLM v x) ∂γ := by
    intro h hc
    rw [← integral_map hX.aemeasurable hc.aestronglyMeasurable, hlaw,
      integral_map (by fun_prop) hc.aestronglyMeasurable]
  have hfc := hf.continuous
  have hgc := hg.continuous
  rw [htrans f hfc, htrans g hgc, htrans (fun y => f y * g y) (hfc.mul hgc)]
  have hYc : Continuous fun x : EuclideanSpace ℝ ι => m + gramCLM v x := by fun_prop
  refine integral_mul_le_integral_mul_stdGaussian
    (F' := fun x => ∑ i, fderiv ℝ f (m + gramCLM v x) (unitVec i) • v i)
    (G' := fun x => ∑ i, fderiv ℝ g (m + gramCLM v x) (unitVec i) • v i)
    (CF := Cf) (CG := Cg) (CF' := ∑ i, (Kf : ℝ) * ‖v i‖) (CG' := ∑ i, (Kg : ℝ) * ‖v i‖)
    (hasFDerivAt_comp_gram hf m v) (hasFDerivAt_comp_gram hg m v) ?_ ?_
    (fun x => hfb _) (fun x => hgb _)
    (fun x => norm_gradient_comp_gram_le hfL _ v) (fun x => norm_gradient_comp_gram_le hgL _ v)
    fun x y => ?_
  · exact continuous_finsetSum _ fun i _ =>
      (((hf.continuous_fderiv one_ne_zero).comp hYc).clm_apply continuous_const).smul
        continuous_const
  · exact continuous_finsetSum _ fun i _ =>
      (((hg.continuous_fderiv one_ne_zero).comp hYc).clm_apply continuous_const).smul
        continuous_const
  · rw [inner_sum_smul_sum_smul]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rw [hv]
    exact mul_nonneg (mul_nonneg (fderiv_unitVec_nonneg hf hfm _ i)
      (fderiv_unitVec_nonneg hg hgm _ j)) (hcov i j)

end Pitt

end LQGMetric
