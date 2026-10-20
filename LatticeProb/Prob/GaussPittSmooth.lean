/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/PittSmooth.lean.
-/
import LatticeProb.Prob.GaussPittCore
import LatticeProb.Prob.GaussPittVector

/-!
# Pitt's inequality for `C¹` Lipschitz monotone functions of a Gaussian vector

`LatticeProb.Pitt.integral_mul_le_of_contDiff`: for `X : Ω → (ι → ℝ)` with Gaussian law and
nonnegative covariances, and bounded, Lipschitz, monotone `C¹` functions `f, g`,
`E[f(X)] E[g(X)] ≤ E[f(X) g(X)]`.

The proof transfers the statement to the standard Gaussian measure of a Euclidean space through
the Gram representation `LatticeProb.Pitt.exists_gram_map_eq`, and then applies the smooth
positive-correlation theorem `LatticeProb.Pitt.integral_mul_le_integral_mul_stdGaussian`. The
gradients of the transferred functions have nonnegative coefficients on the Gram vectors, whose
pairwise inner products are the nonnegative covariances, so their inner products are nonnegative.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb

namespace Pitt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The composition `x ↦ f (m + gramCLM v x)` of a `C¹` function `f` with an affine Gram map has
Fréchet derivative the inner product with `∑ i, ∂ᵢf(m + gramCLM v x) • v i`. -/
lemma hasFDerivAt_comp_gram {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (m : ι → ℝ) (v : ι → E)
    (x : E) :
    HasFDerivAt (fun x => f (m + gramCLM v x))
      (innerSL ℝ (∑ i, fderiv ℝ f (m + gramCLM v x) (unitVec i) • v i)) x := by
  have h1 : HasFDerivAt (fun x => m + gramCLM v x) (gramCLM v) x :=
    (gramCLM v).hasFDerivAt.const_add m
  have h2 := ((hf.differentiable one_ne_zero) (m + gramCLM v x)).hasFDerivAt.comp x h1
  rwa [dual_comp_gramCLM] at h2

/-- A monotone `C¹` function has nonnegative derivative in each unit coordinate direction. -/
lemma fderiv_unitVec_nonneg {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hfm : Monotone f)
    (y : ι → ℝ) (i : ι) : 0 ≤ fderiv ℝ f y (unitVec i) := by
  have hl : HasDerivAt (fun t : ℝ => y + t • unitVec i) (unitVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVec i)).const_add y
  have hd := ((hf.differentiable one_ne_zero) y).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by simp)
  refine hd.nonneg_of_monotone fun s t hst => hfm ?_
  exact add_le_add_right (smul_le_smul_of_nonneg_right hst (unitVec_nonneg i)) y

/-- If `f` is `K`-Lipschitz, the vector `∑ i, ∂ᵢf(y) • v i` has norm at most `∑ i, K ‖v i‖`. -/
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
covariances: for bounded, Lipschitz, monotone `C¹` functions `f` and `g`,
`E[f(X)] E[g(X)] ≤ E[f(X) g(X)]`. -/
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

end LatticeProb

/-! ### Nonvacuity example -/

namespace LatticeProb.Pitt.PittSmoothExample

open MeasureTheory ProbabilityTheory Real

-- The hypotheses of `integral_mul_le_of_contDiff` hold for the Gaussian vector on `ℝ` whose
-- coordinates all equal the standard Gaussian variable, and for the monotone smooth functions
-- `y ↦ arctan (y 0)`: they are `C¹`, monotone, bounded by `π / 2`, and `1`-Lipschitz.
example :
    (∫ ω, Real.arctan ω ∂stdGaussian ℝ) * (∫ ω, Real.arctan ω ∂stdGaussian ℝ) ≤
      ∫ ω, Real.arctan ω * Real.arctan ω ∂stdGaussian ℝ := by
  have hX : HasGaussianLaw (fun ω : ℝ => fun _ : Fin 1 => ω) (stdGaussian ℝ) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℝ)).map_fun
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
  have hcov : ∀ _ _ : Fin 1, 0 ≤ cov[fun ω : ℝ => ω, fun ω : ℝ => ω; stdGaussian ℝ] :=
    fun _ _ => by
      rw [covariance_self measurable_id'.aemeasurable]
      exact variance_nonneg _ _
  have hLa : LipschitzWith 1 Real.arctan := by
    refine lipschitzWith_of_nnnorm_deriv_le
      ((Real.contDiff_arctan (n := 1)).differentiable (by norm_num)) fun x => ?_
    simp only [Real.deriv_arctan]
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 1 / (1 + x ^ 2) by positivity), NNReal.coe_one,
      div_le_one (show (0 : ℝ) < 1 + x ^ 2 by positivity)]
    linarith [sq_nonneg x]
  have hproj : LipschitzWith 1 (fun y : Fin 1 → ℝ => y 0) :=
    LipschitzWith.of_dist_le_mul fun y z => by simpa using dist_le_pi_dist y z 0
  exact integral_mul_le_of_contDiff (Cf := π / 2) (Cg := π / 2) hX hcov
    (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ 0))
    (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ 0))
    (fun y z h => Real.arctan_strictMono.monotone (h 0))
    (fun y z h => Real.arctan_strictMono.monotone (h 0))
    (fun y => abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)
    (fun y => abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)
    (hLa.comp hproj) (hLa.comp hproj)

end LatticeProb.Pitt.PittSmoothExample
