/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.ConcentrationMollify at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sharp sub-Gaussian MGF bound for bounded Lipschitz functions

Source: R. J. Adler, J. E. Taylor, *Random Fields and Geometry* (Springer 2007), proof of
Lemma 2.1.6 (p. 55): "to remove the `C²` assumption, take a sequence of `C²` approximations to
`f` each one of which has Lipschitz coefficient no greater than `σ`" and pass to the limit.

We take the approximations to be the convolutions `φₖ ⋆ F` with normalised smooth bumps `φₖ`
of radius `1/(k+1)` (mathlib's `ContDiffBump.normed`): they are smooth, `L`-Lipschitz and bounded
by the bound of `F`, and converge pointwise to `F`; the MGF bound of
`GaussConc.mgf_le_of_smoothBdd` passes to the limit by dominated convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace NNReal ContDiff Convolution

namespace LQGMetric

namespace GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Mollify

variable (φ : ContDiffBump (0 : E)) {F : E → ℝ} {L : ℝ≥0} {M : ℝ}

/-- The mollification `φ ⋆ F` (with respect to an additive Haar measure). -/
def mollify (F : E → ℝ) : E → ℝ :=
  φ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] F

lemma mollify_apply (x : E) :
    mollify φ F x = ∫ t, φ.normed Measure.addHaar t * F (x - t) ∂Measure.addHaar := by
  simp [mollify, convolution_def]

lemma integrable_normed_mul (hFc : Continuous F) (hM : ∀ x, |F x| ≤ M) (x : E) :
    Integrable (fun t => φ.normed Measure.addHaar t * F (x - t)) Measure.addHaar :=
  φ.integrable_normed.mul_bdd (hFc.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hM _)

lemma abs_mollify_le (hFc : Continuous F) (hM : ∀ x, |F x| ≤ M) (x : E) :
    |mollify φ F x| ≤ M := by
  rw [mollify_apply, ← Real.norm_eq_abs]
  calc _ ≤ ∫ t, φ.normed Measure.addHaar t * M ∂Measure.addHaar :=
        norm_integral_le_of_norm_le (φ.integrable_normed.mul_const M) (ae_of_all _ fun t => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hM _) (φ.nonneg_normed t))
    _ = M := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma lipschitzWith_mollify (hF : LipschitzWith L F) (hM : ∀ x, |F x| ≤ M) :
    LipschitzWith L (mollify φ F) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hFc := hF.continuous
  rw [Real.dist_eq, mollify_apply, mollify_apply,
    ← integral_sub (integrable_normed_mul φ hFc hM x) (integrable_normed_mul φ hFc hM y),
    ← Real.norm_eq_abs]
  calc _ ≤ ∫ t, φ.normed Measure.addHaar t * (L * dist x y) ∂Measure.addHaar :=
        norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (ae_of_all _ fun t => by
          rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (φ.nonneg_normed t)]
          refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
          have := hF.dist_le_mul (x - t) (y - t)
          rwa [Real.dist_eq, dist_sub_right] at this)
    _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

lemma contDiff_mollify (hFc : Continuous F) : ContDiff ℝ 1 (mollify φ F) := by
  have := φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (μ := Measure.addHaar) (n := 1)) (hFc.locallyIntegrable (μ := Measure.addHaar))
  exact_mod_cast this

/-- The centred mollification is a bounded `C¹` function with gradient bounded by `L`. -/
lemma smoothBdd_mollify_sub (hF : LipschitzWith L F) (hM : ∀ x, |F x| ≤ M) (c : ℝ) :
    SmoothBdd (fun x => mollify φ F x - c) (gradient (mollify φ F)) (M + |c|) L where
  hasGrad x := by
    have hd : DifferentiableAt ℝ (mollify φ F) x :=
      ((contDiff_mollify φ hF.continuous).differentiable one_ne_zero) x
    exact hasGradientAt_iff_hasFDerivAt.2
      ((hasGradientAt_iff_hasFDerivAt.1 hd.hasGradientAt).sub_const c)
  cont' := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((contDiff_mollify φ hF.continuous).continuous_fderiv one_ne_zero)
  bdd x := (abs_sub _ _).trans (by gcongr; exact abs_mollify_le φ hF.continuous hM x)
  bdd' x := by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_mollify φ hF hM)

end Mollify

/-- The mollifiers of radius `1/(k+1)`. -/
def bumpSeq (k : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((k : ℝ) + 2)
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

lemma tendsto_bumpSeq_rOut : Tendsto (fun k => (bumpSeq (E := E) k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Sharp MGF bound for bounded Lipschitz functions.** -/
theorem mgf_le_of_lipschitz_bdd {F : E → ℝ} {L : ℝ≥0} {M : ℝ} (hF : LipschitzWith L F)
    (hM : ∀ x, |F x| ≤ M) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂(stdGaussian E)) (stdGaussian E) t ≤
      exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by
  set μ := stdGaussian E
  have hFc := hF.continuous
  set Fk : ℕ → E → ℝ := fun k => mollify (bumpSeq k) F
  set c : ℕ → ℝ := fun k => ∫ y, Fk k y ∂μ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hFkc : ∀ k, Continuous (Fk k) := fun k => (contDiff_mollify _ hFc).continuous
  have hFkb : ∀ k x, |Fk k x| ≤ M := fun k x => abs_mollify_le _ hFc hM x
  have hlim : ∀ x, Tendsto (fun k => Fk k x) atTop (𝓝 (F x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := Measure.addHaar)
      tendsto_bumpSeq_rOut hFc x
  have hc : Tendsto c atTop (𝓝 (∫ y, F y ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun k => (hFkc k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hFkb k x)
      (ae_of_all _ hlim)
  have hcb : ∀ k, |c k| ≤ M := fun k => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const M)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hFkb k x)).trans ?_
    simp
  have hk : ∀ k, mgf (fun x => Fk k x - c k) μ t ≤ exp (t ^ 2 * (L : ℝ) ^ 2 / 2) := by
    intro k
    refine mgf_le_of_smoothBdd (smoothBdd_mollify_sub (bumpSeq k) hF hM (c k)) ?_ t
    rw [integral_sub (Integrable.of_bound (hFkc k).aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hFkb k x)) (integrable_const _),
      integral_const]
    simp [c, μ]
  refine le_of_tendsto' (f := fun k => mgf (fun x => Fk k x - c k) μ t) (x := atTop) ?_ hk
  refine tendsto_integral_of_dominated_convergence (fun _ => exp (|t| * (M + M)))
    (fun k => ((continuous_const.mul ((hFkc k).sub continuous_const)).rexp).aestronglyMeasurable)
    (integrable_const _) (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hFkb k x) (hcb k)))
      (abs_nonneg _)
  · exact (((hlim x).sub hc).const_mul t).rexp


end GaussConc

end LQGMetric
