/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/ConcentrationMollify.lean.
-/
import LatticeProb.Prob.GaussSmoothMGF
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Gaussian mollification and the sharp MGF bound for bounded Lipschitz functions

For a finite-dimensional real inner product space `E` and a bounded `L`-Lipschitz function
`F : E → ℝ`, convolve `F` with a normalised smooth bump `φ` (mathlib's `ContDiffBump.normed`).
The mollification `φ ⋆ F` is `C¹`, `L`-Lipschitz, and bounded by the same bound as `F`, and its
centred version has gradient bounded by `L`, so it satisfies the hypotheses of
`GaussConc.mgf_le_of_smoothBdd`.

The mollifiers `bumpSeq k` have outer radius `1 / (k + 1)`, which tends to zero, so the
mollifications converge pointwise to `F`. Each centred approximation satisfies the sharp
sub-Gaussian MGF bound, and the bound passes to the limit by dominated convergence. This gives
`E e^{t (F - E F)} ≤ e^{t² L² / 2}` under the standard Gaussian measure `stdGaussian E`, for
every real `t`, with no smoothness assumption on `F`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace NNReal ContDiff Convolution

namespace LatticeProb.GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Mollify

variable (φ : ContDiffBump (0 : E)) {F : E → ℝ} {L : ℝ≥0} {M : ℝ}

/-- The mollification `φ ⋆ F` of `F` by the normalised bump `φ`, with respect to an additive
Haar measure. -/
def mollify (F : E → ℝ) : E → ℝ :=
  φ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar] F

/-- The mollification at `x` is the integral `∫ t, φ t * F (x - t)` against the additive Haar
measure. -/
lemma mollify_apply (x : E) :
    mollify φ F x = ∫ t, φ.normed Measure.addHaar t * F (x - t) ∂Measure.addHaar := by
  simp [mollify, convolution_def]

/-- For continuous `F` bounded by `M`, the integrand `t ↦ φ t * F (x - t)` is integrable. -/
lemma integrable_normed_mul (hFc : Continuous F) (hM : ∀ x, |F x| ≤ M) (x : E) :
    Integrable (fun t => φ.normed Measure.addHaar t * F (x - t)) Measure.addHaar :=
  φ.integrable_normed.mul_bdd (hFc.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hM _)

/-- The mollification of a continuous function bounded by `M` is bounded by `M`. -/
lemma abs_mollify_le (_hFc : Continuous F) (hM : ∀ x, |F x| ≤ M) (x : E) :
    |mollify φ F x| ≤ M := by
  rw [mollify_apply, ← Real.norm_eq_abs]
  calc _ ≤ ∫ t, φ.normed Measure.addHaar t * M ∂Measure.addHaar :=
        norm_integral_le_of_norm_le (φ.integrable_normed.mul_const M) (ae_of_all _ fun t => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hM _) (φ.nonneg_normed t))
    _ = M := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The mollification of an `L`-Lipschitz function bounded by `M` is `L`-Lipschitz. -/
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

/-- The mollification of a continuous function is `C¹`. -/
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

/-- The mollifiers of radius `1 / (k + 1)`: the bump `bumpSeq k` has `rIn = 1 / (k + 2)` and
`rOut = 1 / (k + 1)`. -/
def bumpSeq (k : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((k : ℝ) + 2)
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The outer radii of the mollifiers `bumpSeq k` tend to zero. -/
lemma tendsto_bumpSeq_rOut : Tendsto (fun k => (bumpSeq (E := E) k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Sharp MGF bound for bounded Lipschitz functions.** If `F` is `L`-Lipschitz and bounded by
`M`, then under the standard Gaussian measure `E e^{t (F - E F)} ≤ e^{t² L² / 2}` for every real
`t`. -/
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

/-! ### Nonvacuity examples -/

namespace GaussMollifyExample

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

/-- The function `x ↦ sin ⟪v, x⟫` is Lipschitz with constant `‖v‖`, since `sin` is
1-Lipschitz and `⟪v, ·⟫` is `‖v‖`-Lipschitz. -/
theorem lipschitzWith_sin_inner (v : EuclideanSpace ℝ (Fin 2)) :
    LipschitzWith ‖v‖₊ (fun x => Real.sin ⟪v, x⟫) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h : |⟪v, x⟫ - ⟪v, y⟫| ≤ ‖v‖ * dist x y := by
    rw [← inner_sub_right, dist_eq_norm]
    exact abs_real_inner_le_norm _ _
  rw [Real.dist_eq, coe_nnnorm]
  exact (Real.abs_sin_sub_sin_le _ _).trans h

/-- **Sharp MGF bound for `sin ⟪v, ·⟫` from `mgf_le_of_lipschitz_bdd`.** The function
`x ↦ sin ⟪v, x⟫` is `‖v‖`-Lipschitz, bounded by `1`, and has Gaussian mean zero, so
`E e^{t sin ⟪v, X⟫} ≤ e^{t² ‖v‖² / 2}` for all real `t`. -/
theorem mgf_sin_inner_le (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mgf (fun x => Real.sin ⟪v, x⟫) (stdGaussian (EuclideanSpace ℝ (Fin 2))) t ≤
      exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  have h := mgf_le_of_lipschitz_bdd (M := 1) (lipschitzWith_sin_inner v)
    (fun _ => Real.abs_sin_le_one _) t
  simp only [GaussSmoothMGFExample.integral_sin_inner_stdGaussian, sub_zero, coe_nnnorm] at h
  exact h

/-- **Mollification of `sin ⟪v, ·⟫`.** For the concrete mollifier `bumpSeq 0` on
`EuclideanSpace ℝ (Fin 2)`, the mollification of `x ↦ sin ⟪v, x⟫` is `‖v‖`-Lipschitz. -/
theorem lipschitzWith_mollify_sin_inner (v : EuclideanSpace ℝ (Fin 2)) :
    LipschitzWith ‖v‖₊
      (mollify (bumpSeq (E := EuclideanSpace ℝ (Fin 2)) 0) (fun x => Real.sin ⟪v, x⟫)) :=
  lipschitzWith_mollify (bumpSeq 0) (lipschitzWith_sin_inner v) (fun _ => Real.abs_sin_le_one _)

end GaussMollifyExample

end LatticeProb.GaussConc
