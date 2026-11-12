/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.PittLipschitz at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pitt's inequality for Lipschitz monotone functions

`LQGMetric.Pitt.integral_mul_le_of_lipschitz`: the smooth case
`LQGMetric.Pitt.integral_mul_le_of_contDiff` extends to bounded, Lipschitz, monotone `f, g`.
Standard approximation: `f` is replaced by its convolution with a normalized smooth bump of
radius `→ 0`, which is smooth, monotone, bounded by the same constant and Lipschitz with the same
constant, and converges pointwise to `f`; then dominated convergence.
(Pitt 1982 proves the identity for smooth functions; the reduction to general monotone functions
by approximation is the standard one, cf. Esary–Proschan–Walkup 1967, and our arrangement of it
is an own elementary argument.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal Convolution

namespace LQGMetric

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- The bump of radii `1/(n+2) < 2/(n+2)`. -/
def pittBump (n : ℕ) : ContDiffBump (0 : ι → ℝ) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < n + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right this]; norm_num

omit [Fintype ι] in
lemma tendsto_pittBump_rOut : Tendsto (fun n => (pittBump (ι := ι) n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa using h.const_div_atTop 2

/-- The mollification `φₙ ⋆ f`. -/
def pittMollify (n : ℕ) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  ((pittBump n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

lemma pittMollify_apply (n : ℕ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    pittMollify n f x = ∫ t, (pittBump n).normed volume t * f (x - t) := by
  simp [pittMollify, convolution_def]

section Props

variable {f : (ι → ℝ) → ℝ} {C : ℝ} {K : ℝ≥0}

lemma integrable_bump_mul (n : ℕ) (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ C) (x : ι → ℝ) :
    Integrable (fun t => (pittBump n).normed volume t * f (x - t)) volume :=
  (pittBump n).integrable_normed.mul_bdd
    (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hfb (x - t))

lemma contDiff_pittMollify (n : ℕ) (hfc : Continuous f) : ContDiff ℝ 1 (pittMollify n f) :=
  (pittBump n).hasCompactSupport_normed.contDiff_convolution_left _ (pittBump n).contDiff_normed
    hfc.locallyIntegrable

lemma monotone_pittMollify (n : ℕ) (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ C)
    (hfm : Monotone f) : Monotone (pittMollify n f) := fun x y hxy => by
  rw [pittMollify_apply, pittMollify_apply]
  refine integral_mono (integrable_bump_mul n hfc hfb x) (integrable_bump_mul n hfc hfb y)
    fun t => ?_
  exact mul_le_mul_of_nonneg_left (hfm (sub_le_sub_right hxy t)) ((pittBump n).nonneg_normed t)

lemma abs_pittMollify_le (n : ℕ) (hfb : ∀ y, |f y| ≤ C) (x : ι → ℝ) :
    |pittMollify n f x| ≤ C := by
  rw [pittMollify_apply, ← Real.norm_eq_abs]
  calc ‖∫ t, (pittBump n).normed volume t * f (x - t)‖
      ≤ ∫ t, (pittBump n).normed volume t * C :=
        norm_integral_le_of_norm_le ((pittBump n).integrable_normed.mul_const C)
          (ae_of_all _ fun t => by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((pittBump n).nonneg_normed t),
              Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hfb _) ((pittBump n).nonneg_normed t))
    _ = C := by rw [integral_mul_const, (pittBump n).integral_normed, one_mul]

lemma lipschitz_pittMollify (n : ℕ) (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ C)
    (hfL : LipschitzWith K f) : LipschitzWith K (pittMollify n f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, pittMollify_apply, pittMollify_apply,
    ← integral_sub (integrable_bump_mul n hfc hfb x) (integrable_bump_mul n hfc hfb y),
    ← Real.norm_eq_abs]
  calc ‖∫ t, ((pittBump n).normed volume t * f (x - t) -
          (pittBump n).normed volume t * f (y - t))‖
      ≤ ∫ t, (pittBump n).normed volume t * (K * dist x y) :=
        norm_integral_le_of_norm_le ((pittBump n).integrable_normed.mul_const _)
          (ae_of_all _ fun t => by
            rw [← mul_sub, norm_mul, Real.norm_eq_abs,
              abs_of_nonneg ((pittBump n).nonneg_normed t), ← dist_eq_norm]
            refine mul_le_mul_of_nonneg_left ?_ ((pittBump n).nonneg_normed t)
            calc dist (f (x - t)) (f (y - t)) ≤ K * dist (x - t) (y - t) := hfL.dist_le_mul _ _
              _ = K * dist x y := by rw [dist_sub_right])
    _ = K * dist x y := by rw [integral_mul_const, (pittBump n).integral_normed, one_mul]

lemma tendsto_pittMollify (hfc : Continuous f) (x : ι → ℝ) :
    Tendsto (fun n => pittMollify n f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous tendsto_pittBump_rOut hfc x

end Props

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [Fintype ι] in
lemma tendsto_integral_comp_of_bdd {X : Ω → ι → ℝ} (hX : AEMeasurable X P) [IsFiniteMeasure P]
    {h : ℕ → (ι → ℝ) → ℝ} {h₀ : (ι → ℝ) → ℝ} {C : ℝ} (hc : ∀ n, Measurable (h n))
    (hb : ∀ n y, |h n y| ≤ C) (hlim : ∀ y, Tendsto (fun n => h n y) atTop (𝓝 (h₀ y))) :
    Tendsto (fun n => ∫ ω, h n (X ω) ∂P) atTop (𝓝 (∫ ω, h₀ (X ω) ∂P)) :=
  tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => ((hc n).comp_aemeasurable hX).aestronglyMeasurable) (integrable_const C)
    (fun n => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb n _)
    (ae_of_all _ fun ω => hlim _)

variable [DecidableEq ι]

/-- **Pitt's inequality for Lipschitz monotone functions.** -/
theorem integral_mul_le_of_lipschitz {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {f g : (ι → ℝ) → ℝ} {Cf Cg : ℝ} {Kf Kg : ℝ≥0}
    (hfm : Monotone f) (hgm : Monotone g)
    (hfb : ∀ y, |f y| ≤ Cf) (hgb : ∀ y, |g y| ≤ Cg)
    (hfL : LipschitzWith Kf f) (hgL : LipschitzWith Kg g) :
    (∫ ω, f (X ω) ∂P) * (∫ ω, g (X ω) ∂P) ≤ ∫ ω, f (X ω) * g (X ω) ∂P := by
  have := hX.isProbabilityMeasure
  have hfc := hfL.continuous
  have hgc := hgL.continuous
  have hmeas := hX.aemeasurable
  have hn : ∀ n, (∫ ω, pittMollify n f (X ω) ∂P) * (∫ ω, pittMollify n g (X ω) ∂P) ≤
      ∫ ω, pittMollify n f (X ω) * pittMollify n g (X ω) ∂P := fun n =>
    integral_mul_le_of_contDiff hX hcov (contDiff_pittMollify n hfc) (contDiff_pittMollify n hgc)
      (monotone_pittMollify n hfc hfb hfm) (monotone_pittMollify n hgc hgb hgm)
      (abs_pittMollify_le n hfb) (abs_pittMollify_le n hgb)
      (lipschitz_pittMollify n hfc hfb hfL) (lipschitz_pittMollify n hgc hgb hgL)
  have hF := tendsto_integral_comp_of_bdd hmeas
    (fun n => (contDiff_pittMollify n hfc).continuous.measurable)
    (abs_pittMollify_le · hfb) (tendsto_pittMollify hfc)
  have hG := tendsto_integral_comp_of_bdd hmeas
    (fun n => (contDiff_pittMollify n hgc).continuous.measurable)
    (abs_pittMollify_le · hgb) (tendsto_pittMollify hgc)
  have hFG := tendsto_integral_comp_of_bdd hmeas (h := fun n y => pittMollify n f y *
      pittMollify n g y) (h₀ := fun y => f y * g y) (C := Cf * Cg)
    (fun n => ((contDiff_pittMollify n hfc).continuous.mul
      (contDiff_pittMollify n hgc).continuous).measurable)
    (fun n y => by
      rw [abs_mul]
      exact mul_le_mul (abs_pittMollify_le n hfb y) (abs_pittMollify_le n hgb y)
        (abs_nonneg _) ((abs_nonneg _).trans (hfb y)))
    (fun y => (tendsto_pittMollify hfc y).mul (tendsto_pittMollify hgc y))
  exact le_of_tendsto_of_tendsto' (hF.mul hG) hFG hn

end Pitt

end LQGMetric
