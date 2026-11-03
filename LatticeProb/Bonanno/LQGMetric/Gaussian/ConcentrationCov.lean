/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.ConcentrationCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.SteinIBP
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.MGFAnalytic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Gaussian covariance identity and the sharp sub-Gaussian MGF bound (smooth bounded case)

Source: R. J. Adler, J. E. Taylor, *Random Fields and Geometry* (Springer 2007), §2.1:
Lemma 2.1.4 (the covariance identity `Cov(f(X), g(X)) = ∫₀¹ E⟨∇f(X), ∇g(αX + √(1-α²)Y)⟩ dα`)
and Lemma 2.1.5 (for `h` with Lipschitz constant `L` and `E h(X) = 0`, `E e^{t h(X)} ≤ e^{t²L²/2}`,
by the differential inequality `H'(t) ≤ t L² H(t)`).

We prove the covariance identity in the angular parametrisation `α = sin θ`
(`dα = cos θ dθ`), for bounded `C¹` functions with bounded continuous gradients:

  `∫ f g - ∫ f ∫ g = ∫_0^{π/2} cos θ · E_{(u,v)} ⟪∇f(sin θ u + cos θ v), ∇g(u)⟫ dθ`.

Deviation (proof of Lemma 2.1.4): Adler–Taylor verify the identity for characters
`e^{i⟨t,x⟩}` and conclude by an unwritten approximation argument; we instead prove it directly:
write `g(x) - g(y) = ∫_0^{π/2} ⟪∇g(x_θ), x'_θ⟫ dθ` along the rotation
`(x_θ, x'_θ) = (sin θ x + cos θ y, cos θ x - sin θ y)`, use that the rotation (an involution)
preserves the product of two standard Gaussians (`LQGDimension.MaxConc.measurePreserving_rotPair`)
and apply Gaussian integration by parts in the second variable
(`LQGDimension.SteinIBP.integral_inner_mul_stdGaussian`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace LQGMetric

namespace GaussConc

open LQGDimension.MaxConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `f` is a bounded `C¹` function with bounded continuous gradient `f'`
(`|f| ≤ C`, `‖f'‖ ≤ C'`). -/
structure SmoothBdd (f : E → ℝ) (f' : E → E) (C C' : ℝ) : Prop where
  hasGrad : ∀ x, HasGradientAt f (f' x) x
  cont' : Continuous f'
  bdd : ∀ x, |f x| ≤ C
  bdd' : ∀ x, ‖f' x‖ ≤ C'

namespace SmoothBdd

variable {f : E → ℝ} {f' : E → E} {C C' : ℝ}

lemma hasFDerivAt (hf : SmoothBdd f f' C C') (x : E) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ E (f' x)) x :=
  hasGradientAt_iff_hasFDerivAt.1 (hf.hasGrad x)

lemma continuous (hf : SmoothBdd f f' C C') : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf.hasFDerivAt x).continuousAt

/-- Derivative along a `C¹` curve. -/
lemma hasDerivAt_comp (hf : SmoothBdd f f' C C') {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) : HasDerivAt (fun s => f (γ s)) ⟪f' (γ t), γ'⟫ t := by
  have := (hf.hasFDerivAt (γ t)).comp_hasDerivAt t hγ
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this

lemma C_nonneg (hf : SmoothBdd f f' C C') : 0 ≤ C := (abs_nonneg _).trans (hf.bdd 0)

lemma C'_nonneg (hf : SmoothBdd f f' C C') : 0 ≤ C' := (norm_nonneg _).trans (hf.bdd' 0)

end SmoothBdd

variable {f g : E → ℝ} {f' g' : E → E} {C C' D D' : ℝ}

/-- The rotation curve has derivative `cos θ x - sin θ y`. -/
lemma hasDerivAt_rotCurve (x y : E) (θ : ℝ) :
    HasDerivAt (fun s => Real.sin s • x + Real.cos s • y)
      (Real.cos θ • x - Real.sin θ • y) θ := by
  have h := ((Real.hasDerivAt_sin θ).smul_const x).add ((Real.hasDerivAt_cos θ).smul_const y)
  rw [sub_eq_add_neg, ← neg_smul]
  exact h

/-- Pointwise fundamental theorem of calculus along the rotation. -/
lemma sub_eq_integral_rot (hg : SmoothBdd g g' D D') (p : E × E) :
    g p.1 - g p.2 = ∫ θ in (0 : ℝ)..(π / 2), ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫ := by
  have hcont : Continuous fun θ : ℝ => ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫ := by
    unfold rotPair
    exact (hg.cont'.comp (by fun_prop)).inner (by fun_prop)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π / 2)
    (f := fun s => g (Real.sin s • p.1 + Real.cos s • p.2))
    (f' := fun θ => ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫)
    (fun θ _ => hg.hasDerivAt_comp (hasDerivAt_rotCurve p.1 p.2 θ)) (hcont.intervalIntegrable _ _)
  rw [this]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The rotation `rotPair θ` is an involution. -/
lemma rotPair_rotPair (θ : ℝ) (p : E × E) : rotPair θ (rotPair θ p) = p := by
  obtain ⟨x, y⟩ := p
  have h := Real.sin_sq_add_cos_sq θ
  ext <;> simp only [rotPair] <;> match_scalars <;> first | linear_combination h | ring

/-- The integral of a function of the first coordinate under `μ.prod μ`. -/
lemma integral_prod_fst_stdGaussian {h : E → ℝ} (hh : Integrable h (stdGaussian E)) :
    ∫ p, h p.1 ∂((stdGaussian E).prod (stdGaussian E)) = ∫ x, h x ∂(stdGaussian E) := by
  rw [integral_prod _ (hh.comp_fst _)]
  simp

/-- **Rotation + Stein step.** For each angle `θ`,
`E[f(x) ⟪∇g(x_θ), x'_θ⟫] = cos θ · E[⟪∇f(sin θ u + cos θ v), ∇g(u)⟫]`. -/
lemma integral_rot_stein (hf : SmoothBdd f f' C C') (hg : SmoothBdd g g' D D') (θ : ℝ) :
    ∫ p, f p.1 * ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫
        ∂((stdGaussian E).prod (stdGaussian E)) =
      Real.cos θ * ∫ p, ⟪f' (Real.sin θ • p.1 + Real.cos θ • p.2), g' p.1⟫
        ∂((stdGaussian E).prod (stdGaussian E)) := by
  set μ := stdGaussian E
  set s := Real.sin θ
  set c := Real.cos θ
  have hfc := hf.continuous
  set Φ : E × E → ℝ := fun q => f (s • q.1 + c • q.2) * ⟪g' q.1, q.2⟫ with hΦ
  have hΦc : Continuous Φ :=
    (hfc.comp (by fun_prop)).mul ((hg.cont'.comp continuous_fst).inner continuous_snd)
  have hrot := measurePreserving_rotPair (E := E) θ
  have e1 : ∫ p, f p.1 * ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫ ∂(μ.prod μ) =
      ∫ p, Φ (rotPair θ p) ∂(μ.prod μ) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    have hp : s • (rotPair θ p).1 + c • (rotPair θ p).2 = p.1 :=
      congrArg Prod.fst (rotPair_rotPair θ p)
    simp only [Φ, hp]
  have hnorm : Integrable (fun q : E × E => ‖q.2‖) (μ.prod μ) :=
    (IsGaussian.integrable_id.norm).comp_snd μ
  have hΦint : Integrable Φ (μ.prod μ) := by
    refine Integrable.mono' (hnorm.const_mul (C * D')) hΦc.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_assoc]
    exact mul_le_mul (hf.bdd _) ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hg.bdd' _) (norm_nonneg _))) (abs_nonneg _) hf.C_nonneg
  rw [e1, ← integral_map hrot.measurable.aemeasurable hΦc.aestronglyMeasurable, hrot.map_eq,
    integral_prod _ hΦint]
  have hin : ∀ u : E, ∫ v, Φ (u, v) ∂μ =
      c * ∫ v, ⟪f' (s • u + c • v), g' u⟫ ∂μ := by
    intro u
    have hst := LQGDimension.SteinIBP.integral_inner_mul_stdGaussian
      (G := fun v => f (s • u + c • v)) (G' := fun v => c • f' (s • u + c • v))
      (C := C) (C' := |c| * C')
      (fun x e t => by
        have hγ : HasDerivAt (fun r : ℝ => s • u + c • (x + r • e)) (c • ((1 : ℝ) • e)) t :=
          ((((hasDerivAt_id t).smul_const e).const_add x).const_smul c).const_add (s • u)
        have := hf.hasDerivAt_comp hγ
        convert this using 1
        simp [real_inner_smul_left, real_inner_smul_right])
      (hfc.comp (by fun_prop)) ((hf.cont'.comp (by fun_prop)).const_smul c)
      (fun v => hf.bdd _)
      (fun v => by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hf.bdd' _) (g' u)
    have e : ∀ v, Φ (u, v) = ⟪g' u, v⟫ * f (s • u + c • v) := fun v => mul_comm _ _
    refine (integral_congr_ae (ae_of_all _ e)).trans ?_
    rw [hst]
    simp_rw [real_inner_smul_left]
    exact integral_const_mul _ _
  refine (integral_congr_ae (ae_of_all _ hin)).trans ?_
  rw [integral_const_mul, integral_prod]
  exact Integrable.of_bound ((hf.cont'.comp (by fun_prop)).inner
      (hg.cont'.comp continuous_fst)).aestronglyMeasurable (C' * D')
    (ae_of_all _ fun q => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hf.bdd' _) (hg.bdd' _) (norm_nonneg _) hf.C'_nonneg))

/-- **Gaussian covariance identity** (Adler–Taylor, Lemma 2.1.4, in the variable
`α = sin θ`): for bounded `C¹` functions with bounded continuous gradients,
`E[fg] - E f E g = ∫_0^{π/2} cos θ · E⟪∇f(sin θ u + cos θ v), ∇g(u)⟫ dθ`. -/
theorem integral_mul_sub_eq_cov (hf : SmoothBdd f f' C C') (hg : SmoothBdd g g' D D') :
    ∫ x, f x * g x ∂(stdGaussian E) -
        (∫ x, f x ∂(stdGaussian E)) * (∫ x, g x ∂(stdGaussian E)) =
      ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ * ∫ p, ⟪f' (Real.sin θ • p.1 + Real.cos θ • p.2), g' p.1⟫
        ∂((stdGaussian E).prod (stdGaussian E)) := by
  set μ := stdGaussian E
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hbdd : ∀ {h : E → ℝ} {K : ℝ}, Continuous h → (∀ x, |h x| ≤ K) → Integrable h μ :=
    fun hc hb => Integrable.of_bound hc.aestronglyMeasurable _ (ae_of_all _ fun x => hb x)
  have hfi : Integrable f μ := hbdd hfc hf.bdd
  have hgi : Integrable g μ := hbdd hgc hg.bdd
  have hfgi : Integrable (fun x => f x * g x) μ :=
    hbdd (hfc.mul hgc) (fun x => by
      rw [abs_mul]; exact mul_le_mul (hf.bdd x) (hg.bdd x) (abs_nonneg _) hf.C_nonneg)
  -- Step 1: the left side as an integral over `μ ⊗ μ`.
  have hstep1 : ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * (∫ x, g x ∂μ) =
      ∫ p, f p.1 * (g p.1 - g p.2) ∂(μ.prod μ) := by
    simp_rw [mul_sub]
    rw [integral_sub (hfgi.comp_fst μ) ((hfi.mul_prod hgi)),
      integral_prod_fst_stdGaussian hfgi, integral_prod_mul]
  -- Step 2: the fundamental theorem of calculus along the rotation.
  set F : ℝ → E × E → ℝ := fun θ p => f p.1 * ⟪g' (rotPair θ p).1, (rotPair θ p).2⟫ with hF
  have hstep2 : ∀ p : E × E, f p.1 * (g p.1 - g p.2) = ∫ θ in (0 : ℝ)..(π / 2), F θ p := by
    intro p
    rw [sub_eq_integral_rot hg p, ← intervalIntegral.integral_const_mul]
  -- Step 3: Fubini.
  have hFc : Continuous fun z : (E × E) × ℝ => F z.2 z.1 := by
    simp only [hF, rotPair]
    exact (hfc.comp (by fun_prop)).mul ((hg.cont'.comp (by fun_prop)).inner (by fun_prop))
  have hnorm : Integrable (fun q : E × E => ‖q.1‖ + ‖q.2‖) (μ.prod μ) :=
    ((IsGaussian.integrable_id.norm).comp_fst μ).add ((IsGaussian.integrable_id.norm).comp_snd μ)
  have hFint : Integrable (Function.uncurry fun p θ => F θ p)
      ((μ.prod μ).prod (volume.restrict (Ioc 0 (π / 2)))) := by
    refine Integrable.mono' ((hnorm.const_mul (C * D')).comp_fst _) hFc.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, hF, rotPair, Real.norm_eq_abs, abs_mul]
    rw [mul_assoc]
    refine mul_le_mul (hf.bdd _) ((abs_real_inner_le_norm _ _).trans ?_) (abs_nonneg _)
      hf.C_nonneg
    refine mul_le_mul (hg.bdd' _) ?_ (norm_nonneg _) hg.C'_nonneg
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
    · exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
    · exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _))
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  rw [hstep1]
  simp_rw [hstep2, intervalIntegral.integral_of_le hpi]
  rw [integral_integral_swap hFint]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  exact integral_rot_stein hf hg θ

end GaussConc

end LQGMetric
