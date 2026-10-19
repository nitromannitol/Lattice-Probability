/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/ConcentrationCov.lean.
-/
import LatticeProb.Prob.GaussProductRotation
import LatticeProb.Prob.GaussSteinIBP
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian covariance identity for smooth bounded functions

For a finite-dimensional real inner product space `E` with a standard Gaussian measure
`stdGaussian E`, a function `f : E → ℝ` is `SmoothBdd f f' C C'` when it has gradient `f'` at
every point, `f'` is continuous, `|f| ≤ C` and `‖f'‖ ≤ C'`.

For two such functions `f` and `g`, `integral_mul_sub_eq_cov` gives the covariance identity

  `E[f g] - E[f] E[g] = ∫_0^{π/2} cos θ · E⟪∇f(sin θ u + cos θ v), ∇g(u)⟫ dθ`,

where `(u, v)` is distributed as the product of two copies of `stdGaussian E`. The proof writes
`g(u) - g(v)` as an integral along the rotation `(sin θ u + cos θ v, cos θ u - sin θ v)`, uses
that this rotation preserves the product Gaussian measure (`measurePreserving_rotPair`), and
applies Gaussian integration by parts in the second variable (`integral_inner_mul_stdGaussian`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace LatticeProb.GaussConc

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Fréchet derivative of a function with a gradient is the dual of the gradient. -/
lemma hasFDerivAt (hf : SmoothBdd f f' C C') (x : E) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ E (f' x)) x :=
  hasGradientAt_iff_hasFDerivAt.1 (hf.hasGrad x)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A function in `SmoothBdd f f' C C'` is continuous. -/
lemma continuous (hf : SmoothBdd f f' C C') : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf.hasFDerivAt x).continuousAt

omit [MeasurableSpace E] [BorelSpace E] in
/-- Derivative along a `C¹` curve. -/
lemma hasDerivAt_comp (hf : SmoothBdd f f' C C') {γ : ℝ → E} {γ' : E} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) : HasDerivAt (fun s => f (γ s)) ⟪f' (γ t), γ'⟫ t := by
  have := (hf.hasFDerivAt (γ t)).comp_hasDerivAt t hγ
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using this

omit [MeasurableSpace E] [BorelSpace E] in
/-- The bound `C` is nonnegative. -/
lemma C_nonneg (hf : SmoothBdd f f' C C') : 0 ≤ C := (abs_nonneg _).trans (hf.bdd 0)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient bound `C'` is nonnegative. -/
lemma C'_nonneg (hf : SmoothBdd f f' C C') : 0 ≤ C' := (norm_nonneg _).trans (hf.bdd' 0)

end SmoothBdd

variable {f g : E → ℝ} {f' g' : E → E} {C C' D D' : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The rotation curve `s ↦ sin s • x + cos s • y` has derivative `cos θ • x - sin θ • y`. -/
lemma hasDerivAt_rotCurve (x y : E) (θ : ℝ) :
    HasDerivAt (fun s => Real.sin s • x + Real.cos s • y)
      (Real.cos θ • x - Real.sin θ • y) θ := by
  have h := ((Real.hasDerivAt_sin θ).smul_const x).add ((Real.hasDerivAt_cos θ).smul_const y)
  rw [sub_eq_add_neg, ← neg_smul]
  exact h

omit [MeasurableSpace E] [BorelSpace E] in
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

/-- The integral of a function of the first coordinate under the product of two standard
Gaussian measures is its integral under one standard Gaussian measure. -/
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
    have hst := integral_inner_mul_stdGaussian
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

/-- **Gaussian covariance identity** (in the variable `α = sin θ`): for bounded `C¹` functions
with bounded continuous gradients, `E[fg] - E f E g = ∫_0^{π/2} cos θ · E⟪∇f(sin θ u + cos θ v),
∇g(u)⟫ dθ`, where `(u, v)` is distributed as the product of two standard Gaussian measures. -/
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

/-! ### Nonvacuity examples -/

namespace GaussSmoothBddExample

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

/-- The gradient of `x ↦ sin ⟪v, x⟫` on `EuclideanSpace ℝ (Fin 2)` is `cos ⟪v, x⟫ • v`. -/
theorem hasGradientAt_sin_inner (v x : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (fun y => Real.sin ⟪v, y⟫) (Real.cos ⟪v, x⟫ • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun y => Real.sin ⟪v, y⟫) (Real.cos ⟪v, x⟫ • innerSL ℝ v) x :=
    (Real.hasDerivAt_sin ⟪v, x⟫).comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt
  have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)) (Real.cos ⟪v, x⟫ • v) =
      Real.cos ⟪v, x⟫ • innerSL ℝ v := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply]
  rw [e]
  exact h

/-- `x ↦ sin ⟪v, x⟫` on `EuclideanSpace ℝ (Fin 2)` is a `SmoothBdd` function with bound `1`
and gradient bound `‖v‖`. -/
theorem smoothBdd_sin_inner (v : EuclideanSpace ℝ (Fin 2)) :
    SmoothBdd (fun y => Real.sin ⟪v, y⟫) (fun x => Real.cos ⟪v, x⟫ • v) 1 ‖v‖ where
  hasGrad x := hasGradientAt_sin_inner v x
  cont' := by fun_prop
  bdd x := Real.abs_sin_le_one _
  bdd' x := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg v) (Real.abs_cos_le_one _)

/-- **Covariance identity for `sin ⟪v, ·⟫`** on `EuclideanSpace ℝ (Fin 2)`: the covariance of
`sin ⟪v, X⟫` and itself under the standard Gaussian measure is given by the rotation integral
of `integral_mul_sub_eq_cov`. -/
theorem covariance_sin_inner (v : EuclideanSpace ℝ (Fin 2)) :
    ∫ x, Real.sin ⟪v, x⟫ * Real.sin ⟪v, x⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) -
        (∫ x, Real.sin ⟪v, x⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2)))) *
          (∫ x, Real.sin ⟪v, x⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2)))) =
      ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ *
        ∫ p, ⟪Real.cos ⟪v, Real.sin θ • p.1 + Real.cos θ • p.2⟫ • v, Real.cos ⟪v, p.1⟫ • v⟫
          ∂((stdGaussian (EuclideanSpace ℝ (Fin 2))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin 2)))) :=
  integral_mul_sub_eq_cov (smoothBdd_sin_inner v) (smoothBdd_sin_inner v)

end GaussSmoothBddExample

end LatticeProb.GaussConc
