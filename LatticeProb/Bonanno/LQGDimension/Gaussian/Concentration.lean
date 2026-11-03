/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.Concentration at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.GaussianConcentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality

/-!
# Gaussian concentration for finite maxima (Maurey–Pisier)

We prove `Blueprint.MaxConcentration`: for `x ∼ stdGaussian E`,
`M(x) = max_{i ∈ F} (⟪v i, x⟫ + b i)` with `‖v i‖ ≤ σ` on `F`, and every real `t`,
`E exp (t (M - E M)) ≤ exp (π² t² σ² / 8)`.

Proof (Maurey–Pisier interpolation).

1. Replace `M` by the smooth maximum `G = smoothMax F β (⟪v i, ·⟫ + b i)`, whose gradient
   `gradG x = ∑ p_i(x) v i` is a convex combination of the `v i` (so `‖gradG‖ ≤ σ`), and let
   `β → ∞` at the end (`M ≤ G ≤ M + log |F| / β`).
2. On `E × E` with the product measure `μ₂ = stdGaussian E ⊗ stdGaussian E`, write
   `G x - G y = ∫_0^{π/2} ⟪gradG (x_θ), x'_θ⟫ dθ` with `x_θ = sin θ x + cos θ y`,
   `x'_θ = cos θ x - sin θ y`.
3. Jensen in `θ` (via the tangent line `e^u ≥ e^a (1 + u - a)`):
   `exp (t (G x - G y)) ≤ (2/π) ∫_0^{π/2} exp ((π/2) t ⟪gradG x_θ, x'_θ⟫) dθ`.
4. `(x, y) ↦ (x_θ, x'_θ)` preserves `μ₂` (`measurePreserving_rotPair`: through
   `WithLp 2 (E × E)`, where it is a linear isometry and `stdGaussian` is rotation invariant),
   so by Tonelli the expectation of the right side is `E_x E_y exp ((π/2) t ⟪gradG x, y⟫)
   = E_x exp (π² t² ‖gradG x‖² / 8) ≤ exp (π² t² σ² / 8)`.
5. Jensen in `y`: `E_x exp (t (G x - E G)) ≤ E_{x,y} exp (t (G x - G y))`.

All the exponential moments are handled as lower integrals (`∫⁻`), so no integrability side
conditions are needed for Tonelli; integrability of `exp (t (M - E M))` is a consequence.

We also export the sub-Gaussian tail bounds `maxConcentration_tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real WithLp
open scoped RealInnerProductSpace ENNReal

namespace LQGDimension

namespace MaxConc

open SudakovFernique

/-! ### Rotation invariance of the product of two standard Gaussians -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rotation `(x, y) ↦ (sin θ • x + cos θ • y, cos θ • x - sin θ • y)` of `E × E`. -/
def rotPair (θ : ℝ) (p : E × E) : E × E :=
  (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2)

lemma continuous_rotPair (θ : ℝ) : Continuous (rotPair (E := E) θ) := by
  unfold rotPair
  fun_prop

/-- The rotation as a linear map of `E × E`. -/
def rotPairLin (θ : ℝ) : E × E →ₗ[ℝ] E × E :=
  (Real.sin θ • LinearMap.fst ℝ E E + Real.cos θ • LinearMap.snd ℝ E E).prod
    (Real.cos θ • LinearMap.fst ℝ E E - Real.sin θ • LinearMap.snd ℝ E E)

/-- The rotation as a linear map of `WithLp 2 (E × E)`. -/
def rotLin (θ : ℝ) : WithLp 2 (E × E) →ₗ[ℝ] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap ∘ₗ rotPairLin θ ∘ₗ
    (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

lemma rotLin_apply (θ : ℝ) (z : WithLp 2 (E × E)) : rotLin θ z = toLp 2 (rotPair θ (ofLp z)) :=
  rfl

lemma inner_rotLin (θ : ℝ) (z w : WithLp 2 (E × E)) :
    ⟪rotLin θ z, rotLin θ w⟫ = ⟪z, w⟫ := by
  simp only [rotLin_apply, WithLp.prod_inner_apply, rotPair]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination (⟪(ofLp z).1, (ofLp w).1⟫ + ⟪(ofLp z).2, (ofLp w).2⟫) * h

variable [FiniteDimensional ℝ E]

/-- The rotation as a linear isometry equivalence of `WithLp 2 (E × E)`. -/
def rotLI (θ : ℝ) : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) :=
  ((rotLin θ).isometryOfInner (inner_rotLin θ)).toLinearIsometryEquiv rfl

lemma rotLI_apply (θ : ℝ) (z : WithLp 2 (E × E)) : rotLI θ z = toLp 2 (rotPair θ (ofLp z)) :=
  rfl

variable [MeasurableSpace E] [BorelSpace E]

/-- The product of two standard Gaussian measures, seen in `WithLp 2 (E × E)`, is the standard
Gaussian measure there. -/
theorem map_toLp_prod_stdGaussian :
    ((stdGaussian E).prod (stdGaussian E)).map (toLp 2) = stdGaussian (WithLp 2 (E × E)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  have h := WithLp.prod_norm_sq_eq_of_L2 t
  have h' : ((‖t‖ : ℂ)) ^ 2 = (‖(ofLp t).1‖ : ℂ) ^ 2 + (‖(ofLp t).2‖ : ℂ) ^ 2 := by
    exact_mod_cast h
  rw [h']
  ring

theorem prod_stdGaussian_eq_map_ofLp :
    (stdGaussian E).prod (stdGaussian E) = (stdGaussian (WithLp 2 (E × E))).map ofLp := by
  rw [← map_toLp_prod_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (ofLp ∘ toLp 2 : E × E → E × E) = id := rfl
  rw [this, Measure.map_id]

/-- **Rotation invariance**: `(x, y) ↦ (sin θ x + cos θ y, cos θ x - sin θ y)` preserves the
product of two standard Gaussian measures. -/
theorem measurePreserving_rotPair (θ : ℝ) :
    MeasurePreserving (rotPair θ) ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E)) := by
  refine ⟨(continuous_rotPair θ).measurable, ?_⟩
  rw [prod_stdGaussian_eq_map_ofLp, Measure.map_map (continuous_rotPair θ).measurable
    (by fun_prop)]
  have h : (rotPair θ ∘ ofLp : WithLp 2 (E × E) → E × E) = ofLp ∘ (rotLI (E := E) θ) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (rotLI (E := E) θ).continuous.measurable,
    stdGaussian_map]

end Rotation

/-! ### Two elementary Jensen-type inequalities -/

section Jensen

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for an integrable real function. -/
lemma ofReal_integral_le_lintegral_ofReal' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h1 : ∫ x, f x ∂μ ≤ ∫ x, max (f x) 0 ∂μ :=
    integral_mono hf hf.pos_part fun x => le_max_left _ _
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part (ae_of_all _ fun x => le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        congr 1
        funext x
        rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

/-- Jensen's inequality for `exp` and the uniform average on `[0, L]`:
`exp (∫_0^L f) ≤ L⁻¹ ∫_0^L exp (L f)`. -/
lemma exp_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 < L) :
    Real.exp (∫ θ in (0 : ℝ)..L, f θ) ≤ L⁻¹ * ∫ θ in (0 : ℝ)..L, Real.exp (L * f θ) := by
  set a := ∫ θ in (0 : ℝ)..L, f θ with ha
  have hpt : ∀ θ, Real.exp a * (1 - a) + Real.exp a * L * f θ ≤ Real.exp (L * f θ) := by
    intro θ
    have h1 := Real.add_one_le_exp (L * f θ - a)
    have h2 : Real.exp (L * f θ) = Real.exp a * Real.exp (L * f θ - a) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    nlinarith
  have hint : ∫ θ in (0 : ℝ)..L, (Real.exp a * (1 - a) + Real.exp a * L * f θ) =
      L * Real.exp a := by
    have hc : IntervalIntegrable (fun _ => Real.exp a * (1 - a)) volume 0 L :=
      intervalIntegrable_const
    rw [intervalIntegral.integral_add hc
      ((hf.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, ← ha]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hc : IntervalIntegrable (fun _ => Real.exp a * (1 - a)) volume 0 L :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hL.le
    (hc.add ((hf.intervalIntegrable _ _).const_mul _))
    ((Real.continuous_exp.comp (continuous_const.mul hf)).intervalIntegrable _ _)
    (fun θ _ => hpt θ)
  rw [hint] at hmono
  rw [le_inv_mul_iff₀ hL]
  exact hmono

end Jensen

/-! ### The smooth maximum of the affine family -/

section Smooth

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Finset ι} {β : ℝ} {v : ι → E} {b : ι → ℝ}

/-- The affine family `(⟪v i, x⟫ + b i)_i`. -/
def affZ (v : ι → E) (b : ι → ℝ) (x : E) (i : ι) : ℝ := ⟪v i, x⟫ + b i

/-- The smooth maximum `G(x) = smoothMax F β (⟪v i, x⟫ + b i)_i`. -/
def smG (F : Finset ι) (β : ℝ) (v : ι → E) (b : ι → ℝ) (x : E) : ℝ :=
  smoothMax F β (affZ v b x)

/-- The gradient `∑_i p_i(x) • v i` of `smG`, a convex combination of the `v i`. -/
def gradG (F : Finset ι) (β : ℝ) (v : ι → E) (b : ι → ℝ) (x : E) : E :=
  ∑ i ∈ F, softmax F β (affZ v b x) i • v i

/-- The derivative of `θ ↦ G(sin θ x + cos θ y)`: `⟪gradG (x_θ), x'_θ⟫` where
`(x_θ, x'_θ) = rotPair θ (x, y)`. -/
def curveD (F : Finset ι) (β : ℝ) (v : ι → E) (b : ι → ℝ) (θ : ℝ) (p : E × E) : ℝ :=
  ⟪gradG F β v b (rotPair θ p).1, (rotPair θ p).2⟫

lemma continuous_affZ (v : ι → E) (b : ι → ℝ) (i : ι) : Continuous fun x => affZ v b x i :=
  (continuous_const.inner continuous_id).add continuous_const

lemma continuous_smG (hF : F.Nonempty) : Continuous (smG F β v b) :=
  continuous_smoothMax hF β (continuous_affZ v b)

lemma continuous_gradG (hF : F.Nonempty) : Continuous (gradG F β v b) :=
  continuous_finsetSum _ fun i _ =>
    (continuous_softmax hF β (continuous_affZ v b) i).smul continuous_const

lemma continuous_curveD_swap (hF : F.Nonempty) :
    Continuous fun q : (E × E) × ℝ => curveD F β v b q.2 q.1 := by
  unfold curveD rotPair
  exact ((continuous_gradG hF).comp (by fun_prop)).inner (by fun_prop)

lemma continuous_curveD_theta (hF : F.Nonempty) (p : E × E) :
    Continuous fun θ => curveD F β v b θ p := by
  unfold curveD rotPair
  exact ((continuous_gradG hF).comp (by fun_prop)).inner (by fun_prop)

lemma norm_gradG_le (hF : F.Nonempty) {σ : ℝ} (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (x : E) :
    ‖gradG F β v b x‖ ≤ σ := by
  unfold gradG
  calc ‖∑ i ∈ F, softmax F β (affZ v b x) i • v i‖
      ≤ ∑ i ∈ F, ‖softmax F β (affZ v b x) i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, softmax F β (affZ v b x) i * σ := Finset.sum_le_sum fun i hi => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (softmax_nonneg _ _ _ _)]
        exact mul_le_mul_of_nonneg_left (hv i hi) (softmax_nonneg _ _ _ _)
    _ = σ := by rw [← Finset.sum_mul, sum_softmax hF, one_mul]

lemma inner_gradG (x w : E) :
    ⟪gradG F β v b x, w⟫ = ∑ i ∈ F, softmax F β (affZ v b x) i * ⟪v i, w⟫ := by
  simp only [gradG, sum_inner, real_inner_smul_left]

/-- Derivative of `G` along the rotation curve `θ ↦ sin θ x + cos θ y`. -/
lemma hasDerivAt_smG_curve (hF : F.Nonempty) (hβ : β ≠ 0) (x y : E) (θ : ℝ) :
    HasDerivAt (fun s => smG F β v b (Real.sin s • x + Real.cos s • y))
      ⟪gradG F β v b (Real.sin θ • x + Real.cos θ • y), Real.cos θ • x - Real.sin θ • y⟫ θ := by
  have h := hasDerivAt_smoothMax hF hβ
    (γ := fun s => affZ v b (Real.sin s • x + Real.cos s • y))
    (γ' := fun i => ⟪v i, Real.cos θ • x - Real.sin θ • y⟫) (t := θ) (fun i => ?_)
  · rw [inner_gradG]
    exact h
  · have e : (fun s => affZ v b (Real.sin s • x + Real.cos s • y) i) =
        fun s => Real.sin s * ⟪v i, x⟫ + Real.cos s * ⟪v i, y⟫ + b i := by
      funext s
      simp only [affZ, inner_add_right, real_inner_smul_right]
    rw [e]
    refine ((((Real.hasDerivAt_sin θ).mul_const _).add
      ((Real.hasDerivAt_cos θ).mul_const _)).add_const _).congr_deriv ?_
    simp only [inner_sub_right, real_inner_smul_right]
    ring

/-- `G x - G y = ∫_0^{π/2} ⟪gradG x_θ, x'_θ⟫ dθ`. -/
lemma smG_sub_eq_integral (hF : F.Nonempty) (hβ : β ≠ 0) (p : E × E) :
    smG F β v b p.1 - smG F β v b p.2 = ∫ θ in (0 : ℝ)..(π / 2), curveD F β v b θ p := by
  have hc : Continuous fun θ => curveD F β v b θ p := continuous_curveD_theta hF p
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => smG F β v b (Real.sin s • p.1 + Real.cos s • p.2))
    (f' := fun θ => curveD F β v b θ p)
    (fun θ _ => hasDerivAt_smG_curve hF hβ p.1 p.2 θ) (hc.intervalIntegrable _ _)]
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two]

/-- Pointwise Jensen in `θ`:
`exp (t (G x - G y)) ≤ (π/2)⁻¹ ∫_0^{π/2} exp ((π/2) t ⟪gradG x_θ, x'_θ⟫) dθ`. -/
lemma exp_mul_smG_sub_le (hF : F.Nonempty) (hβ : β ≠ 0) (t : ℝ) (p : E × E) :
    Real.exp (t * (smG F β v b p.1 - smG F β v b p.2)) ≤
      (π / 2)⁻¹ * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (π / 2 * (t * curveD F β v b θ p)) := by
  rw [smG_sub_eq_integral hF hβ p, ← intervalIntegral.integral_const_mul]
  exact exp_intervalIntegral_le (f := fun θ => t * curveD F β v b θ p)
    (continuous_const.mul (continuous_curveD_theta hF p)) (by positivity)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_smG (hF : F.Nonempty) (hβ : 0 < β) :
    Integrable (smG F β v b) (stdGaussian E) := by
  have hM := integrable_iSup_inner_add F v b
  refine Integrable.mono' (hM.abs.fun_add (integrable_const (Real.log F.card / β)))
    (continuous_smG hF).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h1 : (⨆ i : F, ⟪v i, x⟫ + b i) ≤ smG F β v b x := iSup_le_smoothMax hF hβ (affZ v b x)
  have h2 : smG F β v b x ≤ (⨆ i : F, ⟪v i, x⟫ + b i) + Real.log F.card / β :=
    smoothMax_le_iSup hF hβ (affZ v b x)
  have hL : 0 ≤ Real.log F.card / β :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hF.card_pos)) hβ.le
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (⨆ i : F, ⟪v i, x⟫ + b i)]
  · linarith [le_abs_self (⨆ i : F, ⟪v i, x⟫ + b i)]

/-- Step 4: `E_{x,y} exp (c ⟪gradG x, y⟫) ≤ exp (σ² c² / 2)`. -/
lemma lintegral_exp_inner_gradG_le (hF : F.Nonempty) {σ : ℝ} (hv : ∀ i ∈ F, ‖v i‖ ≤ σ)
    (c : ℝ) :
    ∫⁻ q, ENNReal.ofReal (Real.exp (c * ⟪gradG F β v b q.1, q.2⟫))
        ∂((stdGaussian E).prod (stdGaussian E)) ≤
      ENNReal.ofReal (Real.exp (σ ^ 2 * c ^ 2 / 2)) := by
  have hmeas : Measurable fun q : E × E =>
      ENNReal.ofReal (Real.exp (c * ⟪gradG F β v b q.1, q.2⟫)) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (((continuous_gradG hF).comp continuous_fst).inner continuous_snd)))).measurable
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (c * ⟪gradG F β v b x, y⟫))
        ∂stdGaussian E ∂stdGaussian E
      ≤ ∫⁻ _x, ENNReal.ofReal (Real.exp (σ ^ 2 * c ^ 2 / 2)) ∂stdGaussian E := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (GaussianMax.integrable_exp_mul_inner _ c)
          (ae_of_all _ fun y => (Real.exp_pos _).le), GaussianMax.integral_exp_mul_inner]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h1 := norm_gradG_le (β := β) (b := b) hF hv x
        have h0 := norm_nonneg (gradG F β v b x)
        have h2 : ‖gradG F β v b x‖ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ h0 h1 2
        nlinarith [sq_nonneg c]
    _ = ENNReal.ofReal (Real.exp (σ ^ 2 * c ^ 2 / 2)) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- Steps 2–4: `E_{x,y} exp (t (G x - G y)) ≤ exp (π² t² σ² / 8)`. -/
theorem lintegral_exp_smG_sub_le (hF : F.Nonempty) (hβ : 0 < β) {σ : ℝ}
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (t * (smG F β v b p.1 - smG F β v b p.2)))
        ∂((stdGaussian E).prod (stdGaussian E)) ≤
      ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hKp : ∀ p : E × E,
      Continuous fun θ => Real.exp (π / 2 * (t * curveD F β v b θ p)) := fun p =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_curveD_theta (β := β) (v := v) (b := b) hF p)))
  have hKcont : Continuous fun q : (E × E) × ℝ =>
      ENNReal.ofReal (Real.exp (π / 2 * (t * curveD F β v b q.2 q.1))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.mul (continuous_curveD_swap (β := β) (v := v) (b := b) hF))))
  have hK0 : ∀ θ, ∫⁻ p, ENNReal.ofReal (Real.exp (π / 2 * (t * curveD F β v b θ p)))
      ∂((stdGaussian E).prod (stdGaussian E)) ≤
      ENNReal.ofReal (Real.exp (σ ^ 2 * (π / 2 * t) ^ 2 / 2)) := by
    intro θ
    have e : ∀ p : E × E, Real.exp (π / 2 * (t * curveD F β v b θ p)) =
        Real.exp ((π / 2 * t) * ⟪gradG F β v b (rotPair θ p).1, (rotPair θ p).2⟫) :=
      fun p => by rw [curveD, mul_assoc]
    simp_rw [e]
    have hmeas : Measurable fun q : E × E =>
        ENNReal.ofReal (Real.exp ((π / 2 * t) * ⟪gradG F β v b q.1, q.2⟫)) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
        (((continuous_gradG (β := β) (v := v) (b := b) hF).comp continuous_fst).inner
          continuous_snd)))).measurable
    rw [(measurePreserving_rotPair θ).lintegral_comp hmeas]
    exact lintegral_exp_inner_gradG_le hF hv (π / 2 * t)
  calc ∫⁻ p, ENNReal.ofReal (Real.exp (t * (smG F β v b p.1 - smG F β v b p.2)))
        ∂((stdGaussian E).prod (stdGaussian E))
      ≤ ∫⁻ p, (ENNReal.ofReal ((π / 2)⁻¹) * ∫⁻ θ in Ioc 0 (π / 2),
          ENNReal.ofReal (Real.exp (π / 2 * (t * curveD F β v b θ p))))
          ∂((stdGaussian E).prod (stdGaussian E)) := by
        refine lintegral_mono fun p => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hKp p).integrableOn_Ioc
          (ae_of_all _ fun θ => (Real.exp_pos _).le), ← ENNReal.ofReal_mul (by positivity),
          ← intervalIntegral.integral_of_le hpi]
        exact ENNReal.ofReal_le_ofReal (exp_mul_smG_sub_le hF hβ.ne' t p)
    _ = ENNReal.ofReal ((π / 2)⁻¹) * ∫⁻ θ in Ioc 0 (π / 2),
          (∫⁻ p, ENNReal.ofReal (Real.exp (π / 2 * (t * curveD F β v b θ p)))
            ∂((stdGaussian E).prod (stdGaussian E))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap]
        exact hKcont.measurable.aemeasurable
    _ ≤ ENNReal.ofReal ((π / 2)⁻¹) *
          ∫⁻ _θ in Ioc 0 (π / 2), ENNReal.ofReal (Real.exp (σ ^ 2 * (π / 2 * t) ^ 2 / 2)) := by
        gcongr with θ
        exact hK0 θ
    _ = ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hc2 : σ ^ 2 * (π / 2 * t) ^ 2 / 2 = π ^ 2 / 8 * t ^ 2 * σ ^ 2 := by ring
        rw [hc2, sub_zero]
        field_simp

/-- Step 5: `E_x exp (t (G x - E G)) ≤ E_{x,y} exp (t (G x - G y))`. -/
lemma lintegral_exp_smG_center_le (hF : F.Nonempty) (hβ : 0 < β) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * (smG F β v b x - ∫ y, smG F β v b y ∂stdGaussian E)))
        ∂stdGaussian E ≤
      ∫⁻ p, ENNReal.ofReal (Real.exp (t * (smG F β v b p.1 - smG F β v b p.2)))
        ∂((stdGaussian E).prod (stdGaussian E)) := by
  have hmeas : Measurable fun p : E × E =>
      ENNReal.ofReal (Real.exp (t * (smG F β v b p.1 - smG F β v b p.2))) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (((continuous_smG hF).comp continuous_fst).sub
        ((continuous_smG hF).comp continuous_snd))))).measurable
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_mono fun x => ?_
  set EG := ∫ y, smG F β v b y ∂stdGaussian E with hEG
  set A := t * (smG F β v b x - EG) with hA
  have hG : Integrable (smG F β v b) (stdGaussian E) := integrable_smG hF hβ
  have hpt : ∀ y, Real.exp A * (1 + t * (EG - smG F β v b y)) ≤
      Real.exp (t * (smG F β v b x - smG F β v b y)) := by
    intro y
    have h1 := Real.add_one_le_exp (t * (EG - smG F β v b y))
    have h2 : Real.exp (t * (smG F β v b x - smG F β v b y)) =
        Real.exp A * Real.exp (t * (EG - smG F β v b y)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hA]
      ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos A).le
    nlinarith
  have hint : Integrable (fun y => Real.exp A * (1 + t * (EG - smG F β v b y)))
      (stdGaussian E) :=
    ((integrable_const 1).add (((integrable_const EG).sub hG).const_mul t)).const_mul _
  have hval : ∫ y, Real.exp A * (1 + t * (EG - smG F β v b y)) ∂stdGaussian E = Real.exp A := by
    rw [integral_const_mul, integral_add (f := fun _ => (1 : ℝ))
      (g := fun a => t * (EG - smG F β v b a)) (integrable_const _)
      (((integrable_const _).sub hG).const_mul t), integral_const_mul,
      integral_sub (integrable_const _) hG, ← hEG]
    simp
  calc ENNReal.ofReal (Real.exp A)
      = ENNReal.ofReal (∫ y, Real.exp A * (1 + t * (EG - smG F β v b y)) ∂stdGaussian E) := by
        rw [hval]
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp A * (1 + t * (EG - smG F β v b y))) ∂stdGaussian E :=
        ofReal_integral_le_lintegral_ofReal' hint
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (t * (smG F β v b x - smG F β v b y)))
          ∂stdGaussian E :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)

/-- Step 1 for fixed `β`: the bound for the maximum up to the factor `exp (|t| log |F| / β)`. -/
theorem lintegral_exp_max_le_of_smooth (hF : F.Nonempty) (hβ : 0 < β) {σ : ℝ}
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)))
        ∂stdGaussian E ≤
      ENNReal.ofReal (Real.exp (|t| * (Real.log F.card / β)) *
        Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  set L := Real.log F.card / β with hL
  set EG := ∫ y, smG F β v b y ∂stdGaussian E with hEG
  set EM := vecExpectedMax F v b with hEM
  have hM := integrable_iSup_inner_add F v b
  have hG : Integrable (smG F β v b) (stdGaussian E) := integrable_smG hF hβ
  have hb1 : ∀ x, (⨆ i : F, ⟪v i, x⟫ + b i) ≤ smG F β v b x := fun x =>
    iSup_le_smoothMax hF hβ (affZ v b x)
  have hb2 : ∀ x, smG F β v b x ≤ (⨆ i : F, ⟪v i, x⟫ + b i) + L := fun x =>
    smoothMax_le_iSup hF hβ (affZ v b x)
  have hE1 : EM ≤ EG := integral_mono hM hG hb1
  have hE2 : EG ≤ EM + L := by
    have h := integral_mono hG (hM.fun_add (integrable_const L)) hb2
    rw [integral_add hM (integrable_const L), integral_const] at h
    simp only [probReal_univ, one_smul] at h
    exact h
  have hpt : ∀ x, Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - EM)) ≤
      Real.exp (|t| * L) * Real.exp (t * (smG F β v b x - EG)) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    set d := ((⨆ i : F, ⟪v i, x⟫ + b i) - EM) - (smG F β v b x - EG) with hd
    have hdabs : |d| ≤ L := by
      rw [abs_le]
      constructor <;> linarith [hb1 x, hb2 x]
    have h1 : t * d ≤ |t| * L := by
      calc t * d ≤ |t * d| := le_abs_self _
        _ = |t| * |d| := abs_mul _ _
        _ ≤ |t| * L := mul_le_mul_of_nonneg_left hdabs (abs_nonneg t)
    have h2 : t * ((⨆ i : F, ⟪v i, x⟫ + b i) - EM) = t * (smG F β v b x - EG) + t * d := by
      rw [hd]
      ring
    linarith
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - EM))) ∂stdGaussian E
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (|t| * L)) *
          ENNReal.ofReal (Real.exp (t * (smG F β v b x - EG))) ∂stdGaussian E := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (Real.exp (|t| * L)) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (t * (smG F β v b x - EG))) ∂stdGaussian E :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (|t| * L)) *
          ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
        gcongr
        exact (lintegral_exp_smG_center_le hF hβ t).trans (lintegral_exp_smG_sub_le hF hβ hv t)
    _ = ENNReal.ofReal (Real.exp (|t| * L) * Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

end Smooth

/-! ### The concentration inequality for the maximum -/

section Main

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma measurable_exp_max (F : Finset ι) (v : ι → E) (b : ι → ℝ) (t c : ℝ) :
    Measurable fun x : E => Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - c)) := by
  have hM : Measurable fun x : E => ⨆ i : F, ⟪v i, x⟫ + b i :=
    Measurable.iSup fun i => by fun_prop
  exact Real.measurable_exp.comp (measurable_const.mul (hM.sub measurable_const))

/-- **Gaussian concentration for finite maxima**, lower-integral form:
`∫⁻ exp (t (M - E M)) ≤ exp (π² t² σ² / 8)`. -/
theorem lintegral_exp_max_le (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ}
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)))
        ∂stdGaussian E ≤
      ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp only [vecExpectedMax, iSup_of_empty', Real.sSup_empty]
    simp only [integral_zero, sub_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
  set B := Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) with hB
  set L := Real.log F.card with hL
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (|t| * (L / n)) * B)) atTop
      (𝓝 (ENNReal.ofReal B)) := by
    apply ENNReal.tendsto_ofReal
    have h1 : Tendsto (fun n : ℕ => L / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat L
    have h2 := ((Real.continuous_exp.tendsto _).comp (h1.const_mul |t|)).mul_const B
    simpa using h2
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact lintegral_exp_max_le_of_smooth hF hn' hv t

theorem integrable_exp_max (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ}
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)))
      (stdGaussian E) := by
  rw [← lintegral_ofReal_ne_top_iff_integrable
    (measurable_exp_max F v b t _).aestronglyMeasurable
    (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_exp_max_le F v b hv t)

/-- **Gaussian concentration for finite maxima**: `E exp (t (M - E M)) ≤ exp (π² t² σ² / 8)`. -/
theorem integral_exp_max_le (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ}
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) (t : ℝ) :
    ∫ x, Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b)) ∂(stdGaussian E) ≤
      Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
    (measurable_exp_max F v b t _).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (lintegral_exp_max_le F v b hv t)

/-- Upper tail: `P(M - E M ≥ s) ≤ exp (-2 s² / (π² σ²))`. -/
theorem max_sub_tail_le (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) {s : ℝ} (hs : 0 ≤ s) :
    (stdGaussian E).real {x | s ≤ (⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b} ≤
      Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) := by
  set t := 4 * s / (π ^ 2 * σ ^ 2) with ht
  have ht0 : 0 ≤ t := by positivity
  have h := measure_ge_le_exp_mul_mgf (μ := stdGaussian E)
    (X := fun x => (⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b) s ht0
    (integrable_exp_max F v b hv t)
  refine h.trans ?_
  have hmgf := integral_exp_max_le F v b hv t
  rw [mgf]
  calc Real.exp (-t * s) * ∫ x, Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + b i) -
        vecExpectedMax F v b)) ∂stdGaussian E
      ≤ Real.exp (-t * s) * Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [ht]
        field_simp
        ring

/-- Lower tail: `P(E M - M ≥ s) ≤ exp (-2 s² / (π² σ²))`. -/
theorem sub_max_tail_le (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hv : ∀ i ∈ F, ‖v i‖ ≤ σ) {s : ℝ} (hs : 0 ≤ s) :
    (stdGaussian E).real {x | s ≤ vecExpectedMax F v b - (⨆ i : F, ⟪v i, x⟫ + b i)} ≤
      Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) := by
  set t := 4 * s / (π ^ 2 * σ ^ 2) with ht
  have ht0 : 0 ≤ t := by positivity
  have e : ∀ x : E, t * (vecExpectedMax F v b - (⨆ i : F, ⟪v i, x⟫ + b i)) =
      (-t) * ((⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b) := fun x => by ring
  have hint : Integrable
      (fun x => Real.exp (t * (vecExpectedMax F v b - (⨆ i : F, ⟪v i, x⟫ + b i))))
      (stdGaussian E) := by
    simp_rw [e]
    exact integrable_exp_max F v b hv (-t)
  have h := measure_ge_le_exp_mul_mgf (μ := stdGaussian E)
    (X := fun x => vecExpectedMax F v b - (⨆ i : F, ⟪v i, x⟫ + b i)) s ht0 hint
  refine h.trans ?_
  have hmgf := integral_exp_max_le F v b hv (-t)
  rw [mgf]
  simp_rw [e]
  calc Real.exp (-t * s) * ∫ x, Real.exp ((-t) * ((⨆ i : F, ⟪v i, x⟫ + b i) -
        vecExpectedMax F v b)) ∂stdGaussian E
      ≤ Real.exp (-t * s) * Real.exp (π ^ 2 / 8 * (-t) ^ 2 * σ ^ 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [ht]
        field_simp
        ring

end Main

end MaxConc

open MaxConc

/-- **Gaussian concentration for finite maxima** (blueprint obligation `MaxConcentration`),
unconditionally. -/
theorem maxConcentration : Blueprint.MaxConcentration := by
  intro ι E _ _ _ _ _ F v b σ hv t
  exact integral_exp_max_le F v b hv t

/-- **Sub-Gaussian tails of a finite maximum**: for `σ > 0`, `s ≥ 0`,
`P(M - E M ≥ s) ≤ exp (-2 s² / (π² σ²))` and `P(E M - M ≥ s) ≤ exp (-2 s² / (π² σ²))`. -/
theorem maxConcentration_tail {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ} (hσ : 0 < σ) (hv : ∀ i ∈ F, ‖v i‖ ≤ σ)
    {s : ℝ} (hs : 0 ≤ s) :
    (stdGaussian E).real {x | s ≤ (⨆ i : F, ⟪v i, x⟫ + b i) - vecExpectedMax F v b} ≤
        Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) ∧
      (stdGaussian E).real {x | s ≤ vecExpectedMax F v b - (⨆ i : F, ⟪v i, x⟫ + b i)} ≤
        Real.exp (-2 * s ^ 2 / (π ^ 2 * σ ^ 2)) :=
  ⟨max_sub_tail_le F v b hσ hv hs, sub_max_tail_le F v b hσ hv hs⟩

end LQGDimension
