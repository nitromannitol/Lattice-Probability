/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/KahaneInterp.lean.
-/
import LatticeProb.Prob.GaussKahaneBound
import LatticeProb.Prob.GaussKahaneStein

/-!
# Kahane's convexity inequality in Gram form

`LatticeProb.Kahane.integral_kW_zero_le`: for `u, u' : ι → H` with `u i ⊥ u' j` and
`⟪u i, u j⟫ ≤ ⟪u' i, u' j⟫` for all `i, j`, weights `p i > 0`, and `F` admissible
(`KahaneFun`: convex `C²` on `(0, ∞)`, polynomial growth in `y + y⁻¹`), with `x` standard
Gaussian on `H`:

  `E F(∑ p_i e^{⟪u i, x⟫ - ⟪u i, u i⟫/2}) ≤ E F(∑ p_i e^{⟪u' i, x⟫ - ⟪u' i, u' i⟫/2})`.

Proof: let `φ(θ) = E F(W θ x)` along `U θ i = cos θ u i + sin θ u' i`. By dominated
differentiation `φ'(θ) = E[F'(W) ∑ᵢ wᵢ (⟪U'ᵢ, x⟫ - ⟪Uᵢ, U'ᵢ⟫)]`. Gaussian integration by parts on
`⟪U'ᵢ, x⟫ F'(W) wᵢ` (`integral_inner_mul_stdGaussian_of_le`) cancels the `⟪Uᵢ, U'ᵢ⟫` terms and
leaves `φ'(θ) = E[F''(W) ∑ᵢⱼ wᵢ wⱼ ⟪Uⱼ, U'ᵢ⟫]`, where `⟪Uⱼ, U'ᵢ⟫ = cos θ sin θ (⟪u' j, u' i⟫ -
⟪u j, u i⟫) ≥ 0` on `[0, π/2]`. Since `U θ` runs from `u` to `u'` along `√(1 - t) u + √t u'`
with `t = sin² θ`, the endpoint comparison follows from `φ` being monotone on `[0, π/2]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb

namespace Kahane

section interp

variable {F F' F'' : ℝ → ℝ} {C : ℝ} {k : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
variable {p : ι → ℝ} {u u' : ι → H}

variable (hFK : KahaneFun F F' F'' C k) (hp : ∀ i, 0 < p i)
include hFK hp

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- For each `θ`, the composite `x ↦ F (kW p u u' θ x)` is continuous. -/
lemma continuous_F_kW (θ : ℝ) : Continuous fun x => F (kW p u u' θ x) :=
  hFK.continuousOn.comp_continuous (continuous_kW p u u' θ) fun x => kW_pos hp θ x

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- For each `θ`, the composite `x ↦ F' (kW p u u' θ x)` is continuous. -/
lemma continuous_F'_kW (θ : ℝ) : Continuous fun x => F' (kW p u u' θ x) :=
  hFK.continuousOn'.comp_continuous (continuous_kW p u u' θ) fun x => kW_pos hp θ x

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- For each `θ`, the composite `x ↦ F'' (kW p u u' θ x)` is continuous. -/
lemma continuous_F''_kW (θ : ℝ) : Continuous fun x => F'' (kW p u u' θ x) :=
  hFK.continuousOn''.comp_continuous (continuous_kW p u u' θ) fun x => kW_pos hp θ x

omit [Nonempty ι] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H]
  [BorelSpace H] in
/-- A bound by `kUB` gives an exponential bound of the form `kAe * exp (kBe * ‖x‖)`. -/
lemma le_exp_of_le_kUB {f : H → ℝ} (hf : ∀ x, |f x| ≤ kUB C k p u u' x) (x : H) :
    |f x| ≤ kAe C k p u u' * Real.exp (kBe k u u' * ‖x‖) :=
  (hf x).trans (kUB_le_exp hFK hp x)

omit [Nonempty ι] in
/-- A continuous function dominated by `kUB` is integrable against the standard Gaussian. -/
lemma integrable_of_le_kUB {f : H → ℝ} (hfc : Continuous f) (hf : ∀ x, |f x| ≤ kUB C k p u u' x) :
    Integrable f (stdGaussian H) :=
  integrable_of_le_exp hfc.aestronglyMeasurable (le_exp_of_le_kUB hFK hp hf)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The `θ`-derivative of `θ ↦ F (kW p u u' θ x)` is `kD F' p u u' θ x`. -/
lemma hasDerivAt_F_kW_theta (θ : ℝ) (x : H) :
    HasDerivAt (fun t => F (kW p u u' t x)) (kD F' p u u' θ x) θ := by
  have hs : HasDerivAt (fun t => kW p u u' t x)
      (∑ i, kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)) θ := by
    unfold kW
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_kw_theta p u u' θ x i
  exact (hFK.hasDerivAt _ (kW_pos hp θ x)).comp θ hs

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- Along a line `s ↦ x + s • e`, the function `kG F' p u u' θ i` has the derivative
`⟪kGrad F' F'' p u u' θ i (x + t • e), e⟫` at `t`. -/
lemma hasDerivAt_kG_line (θ : ℝ) (i : ι) (x e : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kG F' p u u' θ i (x + s • e))
      ⟪kGrad F' F'' p u u' θ i (x + t • e), e⟫ t := by
  have hs : HasDerivAt (fun s : ℝ => kW p u u' θ (x + s • e))
      (∑ j, kw p u u' θ (x + t • e) j * ⟪kU u u' θ j, e⟫) t := by
    unfold kW
    exact HasDerivAt.fun_sum fun j _ => hasDerivAt_kw_line p u u' θ x e t j
  have h1 := (hFK.hasDerivAt' _ (kW_pos hp θ (x + t • e))).comp t hs
  have h2 := h1.mul (hasDerivAt_kw_line p u u' θ x e t i)
  refine h2.congr_deriv ?_
  simp only [kGrad, inner_add_left, real_inner_smul_left, sum_inner, Function.comp_def]
  ring

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The gradient `kGrad F' F'' p u u' θ i` is continuous. -/
lemma continuous_kGrad (θ : ℝ) (i : ι) : Continuous (kGrad F' F'' p u u' θ i) := by
  unfold kGrad
  exact (((continuous_F''_kW hFK hp θ).mul (continuous_kw p u u' θ i)).smul
    (continuous_finsetSum _ fun j _ => (continuous_kw p u u' θ j).smul continuous_const)).add
    (((continuous_F'_kW hFK hp θ).mul (continuous_kw p u u' θ i)).smul continuous_const)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The function `kG F' p u u' θ i` is continuous. -/
lemma continuous_kG (θ : ℝ) (i : ι) : Continuous (kG F' p u u' θ i) :=
  (continuous_F'_kW hFK hp θ).mul (continuous_kw p u u' θ i)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The `θ`-derivative `kD F' p u u' θ` is continuous. -/
lemma continuous_kD (θ : ℝ) : Continuous (kD F' p u u' θ) := by
  unfold kD
  exact (continuous_F'_kW hFK hp θ).mul (continuous_finsetSum _ fun i _ =>
    (continuous_kw p u u' θ i).mul ((continuous_const.inner continuous_id).sub continuous_const))

/-- Gaussian integration by parts for `⟪a, x⟫ G_i(x)`. -/
lemma integral_inner_mul_kG (θ : ℝ) (i : ι) (a : H) :
    ∫ x, ⟪a, x⟫ * kG F' p u u' θ i x ∂(stdGaussian H) =
      ∫ x, ⟪kGrad F' F'' p u u' θ i x, a⟫ ∂(stdGaussian H) :=
  integral_inner_mul_stdGaussian_of_le (hasDerivAt_kG_line hFK hp θ i)
    (continuous_kG hFK hp θ i) (continuous_kGrad hFK hp θ i)
    (le_exp_of_le_kUB hFK hp (abs_kG_le_kUB hFK hp θ i))
    (fun x => (norm_kGrad_le hFK hp θ i x).trans (kUB_le_exp hFK hp x)) a

omit [Fintype ι] [Nonempty ι] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] hFK hp in
/-- The inner products along the path are nonnegative on `[0, π/2]`. -/
lemma inner_kU_kU'_nonneg (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hcov : ∀ i j, ⟪u i, u j⟫ ≤ ⟪u' i, u' j⟫) {θ : ℝ} (hθ : 0 ≤ Real.cos θ * Real.sin θ)
    (i j : ι) : 0 ≤ ⟪kU u u' θ j, kU' u u' θ i⟫ := by
  have h1 : ⟪u j, u' i⟫ = 0 := horth j i
  have h2 : ⟪u' j, u i⟫ = 0 := by rw [real_inner_comm]; exact horth i j
  have e : ⟪kU u u' θ j, kU' u u' θ i⟫ =
      Real.cos θ * Real.sin θ * (⟪u' j, u' i⟫ - ⟪u j, u i⟫) := by
    simp only [kU, kU', inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, h1, h2]
    ring
  rw [e]
  exact mul_nonneg hθ (sub_nonneg.2 (hcov j i))

/-- **The derivative of the interpolation is nonnegative.** -/
lemma integral_kD_nonneg (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hcov : ∀ i j, ⟪u i, u j⟫ ≤ ⟪u' i, u' j⟫) {θ : ℝ} (hθ : 0 ≤ Real.cos θ * Real.sin θ) :
    0 ≤ ∫ x, kD F' p u u' θ x ∂(stdGaussian H) := by
  set a : ι → H → ℝ := fun i x => ⟪kU' u u' θ i, x⟫ * kG F' p u u' θ i x
  set b : ι → H → ℝ := fun i x => ⟪kU u u' θ i, kU' u u' θ i⟫ * kG F' p u u' θ i x
  set c : ι → H → ℝ := fun i x => ⟪kGrad F' F'' p u u' θ i x, kU' u u' θ i⟫
  have hGi : ∀ i, Integrable (kG F' p u u' θ i) (stdGaussian H) := fun i =>
    integrable_of_le_kUB hFK hp (continuous_kG hFK hp θ i) (abs_kG_le_kUB hFK hp θ i)
  have hai : ∀ i, Integrable (a i) (stdGaussian H) := fun i => by
    refine integrable_of_le_exp (A := ‖kU' u u' θ i‖ * kAe C k p u u') (B := kBe k u u' + 1)
      ((continuous_const.inner continuous_id).mul (continuous_kG hFK hp θ i)).aestronglyMeasurable
      fun x => ?_
    have hA : 0 ≤ kAe C k p u u' := by
      unfold kAe
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hFK.C_nonneg (by positivity))
        (by positivity)) (by positivity))
        (pow_nonneg (zero_le_one.trans (one_le_kA (u := u) (u' := u') hp)) _)
    simp only [a]
    rw [abs_mul]
    calc |⟪kU' u u' θ i, x⟫| * |kG F' p u u' θ i x|
        ≤ (‖kU' u u' θ i‖ * ‖x‖) * (kAe C k p u u' * Real.exp (kBe k u u' * ‖x‖)) :=
          mul_le_mul (abs_real_inner_le_norm _ _)
            (le_exp_of_le_kUB hFK hp (abs_kG_le_kUB hFK hp θ i) x) (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖kU' u u' θ i‖ * (‖x‖ * (kAe C k p u u' * Real.exp (kBe k u u' * ‖x‖))) := by ring
      _ ≤ ‖kU' u u' θ i‖ * (kAe C k p u u' * Real.exp ((kBe k u u' + 1) * ‖x‖)) :=
          mul_le_mul_of_nonneg_left (norm_mul_exp_le _ _ hA x) (norm_nonneg _)
      _ = _ := by ring
  have hbi : ∀ i, Integrable (b i) (stdGaussian H) := fun i => (hGi i).const_mul _
  have hci : ∀ i, Integrable (c i) (stdGaussian H) := fun i =>
    integrable_of_le_exp (A := kAe C k p u u' * ‖kU' u u' θ i‖) (B := kBe k u u')
      ((continuous_kGrad hFK hp θ i).inner continuous_const).aestronglyMeasurable fun x => by
        refine (abs_real_inner_le_norm _ _).trans ?_
        calc ‖kGrad F' F'' p u u' θ i x‖ * ‖kU' u u' θ i‖
            ≤ (kAe C k p u u' * Real.exp (kBe k u u' * ‖x‖)) * ‖kU' u u' θ i‖ :=
              mul_le_mul_of_nonneg_right
                ((norm_kGrad_le hFK hp θ i x).trans (kUB_le_exp hFK hp x)) (norm_nonneg _)
          _ = _ := by ring
  have hD : kD F' p u u' θ = fun x => ∑ i, (a i x - b i x) := by
    funext x
    simp only [kD, a, b, kG, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstein : ∀ i, ∫ x, a i x ∂(stdGaussian H) = ∫ x, c i x ∂(stdGaussian H) := fun i =>
    integral_inner_mul_kG hFK hp θ i (kU' u u' θ i)
  rw [hD]
  beta_reduce
  rw [integral_finsetSum (f := fun i x => a i x - b i x) _ fun i _ => (hai i).sub (hbi i)]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [integral_sub (hai i) (hbi i), hstein i, ← integral_sub (hci i) (hbi i)]
  refine integral_nonneg fun x => ?_
  have e : c i x - b i x = F'' (kW p u u' θ x) * kw p u u' θ x i *
      ∑ j, kw p u u' θ x j * ⟪kU u u' θ j, kU' u u' θ i⟫ := by
    simp only [c, b, kGrad, kG, inner_add_left, real_inner_smul_left, sum_inner]
    ring
  show 0 ≤ c i x - b i x
  rw [e]
  exact mul_nonneg (mul_nonneg (hFK.nonneg'' _ (kW_pos hp θ x)) (kw_pos hp θ x i).le)
    (Finset.sum_nonneg fun j _ => mul_nonneg (kw_pos hp θ x j).le
      (inner_kU_kU'_nonneg horth hcov hθ i j))

/-- **Kahane's convexity inequality, Gram form.** -/
theorem integral_kW_zero_le (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    (hcov : ∀ i j, ⟪u i, u j⟫ ≤ ⟪u' i, u' j⟫) :
    ∫ x, F (kW p u u' 0 x) ∂(stdGaussian H) ≤ ∫ x, F (kW p u u' (π / 2) x) ∂(stdGaussian H) := by
  have hderiv : ∀ θ, HasDerivAt (fun t => ∫ x, F (kW p u u' t x) ∂(stdGaussian H))
      (∫ x, kD F' p u u' θ x ∂(stdGaussian H)) θ := fun θ =>
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) univ_mem
      (Eventually.of_forall fun t => (continuous_F_kW hFK hp t).aestronglyMeasurable)
      (integrable_of_le_kUB hFK hp (continuous_F_kW hFK hp θ) (abs_F_kW_le hFK hp θ))
      (continuous_kD hFK hp θ).aestronglyMeasurable
      (ae_of_all _ fun x t _ => by
        rw [Real.norm_eq_abs]; exact le_exp_of_le_kUB hFK hp (abs_kD_le hFK hp t) x)
      ((integrable_exp_mul_norm_stdGaussian _).const_mul _)
      (ae_of_all _ fun x t _ => hasDerivAt_F_kW_theta hFK hp t x)).2
  have hmono : MonotoneOn (fun t => ∫ x, F (kW p u u' t x) ∂(stdGaussian H)) (Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
      (fun θ _ => (hderiv θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hderiv θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
    rw [interior_Icc] at hθ
    rw [(hderiv θ).deriv]
    refine integral_kD_nonneg hFK hp horth hcov (mul_nonneg ?_ ?_)
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
  exact hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos])

end interp

/-! ### Nonvacuity of the hypotheses of `integral_kW_zero_le` -/

namespace KahaneInterpExample

-- With one index, weights `1`, and `u = u' = 0`, the orthogonality and covariance hypotheses hold,
-- so the inequality applies to every admissible `F` (admissible functions exist by
-- `KahaneBoundExample`).
example {F F' F'' : ℝ → ℝ} {C : ℝ} {k : ℕ} (hFK : KahaneFun F F' F'' C k) :
    ∫ x, F (kW (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (0 : ℝ)) (fun _ : Unit => (0 : ℝ)) 0 x)
        ∂(stdGaussian ℝ) ≤
      ∫ x, F (kW (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (0 : ℝ)) (fun _ : Unit => (0 : ℝ))
        (π / 2) x) ∂(stdGaussian ℝ) :=
  integral_kW_zero_le (u := fun _ : Unit => (0 : ℝ)) (u' := fun _ : Unit => (0 : ℝ))
    (p := fun _ : Unit => (1 : ℝ)) hFK (fun _ => one_pos) (fun _ _ => by simp) (fun _ _ => by simp)

end KahaneInterpExample

end Kahane

end LatticeProb
