/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.MaxInequality at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian

/-!
# Gaussian maximal inequality

Let `x` be a standard Gaussian vector of a finite-dimensional real inner product space `E`
(`x ∼ stdGaussian E`).

* `stdGaussian_map_inner`: the law of `⟪u, x⟫` is `𝒩(0, ‖u‖²)`.
* `integral_exp_mul_inner`: `E exp (t ⟪u, x⟫) = exp (‖u‖² t² / 2)`.
* `integral_inner_sq`: `E ⟪u, x⟫² = ‖u‖²`.
* `integral_iSup_inner_le`: for a finite nonempty `S` of size `N`, vectors with `‖u i‖ ≤ σ` and
  every `λ > 0`, `E max_{i ∈ S} ⟪u i, x⟫ ≤ (log N + λ² σ² / 2) / λ`.
* `integral_iSup_inner_le_sqrt`: `E max_{i ∈ S} ⟪u i, x⟫ ≤ σ √(2 log N)` when `N ≥ 2`.

The maximal inequality is proved without Jensen's inequality, from the pointwise bound
`λ M ≤ a - 1 + e^{-a} e^{λ M}` (i.e. `y + 1 ≤ e^y`) and `e^{λ M} ≤ ∑_i e^{λ ⟪u i, x⟫}`.
The integrability of the maximum is taken as a hypothesis (it is `Blueprint.MaxIntegrable`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace LQGDimension.GaussianMax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coe_innerSL_eq (u : E) : (⇑(innerSL ℝ u) : E → ℝ) = fun x => ⟪u, x⟫ := by
  ext x
  simp [innerSL_apply_apply]

/-- The law of `⟪u, x⟫` under the standard Gaussian measure is `𝒩(0, ‖u‖²)`. -/
theorem stdGaussian_map_inner (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) = gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm,
    coe_innerSL_eq] at h
  exact h

theorem hasLaw_inner (u : E) :
    HasLaw (fun x => ⟪u, x⟫) (gaussianReal 0 (‖u‖ ^ 2).toNNReal) (stdGaussian E) :=
  ⟨(continuous_const.inner continuous_id).measurable.aemeasurable, stdGaussian_map_inner u⟩

theorem mgf_inner (u : E) (t : ℝ) :
    mgf (fun x => ⟪u, x⟫) (stdGaussian E) t = exp (‖u‖ ^ 2 * t ^ 2 / 2) := by
  rw [mgf_gaussianReal (hasLaw_inner u) t, Real.coe_toNNReal _ (sq_nonneg _)]
  ring_nf

/-- `E exp (t ⟪u, x⟫) = exp (‖u‖² t² / 2)`. -/
theorem integral_exp_mul_inner (u : E) (t : ℝ) :
    ∫ x, exp (t * ⟪u, x⟫) ∂stdGaussian E = exp (‖u‖ ^ 2 * t ^ 2 / 2) :=
  mgf_inner u t

theorem integrable_exp_mul_inner (u : E) (t : ℝ) :
    Integrable (fun x => exp (t * ⟪u, x⟫)) (stdGaussian E) := by
  rw [← mgf_pos_iff, mgf_inner]
  exact exp_pos _

theorem integrable_inner_sq (u : E) :
    Integrable (fun x => ⟪u, x⟫ ^ 2) (stdGaussian E) := by
  have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ u) 2 (by simp)).integrable_sq
  rwa [coe_innerSL_eq] at h

/-- `E ⟪u, x⟫² = ‖u‖²`. -/
theorem integral_inner_sq (u : E) :
    ∫ x, ⟪u, x⟫ ^ 2 ∂stdGaussian E = ‖u‖ ^ 2 := by
  have h := variance_dual_stdGaussian (E := E) (innerSL ℝ u)
  have h0 := integral_strongDual_stdGaussian (E := E) (innerSL ℝ u)
  rw [innerSL_apply_norm] at h
  rw [coe_innerSL_eq] at h h0
  rw [variance_of_integral_eq_zero (X := fun x => ⟪u, x⟫) (μ := stdGaussian E)
    (continuous_const.inner continuous_id).measurable.aemeasurable h0] at h
  exact h

/-- **Gaussian maximal inequality** (exponential-moment form): for a finite nonempty index set
`S` of size `N`, vectors `u i` with `‖u i‖ ≤ σ` and `λ > 0`,
`E max_{i ∈ S} ⟪u i, x⟫ ≤ (log N + λ² σ² / 2) / λ`. -/
theorem integral_iSup_inner_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (u : ι → E)
    {σ l : ℝ} (hl : 0 < l) (hu : ∀ i ∈ S, ‖u i‖ ≤ σ)
    (hint : Integrable (fun x => ⨆ i : S, ⟪u i, x⟫) (stdGaussian E)) :
    ∫ x, (⨆ i : S, ⟪u i, x⟫) ∂stdGaussian E ≤ (Real.log S.card + l ^ 2 * σ ^ 2 / 2) / l := by
  set N : ℝ := (S.card : ℝ) with hNdef
  set a : ℝ := Real.log N + l ^ 2 * σ ^ 2 / 2 with hadef
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast hS.card_pos
  have : Nonempty S := hS.to_subtype
  have hpt : ∀ x, l * (⨆ i : S, ⟪u i, x⟫) ≤
      (a - 1) + exp (-a) * ∑ i ∈ S, exp (l * ⟪u i, x⟫) := by
    intro x
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i : S => ⟪u i, x⟫)
    rw [← hi₀]
    have h1 : exp (l * ⟪u i₀, x⟫) ≤ ∑ i ∈ S, exp (l * ⟪u i, x⟫) :=
      Finset.single_le_sum (f := fun i => exp (l * ⟪u i, x⟫)) (fun i _ => (exp_pos _).le) i₀.2
    have h2 := add_one_le_exp (l * ⟪u i₀, x⟫ - a)
    have h3 : exp (l * ⟪u i₀, x⟫ - a) = exp (-a) * exp (l * ⟪u i₀, x⟫) := by
      rw [← exp_add]
      ring_nf
    rw [h3] at h2
    nlinarith [exp_pos (-a)]
  have hRint : Integrable (fun x => (a - 1) + exp (-a) * ∑ i ∈ S, exp (l * ⟪u i, x⟫))
      (stdGaussian E) :=
    (integrable_const _).add
      ((integrable_finsetSum S fun i _ => integrable_exp_mul_inner (u i) l).const_mul _)
  have hmono := integral_mono (hint.const_mul l) hRint hpt
  rw [integral_const_mul, integral_add (integrable_const _)
    ((integrable_finsetSum S fun i _ => integrable_exp_mul_inner (u i) l).const_mul _),
    integral_const, integral_const_mul,
    integral_finsetSum S fun i _ => integrable_exp_mul_inner (u i) l] at hmono
  simp only [integral_exp_mul_inner, probReal_univ, one_smul] at hmono
  have hsum : ∑ i ∈ S, exp (‖u i‖ ^ 2 * l ^ 2 / 2) ≤ N * exp (l ^ 2 * σ ^ 2 / 2) := by
    calc ∑ i ∈ S, exp (‖u i‖ ^ 2 * l ^ 2 / 2)
        ≤ ∑ _i ∈ S, exp (l ^ 2 * σ ^ 2 / 2) := by
          refine Finset.sum_le_sum fun i hi => exp_le_exp.2 ?_
          have := pow_le_pow_left₀ (norm_nonneg _) (hu i hi) 2
          nlinarith [sq_nonneg l]
      _ = N * exp (l ^ 2 * σ ^ 2 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hexp : exp (-a) * (N * exp (l ^ 2 * σ ^ 2 / 2)) = 1 := by
    rw [hadef, exp_neg, exp_add, exp_log hN]
    field_simp
  rw [le_div_iff₀ hl]
  have hea := exp_pos (-a)
  nlinarith [mul_le_mul_of_nonneg_left hsum hea.le]

/-- **Gaussian maximal inequality**: `E max_{i ∈ S} ⟪u i, x⟫ ≤ σ √(2 log N)` for `N ≥ 2`
vectors of norm at most `σ`. -/
theorem integral_iSup_inner_le_sqrt {ι : Type*} (S : Finset ι) (hS : 1 < S.card) (u : ι → E)
    {σ : ℝ} (hσ : 0 < σ) (hu : ∀ i ∈ S, ‖u i‖ ≤ σ)
    (hint : Integrable (fun x => ⨆ i : S, ⟪u i, x⟫) (stdGaussian E)) :
    ∫ x, (⨆ i : S, ⟪u i, x⟫) ∂stdGaussian E ≤ σ * √(2 * Real.log S.card) := by
  have hS0 : S.Nonempty := Finset.card_pos.1 (by omega)
  have hlog : 0 < Real.log S.card := Real.log_pos (by exact_mod_cast hS)
  set s := √(2 * Real.log S.card) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * Real.log S.card := Real.sq_sqrt (by positivity)
  have h := integral_iSup_inner_le S hS0 u (l := s / σ) (by positivity) hu hint
  refine h.trans (le_of_eq ?_)
  field_simp
  nlinarith [hs2]

end LQGDimension.GaussianMax
