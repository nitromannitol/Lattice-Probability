import Mathlib

/-!
# A second-moment bound for the Laplace transform of a sum of independent nonnegative variables

Let `I₁, …, Iₙ ≥ 0` be independent random variables on a probability space, `S = ∑ Iₖ`,
`L = E e^{-S}` and, for `η ∈ (0,1)`, `c = -log (1 - η)`.  Then
`E e^{-2S} ≤ L² · exp (L⁻² (η (-log L) + ∑ₖ P[Iₖ > c]))`.

The proof uses the independence only through the factorisation of the Laplace transform of a sum,
`E e^{-tS} = ∏ₖ E e^{-t Iₖ}`, and the elementary inequality
`(1 - z)² ≤ η (1 - z) + 1_{1 - z > η}` for `z ∈ (0, 1]`.

* `LatticeProb.mgf_neg_two_le_of_nonneg`: the one-variable inequality
  `E e^{-2X} ≤ (E e^{-X})² + η (1 - E e^{-X}) + P[X > c]`.
* `LatticeProb.mgf_sum_neg_two_le`: the bound for a finite family of independent nonnegative
  variables.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `e^{c X}` is integrable for a nonnegative measurable `X`, `c ≤ 0` and a finite measure. -/
theorem integrable_exp_mul_of_nonneg [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (h0 : ∀ ω, 0 ≤ X ω) {c : ℝ} (hc : c ≤ 0) :
    Integrable (fun ω => Real.exp (c * X ω)) μ :=
  Integrable.of_bound (measurable_const.mul hX).exp.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc (h0 ω)))

/-- **One-variable step.**  For a nonnegative measurable `X`, `η ∈ (0,1)` and
`c = -log (1 - η)`: `E e^{-2X} ≤ (E e^{-X})² + η (1 - E e^{-X}) + P[X > c]`. -/
theorem mgf_neg_two_le_of_nonneg [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (h0 : ∀ ω, 0 ≤ X ω) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    mgf X μ (-2) ≤ mgf X μ (-1) ^ 2 + η * (1 - mgf X μ (-1)) +
      μ.real {ω | -Real.log (1 - η) < X ω} := by
  set S : Set Ω := {ω | -Real.log (1 - η) < X ω} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hX
  have hZi : Integrable (fun ω => Real.exp (-1 * X ω)) μ :=
    integrable_exp_mul_of_nonneg hX h0 (by norm_num)
  have hZ2i : Integrable (fun ω => Real.exp (-2 * X ω)) μ :=
    integrable_exp_mul_of_nonneg hX h0 (by norm_num)
  have hind : Integrable (fun ω => S.indicator (1 : Ω → ℝ) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hSm
  have hpt : ∀ ω, Real.exp (-2 * X ω) ≤
      (2 - η) * Real.exp (-1 * X ω) + (η - 1) + S.indicator (1 : Ω → ℝ) ω := by
    intro ω
    have hz : Real.exp (-2 * X ω) = Real.exp (-1 * X ω) * Real.exp (-1 * X ω) := by
      rw [← Real.exp_add]; ring_nf
    have hz0 : 0 < Real.exp (-1 * X ω) := Real.exp_pos _
    have hz1 : Real.exp (-1 * X ω) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [h0 ω])
    rw [hz]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      simp only [Pi.one_apply]
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      have hle : X ω ≤ -Real.log (1 - η) := not_lt.1 hω
      have hge : 1 - η ≤ Real.exp (-1 * X ω) :=
        calc 1 - η = Real.exp (Real.log (1 - η)) := (Real.exp_log (by linarith)).symm
          _ ≤ _ := Real.exp_le_exp.2 (by linarith)
      nlinarith
  have hA : Integrable (fun ω => (2 - η) * Real.exp (-1 * X ω) + (η - 1)) μ :=
    (hZi.const_mul (2 - η)).add (integrable_const (η - 1))
  have hRHS : Integrable (fun ω => (2 - η) * Real.exp (-1 * X ω) + (η - 1) +
      S.indicator (1 : Ω → ℝ) ω) μ := hA.add hind
  have hmono := integral_mono hZ2i hRHS hpt
  rw [integral_add hA hind,
    integral_add (hZi.const_mul (2 - η)) (integrable_const (η - 1)), integral_const_mul,
    integral_const, integral_indicator_one hSm] at hmono
  have hmgf1 : mgf X μ (-1) = ∫ ω, Real.exp (-1 * X ω) ∂μ := rfl
  have hmgf2 : mgf X μ (-2) = ∫ ω, Real.exp (-2 * X ω) ∂μ := rfl
  rw [hmgf1, hmgf2]
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith [sq_nonneg (∫ ω, Real.exp (-1 * X ω) ∂μ - 1)]

/-- **Second moment of the Laplace transform of a sum of independent nonnegative variables.**
Let `I : ι → Ω → ℝ` be a finite independent family of nonnegative measurable random variables,
`S = ∑ I i`, `L = E e^{-S}`, `η ∈ (0,1)` and `c = -log (1 - η)`.  Then
`E e^{-2S} ≤ L² · exp (L⁻² (η (-log L) + ∑ i, P[I i > c]))`. -/
theorem mgf_sum_neg_two_le {ι : Type*} [Fintype ι] [IsProbabilityMeasure μ] {I : ι → Ω → ℝ}
    (hind : iIndepFun I μ) (hmeas : ∀ i, Measurable (I i)) (h0 : ∀ i ω, 0 ≤ I i ω)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    mgf (∑ i, I i) μ (-2) ≤ mgf (∑ i, I i) μ (-1) ^ 2 *
      Real.exp ((mgf (∑ i, I i) μ (-1))⁻¹ ^ 2 *
        (η * (-Real.log (mgf (∑ i, I i) μ (-1))) +
          ∑ i, μ.real {ω | -Real.log (1 - η) < I i ω})) := by
  classical
  have hsum1 := hind.mgf_sum (t := -1) hmeas Finset.univ
  have hsum2 := hind.mgf_sum (t := -2) hmeas Finset.univ
  rw [hsum1, hsum2]
  set a : ι → ℝ := fun i => mgf (I i) μ (-1) with ha
  set b : ι → ℝ := fun i => mgf (I i) μ (-2) with hb
  set p : ι → ℝ := fun i => μ.real {ω | -Real.log (1 - η) < I i ω} with hp
  have ha_pos : ∀ i, 0 < a i := fun i =>
    integral_exp_pos (integrable_exp_mul_of_nonneg (hmeas i) (h0 i) (by norm_num))
  have ha_le : ∀ i, a i ≤ 1 := fun i => by
    have hle : ∫ ω, Real.exp (-1 * I i ω) ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ :=
      integral_mono (integrable_exp_mul_of_nonneg (hmeas i) (h0 i) (by norm_num))
        (integrable_const 1) fun ω =>
          Real.exp_le_one_iff.2 (by linarith [h0 i ω])
    have h1 : ∫ _ω, (1 : ℝ) ∂μ = 1 := by simp
    exact h1 ▸ hle
  have hb_nn : ∀ i, 0 ≤ b i := fun i => mgf_nonneg
  have hp_nn : ∀ i, 0 ≤ p i := fun i => measureReal_nonneg
  set L : ℝ := ∏ i, a i with hL
  have hL_pos : 0 < L := Finset.prod_pos fun i _ => ha_pos i
  have hL_le : ∀ i, L ≤ a i := fun i => by
    rw [hL, ← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact mul_le_of_le_one_right (ha_pos i).le
      (Finset.prod_le_one₀ (fun j _ => (ha_pos j).le) fun j _ => ha_le j)
  -- the per-variable bound
  have hstep : ∀ i, b i ≤ a i ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (1 - a i) + p i)) := by
    intro i
    have h1 := mgf_neg_two_le_of_nonneg (μ := μ) (hmeas i) (h0 i) hη0 hη1
    set r : ℝ := η * (1 - a i) + p i with hr
    have hr0 : 0 ≤ r := add_nonneg (mul_nonneg hη0.le (sub_nonneg.2 (ha_le i))) (hp_nn i)
    have h2 : 1 ≤ a i * L⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hL_pos]
      simpa using hL_le i
    have h3 : 1 ≤ (a i * L⁻¹) ^ 2 := one_le_pow₀ h2
    have h4 : r ≤ a i ^ 2 * (L⁻¹ ^ 2 * r) := by
      have : a i ^ 2 * (L⁻¹ ^ 2 * r) = (a i * L⁻¹) ^ 2 * r := by ring
      rw [this]
      nlinarith
    have h5 : L⁻¹ ^ 2 * r + 1 ≤ Real.exp (L⁻¹ ^ 2 * r) := Real.add_one_le_exp _
    have h6 : b i ≤ a i ^ 2 + r := by
      have : b i ≤ a i ^ 2 + η * (1 - a i) + p i := h1
      linarith
    nlinarith [sq_nonneg (a i)]
  have hprod : ∏ i, b i ≤ ∏ i, (a i ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (1 - a i) + p i))) :=
    Finset.prod_le_prod₀ (fun i _ => hb_nn i) fun i _ => hstep i
  have hrhs : ∏ i, (a i ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (1 - a i) + p i))) =
      L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * ∑ i, (1 - a i) + ∑ i, p i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, ← Real.exp_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  -- `∑ (1 - a i) ≤ -log L`
  have hlog : ∑ i, (1 - a i) ≤ -Real.log L := by
    have : Real.log L = ∑ i, Real.log (a i) :=
      Real.log_prod fun i _ => (ha_pos i).ne'
    rw [this, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => by linarith [Real.log_le_sub_one_of_pos (ha_pos i)]
  have hexp : Real.exp (L⁻¹ ^ 2 * (η * ∑ i, (1 - a i) + ∑ i, p i)) ≤
      Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L) + ∑ i, p i)) := by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have := mul_le_mul_of_nonneg_left hlog hη0.le
    linarith
  calc ∏ i, b i ≤ _ := hprod
    _ = _ := hrhs
    _ ≤ L ^ 2 * Real.exp (L⁻¹ ^ 2 * (η * (-Real.log L) + ∑ i, p i)) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg _)

end LatticeProb
