import Mathlib

/-!
# Laplace transforms of sums over independent copies with random weights

Let `μ` be a probability measure on a space `Ωa` carrying positive random weights `V i`
(`i` in a finite index type) and let `Z ≥ 0` be a measurable function on a probability space
`(Ω₁, P₁)`.  On the product `Ωa × (ι → Ω₁)` with the measure `μ ⊗ P₁^ι`, the `ι`-indexed
copies `x ↦ Z (x.2 i)` are conditionally independent given the weights, so the Laplace transform
of the weighted sum `∑ i, V i * Z (x.2 i)` factorises, conditionally on the weights, into a product
of one-dimensional Laplace transforms.  If `L` bounds the one-dimensional Laplace transforms of `Z`,
we obtain
`E exp (-lam ∑ i V i Z_i) ≤ E ∏ i L (lam V i)`.
-/

open MeasureTheory

noncomputable section

namespace LatticeProb

variable {Ωa Ω₁ ι : Type*} [MeasurableSpace Ωa] [MeasurableSpace Ω₁] [Fintype ι]

/-- **Factorisation of the Laplace transform of a randomly weighted sum of i.i.d. copies.**
Let `μ` be a probability measure on `Ωa`, `V i : Ωa → ℝ` positive measurable weights and
`Z : Ω₁ → ℝ` measurable and nonnegative with `P₁`-Laplace transforms bounded by `L`.  Then for
`0 < lam` and integrable `a ↦ ∏ i, L (lam * V i a)`,
`∫ exp (-(lam ∑ i V i x.1 * Z (x.2 i))) ∂(μ ⊗ P₁^ι) ≤ ∫ ∏ i L (lam * V i a) ∂μ`. -/
theorem integral_exp_neg_sum_prod_le (μ : Measure Ωa) [IsProbabilityMeasure μ]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (V : ι → Ωa → ℝ) (Z : Ω₁ → ℝ)
    (hV : ∀ i, Measurable (V i)) (hVpos : ∀ i a, 0 < V i a) (hZ : Measurable Z)
    (hZ0 : ∀ w, 0 ≤ Z w) (L : ℝ → ℝ)
    (hL : ∀ ν : ℝ, 0 < ν → ∫ w, Real.exp (-(ν * Z w)) ∂P₁ ≤ L ν) {lam : ℝ} (hlam : 0 < lam)
    (hint : Integrable (fun a => ∏ i, L (lam * V i a)) μ) :
    ∫ x : Ωa × (ι → Ω₁), Real.exp (-(lam * ∑ i, V i x.1 * Z (x.2 i)))
        ∂(μ.prod (Measure.pi fun _ : ι => P₁)) ≤
      ∫ a, ∏ i, L (lam * V i a) ∂μ := by
  have hfac : ∀ (a : Ωa) (y : ι → Ω₁), Real.exp (-(lam * ∑ i, V i a * Z (y i))) =
      ∏ i, Real.exp (-(lam * V i a * Z (y i))) := by
    intro a y
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmeas : Measurable fun x : Ωa × (ι → Ω₁) =>
      Real.exp (-(lam * ∑ i, V i x.1 * Z (x.2 i))) := by
    refine Real.measurable_exp.comp (Measurable.neg (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => ?_)))
    exact ((hV i).comp measurable_fst).mul (hZ.comp ((measurable_pi_apply i).comp measurable_snd))
  have hbd : ∀ x : Ωa × (ι → Ω₁), ‖Real.exp (-(lam * ∑ i, V i x.1 * Z (x.2 i)))‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hlam.le (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hVpos i x.1).le (hZ0 _))
  have hI : Integrable (fun x : Ωa × (ι → Ω₁) => Real.exp (-(lam * ∑ i, V i x.1 * Z (x.2 i))))
      (μ.prod (Measure.pi fun _ : ι => P₁)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  rw [integral_prod _ hI]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => ?_) hint
    (Filter.Eventually.of_forall fun a => ?_)
  · exact integral_nonneg fun _ => (Real.exp_pos _).le
  · beta_reduce
    simp_rw [hfac]
    have := integral_fintype_prod_eq_prod (μ := fun _ : ι => P₁)
      (fun i (z : Ω₁) => Real.exp (-(lam * V i a * Z z)))
    rw [this]
    refine Finset.prod_le_prod₀ (fun i _ => integral_nonneg fun _ => (Real.exp_pos _).le)
      fun i _ => ?_
    have h := hL (lam * V i a) (mul_pos hlam (hVpos i a))
    simpa using h

end LatticeProb
