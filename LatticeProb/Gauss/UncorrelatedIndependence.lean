import LatticeProb.Gauss.TruncatedExpMoment

/-!
# Uncorrelated linear combinations of a Gaussian process, and the exponential martingale weight

Let `X` be a real Gaussian process. Finite linear combinations of its coordinates (members of the linear span of
the coordinates) again form a Gaussian process, so two families of such combinations that are pairwise uncorrelated
are independent. This is the form in which independence is used for increments of circle averages of a Gaussian
field.

For a centered Gaussian variable `D` of variance `v` the weight `W = exp (-γ² v / 2) exp (γ D) - 1` has mean zero and
second moment `exp (γ² v) - 1`; if `D` is independent of `Y` then `E[F(Y) W] = 0` and
`E[F(Y)² W²] = E[F(Y)²] (exp (γ² v) - 1)`. These are the two identities behind the second moment computation for
Gaussian multiplicative chaos along a geometric sequence of scales.

## Main statements

* `LatticeProb.GaussIndep.isGaussianProcess_of_mem_span`
* `LatticeProb.GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero`,
  `LatticeProb.GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero`
* `LatticeProb.GaussIndep.integral_expWeight`, `LatticeProb.GaussIndep.integral_expWeight_sq`
* `LatticeProb.GaussIndep.integral_mul_expWeight_eq_zero`, `LatticeProb.GaussIndep.integral_sq_mul_expWeight_sq`
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace LatticeProb.GaussIndep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T S S' : Type*}

/-- A real process each of whose coordinates lies in the linear span of the coordinates of a Gaussian process is a
Gaussian process. -/
theorem isGaussianProcess_of_mem_span {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {Y : S → Ω → ℝ}
    (h : ∀ s, Y s ∈ Submodule.span ℝ (Set.range X)) : IsGaussianProcess Y P := by
  refine hX.of_isGaussianProcess fun s => ?_
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (h s)
  refine ⟨c.support,
    ∑ i : c.support, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : c.support => ℝ) i, fun ω => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FunLike.coe_sum,
    FunLike.coe_smul, ContinuousLinearMap.proj_apply, Finset.restrict]
  exact (Finset.sum_coe_sort c.support (fun i => c i * X i ω)).symm

/-- Two families of linear combinations of the coordinates of a real Gaussian process that are pairwise
uncorrelated are independent. -/
theorem indepFun_of_mem_span_of_covariance_eq_zero {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    {A : S → Ω → ℝ} {B : S' → Ω → ℝ} (hA : ∀ s, A s ∈ Submodule.span ℝ (Set.range X))
    (hB : ∀ t, B t ∈ Submodule.span ℝ (Set.range X)) (h : ∀ s t, cov[A s, B t; P] = 0) :
    IndepFun (fun ω s => A s ω) (fun ω t => B t ω) P := by
  have hAB : IsGaussianProcess (Sum.elim A B) P :=
    isGaussianProcess_of_mem_span hX fun s => by
      cases s with
      | inl s => exact hA s
      | inr t => exact hB t
  exact hAB.indepFun_of_covariance_eq_zero (fun s => hAB.aemeasurable (Sum.inl s))
    (fun t => hAB.aemeasurable (Sum.inr t)) h

/-- A linear combination of the coordinates of a real Gaussian process that is uncorrelated with each member of a
family of such combinations is independent of the family. -/
theorem indepFun_real_of_mem_span_of_covariance_eq_zero {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    {D : Ω → ℝ} {B : S' → Ω → ℝ} (hD : D ∈ Submodule.span ℝ (Set.range X))
    (hB : ∀ t, B t ∈ Submodule.span ℝ (Set.range X)) (h : ∀ t, cov[D, B t; P] = 0) :
    IndepFun D (fun ω t => B t ω) P := by
  have key := indepFun_of_mem_span_of_covariance_eq_zero hX (A := fun _ : Unit => D) (fun _ => hD) hB
    (fun _ t => h t)
  exact key.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (measurable_pi_apply ()) measurable_id

/-- The difference of two coordinates lies in the span of the coordinates. -/
theorem sub_mem_span_range (X : T → Ω → ℝ) (s t : T) : X s - X t ∈ Submodule.span ℝ (Set.range X) :=
  Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) (Submodule.subset_span ⟨t, rfl⟩)

/-- The difference of two coordinates, written pointwise, lies in the span of the coordinates. -/
theorem fun_sub_mem_span_range (X : T → Ω → ℝ) (s t : T) :
    (fun ω => X s ω - X t ω) ∈ Submodule.span ℝ (Set.range X) :=
  sub_mem_span_range X s t

/-! ### The exponential weight of a centered Gaussian variable -/

/-- The weight `exp (-γ² v / 2) exp (γ x) - 1`, whose mean under `N(0, v)` is zero. -/
noncomputable def expWeight (γ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  rexp (-(γ ^ 2 * v) / 2) * rexp (γ * x) - 1

theorem measurable_expWeight (γ : ℝ) (v : ℝ≥0) : Measurable (expWeight γ v) := by
  unfold expWeight
  fun_prop

theorem integrable_expWeight (γ : ℝ) (v : ℝ≥0) : Integrable (expWeight γ v) (gaussianReal 0 v) :=
  ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) γ).const_mul _).sub (integrable_const _)

/-- The exponential weight has mean zero under `N(0, v)`. -/
theorem integral_expWeight_gaussianReal (γ : ℝ) (v : ℝ≥0) : ∫ x, expWeight γ v x ∂(gaussianReal 0 v) = 0 := by
  unfold expWeight
  rw [integral_sub ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) γ).const_mul _) (integrable_const _),
    integral_const_mul, GaussTail.integral_exp_mul_gaussianReal_zero, ← Real.exp_add]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have : -(γ ^ 2 * (v : ℝ)) / 2 + v * γ ^ 2 / 2 = 0 := by ring
  rw [this, Real.exp_zero, sub_self]

/-- The exponential weight has second moment `exp (γ² v) - 1` under `N(0, v)`. -/
theorem integral_expWeight_sq_gaussianReal (γ : ℝ) (v : ℝ≥0) :
    ∫ x, expWeight γ v x ^ 2 ∂(gaussianReal 0 v) = rexp (γ ^ 2 * v) - 1 := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) γ
  have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (2 * γ)
  have hpt : ∀ x : ℝ, expWeight γ v x ^ 2 =
      rexp (-(γ ^ 2 * v)) * rexp (2 * γ * x) - 2 * rexp (-(γ ^ 2 * v) / 2) * rexp (γ * x) + 1 := by
    intro x
    have e1 : rexp (-(γ ^ 2 * v)) = rexp (-(γ ^ 2 * v) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have e2 : rexp (2 * γ * x) = rexp (γ * x) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    unfold expWeight
    rw [e1, e2]
    ring
  have i2 : Integrable (fun x : ℝ => rexp (-(γ ^ 2 * v)) * rexp (2 * γ * x)) (gaussianReal 0 v) := h2.const_mul _
  have i1 : Integrable (fun x : ℝ => 2 * rexp (-(γ ^ 2 * v) / 2) * rexp (γ * x)) (gaussianReal 0 v) :=
    h1.const_mul _
  have i3 : Integrable (fun x : ℝ => rexp (-(γ ^ 2 * v)) * rexp (2 * γ * x) -
      2 * rexp (-(γ ^ 2 * v) / 2) * rexp (γ * x)) (gaussianReal 0 v) := i2.sub i1
  simp_rw [hpt]
  rw [integral_add i3 (integrable_const _), integral_sub i2 i1, integral_const_mul, integral_const_mul,
    GaussTail.integral_exp_mul_gaussianReal_zero, GaussTail.integral_exp_mul_gaussianReal_zero,
    mul_assoc 2, ← Real.exp_add, ← Real.exp_add]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have a1 : -(γ ^ 2 * (v : ℝ)) + v * (2 * γ) ^ 2 / 2 = γ ^ 2 * v := by ring
  have a2 : -(γ ^ 2 * (v : ℝ)) / 2 + v * γ ^ 2 / 2 = 0 := by ring
  rw [a1, a2, Real.exp_zero]
  ring

variable {D : Ω → ℝ} {v : ℝ≥0}

/-- The exponential weight of a centered Gaussian random variable has mean zero. -/
theorem integral_expWeight (hD : HasLaw D (gaussianReal 0 v) P) (γ : ℝ) :
    ∫ ω, expWeight γ v (D ω) ∂P = 0 := by
  have h := hD.integral_comp (measurable_expWeight γ v).aestronglyMeasurable
  rw [integral_expWeight_gaussianReal] at h
  exact h

/-- The exponential weight of a centered Gaussian random variable of variance `v` has second moment
`exp (γ² v) - 1`. -/
theorem integral_expWeight_sq (hD : HasLaw D (gaussianReal 0 v) P) (γ : ℝ) :
    ∫ ω, expWeight γ v (D ω) ^ 2 ∂P = rexp (γ ^ 2 * v) - 1 := by
  have h := hD.integral_comp (f := fun x => expWeight γ v x ^ 2)
    ((measurable_expWeight γ v).pow_const 2).aestronglyMeasurable
  rw [integral_expWeight_sq_gaussianReal] at h
  exact h

variable {β : Type*} [MeasurableSpace β] {Y : Ω → β}

/-- Martingale orthogonality: if the centered Gaussian variable `D` is independent of `Y`, then any function of `Y`
is orthogonal to the exponential weight of `D`. No integrability of `F ∘ Y` is needed. -/
theorem integral_mul_expWeight_eq_zero (hD : HasLaw D (gaussianReal 0 v) P) (hY : AEMeasurable Y P)
    (hind : IndepFun Y D P) {F : β → ℝ} (hF : Measurable F) (γ : ℝ) :
    ∫ ω, F (Y ω) * expWeight γ v (D ω) ∂P = 0 := by
  have hi : IndepFun (F ∘ Y) (expWeight γ v ∘ D) P := hind.comp hF (measurable_expWeight γ v)
  have h := hi.integral_mul_eq_mul_integral (hF.comp_aemeasurable hY).aestronglyMeasurable
    ((measurable_expWeight γ v).comp_aemeasurable hD.aemeasurable).aestronglyMeasurable
  have h0 : ∫ ω, (expWeight γ v ∘ D) ω ∂P = 0 := integral_expWeight hD γ
  rw [h0, mul_zero] at h
  exact h

/-- Second moment: if the centered Gaussian variable `D` of variance `v` is independent of `Y`, then
`E[F(Y)² W²] = E[F(Y)²] (exp (γ² v) - 1)` for the exponential weight `W` of `D`. -/
theorem integral_sq_mul_expWeight_sq (hD : HasLaw D (gaussianReal 0 v) P) (hY : AEMeasurable Y P)
    (hind : IndepFun Y D P) {F : β → ℝ} (hF : Measurable F) (γ : ℝ) :
    ∫ ω, F (Y ω) ^ 2 * expWeight γ v (D ω) ^ 2 ∂P = (∫ ω, F (Y ω) ^ 2 ∂P) * (rexp (γ ^ 2 * v) - 1) := by
  have hF2 : Measurable fun y => F y ^ 2 := hF.pow_const 2
  have hW2 : Measurable fun x => expWeight γ v x ^ 2 := (measurable_expWeight γ v).pow_const 2
  have hi : IndepFun ((fun y => F y ^ 2) ∘ Y) ((fun x => expWeight γ v x ^ 2) ∘ D) P := hind.comp hF2 hW2
  have h := hi.integral_mul_eq_mul_integral (hF2.comp_aemeasurable hY).aestronglyMeasurable
    (hW2.comp_aemeasurable hD.aemeasurable).aestronglyMeasurable
  have h0 : ∫ ω, ((fun x => expWeight γ v x ^ 2) ∘ D) ω ∂P = rexp (γ ^ 2 * v) - 1 := integral_expWeight_sq hD γ
  rw [h0] at h
  exact h

/-- The product form of `integral_sq_mul_expWeight_sq`: `E[(F(Y) W)²] = E[F(Y)²] (exp (γ² v) - 1)`. -/
theorem integral_mul_expWeight_sq (hD : HasLaw D (gaussianReal 0 v) P) (hY : AEMeasurable Y P)
    (hind : IndepFun Y D P) {F : β → ℝ} (hF : Measurable F) (γ : ℝ) :
    ∫ ω, (F (Y ω) * expWeight γ v (D ω)) ^ 2 ∂P = (∫ ω, F (Y ω) ^ 2 ∂P) * (rexp (γ ^ 2 * v) - 1) := by
  simp_rw [mul_pow]
  exact integral_sq_mul_expWeight_sq hD hY hind hF γ

end LatticeProb.GaussIndep
