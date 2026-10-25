module

/-
# Finite weighted laws and order encodings

Finite real weights are sent to their exact scaled Dirac law. A finite poset is
encoded by its principal lower sets in a finite Boolean cube.

Finite weighted Dirac sums give literal atom laws. Encoding principal lower sets in a Boolean cube preserves and reflects the original partial order.
-/

public import LatticeProb.Prob.Strassen.Defs

@[expose] public section



open MeasureTheory
open scoped BigOperators

namespace LatticeProb.StrassenAux

variable {P X : Type*} [Fintype P] [MeasurableSpace X]

/-- The law of an encoded finite random variable with its original real weights. -/
noncomputable def finiteLaw (f : P → X) (p : P → ℝ) : Measure X :=
  ∑ x, ENNReal.ofReal (p x) • Measure.dirac (f x)

/-- The mass of a measurable set under the finite weighted Dirac sum is the sum of the weights of its indexed atoms. -/
theorem finiteLaw_apply (f : P → X) (p : P → ℝ) (A : Set X)
    (hA : MeasurableSet A) :
    finiteLaw f p A = ∑ x, Set.indicator (f ⁻¹' A) (fun x => ENNReal.ofReal (p x)) x := by
  classical
  unfold finiteLaw
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hA]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x ∈ A <;> simp [hx]

/-- For nonnegative weights, taking `ofReal` commutes with the finite sum over an event. -/
theorem sum_indicator_ofReal_eq (p : P → ℝ) (hp : ∀ x, 0 ≤ p x) (A : Set P) :
    (∑ x, Set.indicator A (fun x => ENNReal.ofReal (p x)) x) =
      ENNReal.ofReal (∑ x, Set.indicator A p x) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  · intro x _
    by_cases hx : x ∈ A <;> simp [hx, hp x]

/-- **Finite weighted probability law.** Nonnegative weights summing to one make the finite Dirac sum a probability measure. -/
theorem isProbabilityMeasure_finiteLaw (f : P → X) (p : P → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    IsProbabilityMeasure (finiteLaw f p) := by
  constructor
  rw [finiteLaw_apply _ _ _ MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x), hsum, ENNReal.ofReal_one]

/-- An injective atom map makes the mass of its indexed singleton equal to the nonnegative-real extension of the corresponding weight. -/
theorem finiteLaw_singleton [MeasurableSingletonClass X] (f : P → X)
    (hf : Function.Injective f) (p : P → ℝ) (x : P) :
    finiteLaw f p {f x} = ENNReal.ofReal (p x) := by
  classical
  rw [finiteLaw_apply _ _ _ (measurableSet_singleton _)]
  have heq : f ⁻¹' {f x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf.eq_iff]
  rw [heq]
  simp

/-- The finite weighted law is supported almost surely on the image of its atom map. -/
theorem finiteLaw_ae_range [MeasurableSingletonClass X] (f : P → X) (p : P → ℝ) :
    ∀ᵐ x ∂finiteLaw f p, x ∈ Set.range f := by
  classical
  rw [ae_iff]
  change finiteLaw f p (Set.range f)ᶜ = 0
  rw [finiteLaw_apply _ _ _ (Set.finite_range f).measurableSet.compl]
  apply Finset.sum_eq_zero
  intro x _
  simp

/-- For an injective finite map, the sum of the singleton masses equals the mass of its image. -/
theorem sum_measure_singleton_range [MeasurableSingletonClass X] (μ : Measure X)
    (f : P → X) (hf : Function.Injective f) :
    (∑ x, μ {f x}) = μ (Set.range f) := by
  classical
  have hr : (↑(Finset.univ.image f) : Set X) = Set.range f := by
    ext x
    simp
  rw [← hr, ← sum_measure_singleton, Finset.sum_image]
  exact fun x _ y _ h => hf h

/-- The principal lower-set encoding of a finite poset into a Boolean cube. -/
noncomputable def orderCode [PartialOrder P] (x : P) : Fin (Fintype.card P) → Bool := by
  classical
  exact fun i => decide ((Fintype.equivFin P).symm i ≤ x)

/-- The principal-lower-set Boolean encoding preserves the order. -/
theorem orderCode_mono [PartialOrder P] {x y : P} (hxy : x ≤ y) :
    ∀ i, orderCode x i = true → orderCode y i = true := by
  classical
  intro i hi
  simp only [orderCode, decide_eq_true_eq] at hi ⊢
  exact hi.trans hxy

/-- Pointwise comparison of the Boolean encodings reflects the original order. -/
theorem le_of_orderCode [PartialOrder P] {x y : P}
    (h : ∀ i, orderCode x i = true → orderCode y i = true) : x ≤ y := by
  classical
  have hx : orderCode x (Fintype.equivFin P x) = true := by
    simp [orderCode]
  have hy := h (Fintype.equivFin P x) hx
  simpa only [orderCode, Equiv.symm_apply_apply, decide_eq_true_eq] using hy

/-- The principal-lower-set Boolean encoding of a finite partial order is injective. -/
theorem orderCode_injective [PartialOrder P] : Function.Injective (orderCode (P := P)) := by
  intro x y h
  apply le_antisymm
  · apply le_of_orderCode
    intro i hi
    rwa [← h]
  · apply le_of_orderCode
    intro i hi
    rwa [h]

end LatticeProb.StrassenAux
