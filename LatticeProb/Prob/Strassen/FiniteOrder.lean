module

/- # Monotone real atom couplings on finite posets

Encode the finite partial order in a Boolean cube, apply the proved monotone coupling theorem, and recover the exact real atom marginals.
-/

public import LatticeProb.Prob.Strassen.FiniteAtoms
public import LatticeProb.Prob.Strassen.LimitPassage

@[expose] public section



open MeasureTheory
open scoped BigOperators

namespace LatticeProb.StrassenAux

/-- **Finite partially ordered coupling.** Upper-set domination of finite probability weights gives a nonnegative real
matrix with exact marginals, total mass one, and order support. -/
theorem exists_monotone_matrix_of_upper_set_domination
    {P : Type*} [Fintype P] [PartialOrder P]
    (p₁ p₂ : P → ℝ) (hp₁ : ∀ x, 0 ≤ p₁ x) (hp₂ : ∀ x, 0 ≤ p₂ x)
    (hsum₁ : ∑ x, p₁ x = 1) (hsum₂ : ∑ x, p₂ x = 1)
    (hdom : ∀ A : Set P, IsUpperSet A →
      ∑ x, Set.indicator A p₁ x ≤ ∑ x, Set.indicator A p₂ x) :
    ∃ q : P → P → ℝ,
      (∀ x y, 0 ≤ q x y) ∧
      (∀ x, ∑ y, q x y = p₁ x) ∧
      (∀ y, ∑ x, q x y = p₂ y) ∧
      (∑ x, ∑ y, q x y) = 1 ∧
      (∀ x y, ¬ x ≤ y → q x y = 0) := by
  classical
  let f : P → (Fin (Fintype.card P) → Bool) := orderCode
  have hf : Function.Injective f := orderCode_injective
  let μ := finiteLaw f p₂
  let ν := finiteLaw f p₁
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_finiteLaw f p₂ hp₂ hsum₂
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_finiteLaw f p₁ hp₁ hsum₁
  have hdom' : ∀ A, MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A := by
    intro A hA hinc
    have hupper : IsUpperSet (f ⁻¹' A) := by
      intro x y hxy hx
      exact hinc (f x) (f y) hx (orderCode_mono hxy)
    change finiteLaw f p₁ A ≤ finiteLaw f p₂ A
    rw [finiteLaw_apply _ _ _ hA, finiteLaw_apply _ _ _ hA,
      sum_indicator_ofReal_eq p₁ hp₁, sum_indicator_ofReal_eq p₂ hp₂]
    exact ENNReal.ofReal_le_ofReal (hdom _ hupper)
  obtain ⟨π, hπ, hfst, hsnd, hsupp⟩ := exists_monotone_coupling μ ν hdom'
  letI : IsProbabilityMeasure π := hπ
  let q : P → P → ℝ := fun x y => (π {(f y, f x)}).toReal
  have hrow : ∀ x, ∑ y, q x y = p₁ x :=
    finite_atom_row π f hf p₁ p₂ hp₁ hfst hsnd
  have hcol : ∀ y, ∑ x, q x y = p₂ y :=
    finite_atom_column π f hf p₁ p₂ hp₂ hfst hsnd
  refine ⟨q, fun _ _ => ENNReal.toReal_nonneg, hrow, hcol, ?_, ?_⟩
  · simp only [hrow, hsum₁]
  · intro x y hnot
    have hnull : π {z | ¬ (∀ i, z.2 i = true → z.1 i = true)} = 0 :=
      ae_iff.mp hsupp
    have hatom : π {(f y, f x)} = 0 := by
      apply measure_mono_null _ hnull
      rintro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      intro h
      exact hnot (le_of_orderCode h)
    change (π {(f y, f x)}).toReal = 0
    rw [hatom, ENNReal.toReal_zero]

end LatticeProb.StrassenAux
