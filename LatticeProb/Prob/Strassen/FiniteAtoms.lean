module

/- # Exact atom marginals of a coupling of finite weighted laws

Disjoint singleton fibers recover both marginals. Finite measure bounds and nonnegative weights then identify their real atom sums.
-/

public import LatticeProb.Prob.Strassen.FiniteLaw

@[expose] public section



open MeasureTheory
open scoped BigOperators

namespace LatticeProb.StrassenAux

variable {P X : Type*} [Fintype P] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Summing the disjoint first-coordinate singleton fibers gives the second marginal when the first coordinate is supported on the finite image. -/
theorem sum_pair_singleton_eq_snd (π : Measure (X × X)) (f : P → X)
    (hf : Function.Injective f) (y : X)
    (hrange : ∀ᵐ z ∂π, z.1 ∈ Set.range f) :
    (∑ x, π {(f x, y)}) = π (Prod.snd ⁻¹' {y}) := by
  classical
  have hpair : Function.Injective (fun x => (f x, y)) := by
    intro x x' h
    exact hf (congrArg Prod.fst h)
  rw [sum_measure_singleton_range π _ hpair]
  have hset : Set.range (fun x => (f x, y)) =
      (Prod.fst ⁻¹' Set.range f) ∩ (Prod.snd ⁻¹' {y}) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, rfl⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, hy⟩
      exact ⟨x, Prod.ext hx hy.symm⟩
  rw [hset]
  exact Measure.measure_inter_eq_of_ae (s := Prod.snd ⁻¹' {y})
    (t := Prod.fst ⁻¹' Set.range f) hrange

/-- Summing the disjoint second-coordinate singleton fibers gives the first marginal when the second coordinate is supported on the finite image. -/
theorem sum_pair_singleton_eq_fst (π : Measure (X × X)) (f : P → X)
    (hf : Function.Injective f) (y : X)
    (hrange : ∀ᵐ z ∂π, z.2 ∈ Set.range f) :
    (∑ x, π {(y, f x)}) = π (Prod.fst ⁻¹' {y}) := by
  classical
  have hpair : Function.Injective (fun x => (y, f x)) := by
    intro x x' h
    exact hf (congrArg Prod.snd h)
  rw [sum_measure_singleton_range π _ hpair]
  have hset : Set.range (fun x => (y, f x)) =
      (Prod.snd ⁻¹' Set.range f) ∩ (Prod.fst ⁻¹' {y}) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, rfl⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, hy⟩
      exact ⟨x, Prod.ext hy.symm hx⟩
  rw [hset]
  exact Measure.measure_inter_eq_of_ae (s := Prod.fst ⁻¹' {y})
    (t := Prod.snd ⁻¹' Set.range f) hrange

/-- **Exact finite atom row.** The real singleton masses of a finite coupling sum to the prescribed second marginal weight; finiteness and nonnegative weights justify taking `toReal`. -/
theorem finite_atom_row (π : Measure (X × X)) [IsFiniteMeasure π]
    (f : P → X) (hf : Function.Injective f) (p₁ p₂ : P → ℝ)
    (hp₁ : ∀ x, 0 ≤ p₁ x)
    (hfst : π.map Prod.fst = finiteLaw f p₂)
    (hsnd : π.map Prod.snd = finiteLaw f p₁) (x : P) :
    (∑ y, (π {(f y, f x)}).toReal) = p₁ x := by
  have hrange : ∀ᵐ z ∂π, z.1 ∈ Set.range f := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hfst]
    exact finiteLaw_ae_range f p₂
  rw [← ENNReal.toReal_sum (fun y _ => measure_ne_top π {(f y, f x)}),
    sum_pair_singleton_eq_snd π f hf _ hrange,
    ← Measure.map_apply measurable_snd (measurableSet_singleton _), hsnd,
    finiteLaw_singleton f hf p₁ x, ENNReal.toReal_ofReal (hp₁ x)]

/-- The real singleton masses of a finite coupling sum to the prescribed first marginal weight; finiteness and nonnegative weights justify taking `toReal`. -/
theorem finite_atom_column (π : Measure (X × X)) [IsFiniteMeasure π]
    (f : P → X) (hf : Function.Injective f) (p₁ p₂ : P → ℝ)
    (hp₂ : ∀ x, 0 ≤ p₂ x)
    (hfst : π.map Prod.fst = finiteLaw f p₂)
    (hsnd : π.map Prod.snd = finiteLaw f p₁) (y : P) :
    (∑ x, (π {(f y, f x)}).toReal) = p₂ y := by
  have hrange : ∀ᵐ z ∂π, z.2 ∈ Set.range f := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hsnd]
    exact finiteLaw_ae_range f p₁
  rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top π {(f y, f x)}),
    sum_pair_singleton_eq_fst π f hf _ hrange,
    ← Measure.map_apply measurable_fst (measurableSet_singleton _), hfst,
    finiteLaw_singleton f hf p₂ y, ENNReal.toReal_ofReal (hp₂ y)]

end LatticeProb.StrassenAux
