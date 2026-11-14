import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd

/-!
# Determination of finite measures by product tests

A finite measure on a finite product is determined by integrals of products of
bounded continuous functions of the individual coordinates.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BoundedContinuousFunction

namespace LatticeProb

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, HasOuterApproxClosed (E i)]

/-- Finite measures on a finite product are determined by products of bounded
continuous coordinate tests. -/
theorem measure_eq_of_integral_prod_boundedContinuousFunction_eq
    {μ ν : Measure (∀ i, E i)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : (i : ι) → E i →ᵇ ℝ,
      ∫ x, ∏ i, f i (x i) ∂μ = ∫ x, ∏ i, f i (x i) ∂ν) : μ = ν := by
  let e : (∀ i, E i) ≃ᵐ ((∀ i, E i) × PUnit) := MeasurableEquiv.prodPUnit.symm
  apply e.map_measurableEquiv_injective
  refine Measure.ext_of_integral_prod_mul_boundedContinuousFunction fun f g => ?_
  rw [integral_map_equiv, integral_map_equiv]
  change (∫ x, (∏ i, f i (x i)) * g PUnit.unit ∂μ) =
    ∫ x, (∏ i, f i (x i)) * g PUnit.unit ∂ν
  rw [integral_mul_const, integral_mul_const, h f]

end LatticeProb
