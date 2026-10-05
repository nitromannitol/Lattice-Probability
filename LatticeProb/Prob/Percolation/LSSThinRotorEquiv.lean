/-
# Exact equivalence of the library capstone with the frozen consumer body

The frozen consumer statement is an existential over the thinness threshold whose body uses the
`KDependent`, `IsIncreasing` and `bernoulliField (1/8)` predicates.  `LSSThinRotorMatch` repeats
those predicates verbatim (`consumerKDependent`, `consumerIsIncreasing`,
`consumerBernoulliField`), and `LSSThinCapstone` proves the corresponding conclusion in the
library vocabulary.

This module proves the exact statement equivalence between the two, so that a consumer holding
the library capstone may substitute it for the frozen-shaped statement directly.  Both
directions are given.  The statement is abstract inside the library, with no import of the rotor
development and no rotor file touched; the dense half remains an explicit hypothesis.
-/

import LatticeProb.Prob.Percolation.LSSThinCapstone

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- The frozen-shaped conclusion: the existential over `ε` with the consumer predicates.  This is
the body of the frozen thin domination statement, repeated abstractly in the library. -/
theorem frozenThinShape {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A :=
  thinLSS_capstone_consumer hp hdense

/-- The library conclusion: the existential over `ε` with the library predicates. -/
theorem libraryThinShape {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A :=
  thinLSS_capstone hp hdense

/-- **Exact statement equivalence with the frozen body.**  The library conclusion holds if and
only if the frozen-shaped conclusion holds, after the definitional identifications of the three
predicates.  A consumer may therefore substitute one for the other directly. -/
theorem libraryThinShape_iff_frozen :
    (∃ ε : ℝ, 0 < ε ∧
        ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
          (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
          ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
            μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A) ↔
      (∃ ε : ℝ, 0 < ε ∧
        ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
          (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
          ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
            μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A) :=
  thinLSS_capstone_iff_consumer

/-- **Substitution in the consumer direction.**  A holder of the library conclusion obtains the
frozen-shaped statement. -/
theorem libraryThinShape_to_frozen {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A :=
  frozenThinShape hp hdense

/-- **Substitution in the library direction.**  A holder of the frozen-shaped statement obtains
the library conclusion. -/
theorem frozen_to_libraryThinShape {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A :=
  libraryThinShape hp hdense

end LatticeProb.Percolation
