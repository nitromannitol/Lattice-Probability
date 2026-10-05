/-
# The existential shape of the frozen thin domination statement

The frozen consumer statement is an existential over the thinness threshold:
`∃ ε > 0, ∀ μ, μ a probability measure → μ is 2-dependent → every one-site probability of μ is at
most `2ε` → ∀ increasing `A`, `μ A ≤ bernoulliField(1/8) A``.  This module proves exactly that
existential/quantifier order inside the library, as an abstract theorem conditional on the dense
half.  Two forms are given: the first uses the library's planar predicates, the second the
consumer names (`consumerKDependent`, `consumerIsIncreasing`, `consumerBernoulliField`) that a
rotor consumer can identify with its own.

The threshold is produced explicitly as `ε = (1 - p) / 2` from the dense hypothesis at density
`p < 1`, so `p = 1 - 2ε`.  No domination statement is proved, no `Prop` is frozen, no rotor file
is touched, and nothing is claimed unconditionally.
-/

import LatticeProb.Prob.Percolation.LSSThinRotorMatch
import LatticeProb.Prob.Percolation.LSSThinConsumerShape

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- **The exact existential shape of the frozen statement, in the library vocabulary.**  If the
dense domination hypothesis holds at density `p < 1`, then there is `ε > 0` such that every
probability `2`-dependent planar field whose one-site probability is at most `2ε` is dominated on
increasing events by the product Bernoulli field of density `1/8`.  The `IsProbabilityMeasure`
hypothesis is an explicit arrow, matching the frozen quantifier order. -/
theorem exists_thinPlanar_explicit {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  obtain ⟨ε, hε, h⟩ := exists_thinPlanar_of_dense hp hdense
  exact ⟨ε, hε, fun μ hμ hKD hsite A hA hinc =>
    h μ hμ hKD hsite A hA hinc⟩

/-- **The exact existential shape in the consumer vocabulary.**  The same statement with the
consumer's `KDependent`, `IsIncreasing` and `bernoulliField (1/8)` names, so that a consumer can
apply it directly after the definitional identifications in `LSSThinRotorMatch`. -/
theorem exists_consumerThin_explicit {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A := by
  obtain ⟨ε, hε, h⟩ := exists_thinPlanar_explicit hp hdense
  refine ⟨ε, hε, fun μ hμ hKD hsite A hA hinc => ?_⟩
  rw [consumerKDependent_iff] at hKD
  rw [consumerIsIncreasing_iff] at hinc
  rw [consumerBernoulliField_eq]
  exact h μ hμ hKD hsite A hA hinc

/-- The explicit-threshold form of the same shape: a caller who has already fixed `ε` and knows
`p ≤ 1 - 2ε` gets the statement without reopening the existential. -/
theorem thinPlanar_explicit_of_dense {p ε : ℝ} (hε : 0 < ε) (hp : p ≤ 1 - 2 * ε)
    (hdense : DenseSevenEighths p) :
    ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
      (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
      ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
        μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  exact thinPlanar_of_dense (p := p) (ε := ε) hε.le hp hdense hKD hsite hA hinc

end LatticeProb.Percolation
