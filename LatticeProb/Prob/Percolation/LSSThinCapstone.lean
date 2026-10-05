/-
# The conditional capstone: the library equivalent of the frozen thin conclusion

This module collects the thin-form complement bridge into a single capstone.  From the
transported dense-lower hypothesis at density `p < 1`, the library proves the exact existential
shape of the frozen consumer statement: there is `ε > 0` such that every probability
`2`-dependent planar field with one-site probability at most `2ε` is dominated on increasing
events by the product Bernoulli field of density `1/8`.  The statement is abstract, with no
import of the rotor development and no rotor file touched.

The capstone is given once in the library's planar vocabulary and once in the consumer
vocabulary, together with the equivalence of the two existential shapes.  The dense half remains
an explicit hypothesis; no domination statement is proved and no `Prop` is frozen.
-/

import LatticeProb.Prob.Percolation.LSSThinExistsShape

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- **The conditional capstone in the library vocabulary.**  From the transported dense-lower
hypothesis at density `p < 1`, there is `ε > 0` such that every probability `2`-dependent planar
field with one-site probability at most `2ε` satisfies the thin domination bound on increasing
events.  This is the library statement equivalent to the frozen consumer conclusion. -/
theorem thinLSS_capstone {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A :=
  exists_thinPlanar_explicit hp hdense

/-- **The conditional capstone in the consumer vocabulary.**  The same statement with the
consumer's `KDependent`, `IsIncreasing` and `bernoulliField (1/8)` names. -/
theorem thinLSS_capstone_consumer {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A :=
  exists_consumerThin_explicit hp hdense

/-- **The two existential shapes are equivalent.**  The library capstone and the consumer
capstone are interderivable after the definitional identifications of `LSSThinRotorMatch`. -/
theorem thinLSS_capstone_iff_consumer :
    (∃ ε : ℝ, 0 < ε ∧
        ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
          (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
          ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
            μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A) ↔
      (∃ ε : ℝ, 0 < ε ∧
        ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
          (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
          ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
            μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A) := by
  constructor
  · rintro ⟨ε, hε, hbody⟩
    refine ⟨ε, hε, fun μ hμ hKD hsite A hA hinc => ?_⟩
    rw [consumerKDependent_iff] at hKD
    rw [consumerIsIncreasing_iff] at hinc
    rw [consumerBernoulliField_eq]
    exact hbody μ hμ hKD hsite A hA hinc
  · rintro ⟨ε, hε, hbody⟩
    refine ⟨ε, hε, fun μ hμ hKD hsite A hA hinc => ?_⟩
    rw [← consumerKDependent_iff] at hKD
    rw [← consumerIsIncreasing_iff] at hinc
    rw [← consumerBernoulliField_eq]
    exact hbody μ hμ hKD hsite A hA hinc

end LatticeProb.Percolation
