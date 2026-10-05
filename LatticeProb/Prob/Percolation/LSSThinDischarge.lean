/-
# The conditional discharge of the frozen thin statement

This module composes the library capstone with the exact statement equivalence to the frozen
consumer body, producing one named conditional discharge: from the transported dense-lower
hypothesis at density `p < 1`, the exact frozen `Rotor.External.LSS` statement holds, phrased in
the consumer's own predicates.  A consumer may therefore discharge its frozen hypothesis by
supplying only the dense half.

The statement is abstract inside the library, with no import of the rotor development and no
rotor file touched.  No domination statement is proved and no `Prop` is frozen.
-/

import LatticeProb.Prob.Percolation.LSSThinRotorEquiv

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- **The conditional discharge of the frozen thin statement.**  From the transported dense
domination hypothesis at density `p < 1`, there is `ε > 0` such that every probability
`2`-dependent planar field whose one-site probability is at most `2ε` satisfies the thin
domination bound on increasing events.  This is the body of the frozen consumer statement, with
`KDependent`, `IsIncreasing` and `bernoulliField (1/8)` read in the consumer vocabulary.

The proof is the composition `libraryThinShape_iff_frozen.mp (thinLSS_capstone hp hdense)`: the
capstone yields the library-shaped conclusion, and the equivalence converts it to the frozen
shape.  `ε` is uniform over the field law. -/
theorem rotorThin_discharge {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A :=
  libraryThinShape_iff_frozen.mp (thinLSS_capstone hp hdense)

/-- The same discharge with the witness made explicit.  The threshold is `(1 - p) / 2`, so the
hypothesis `p < 1` is exactly the nonemptiness of the thin regime. -/
theorem rotorThin_discharge_witness {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    0 < (1 - p) / 2 ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ((1 - p) / 2))) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A := by
  refine ⟨by linarith, ?_⟩
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  rw [consumerKDependent_iff] at hKD
  rw [consumerIsIncreasing_iff] at hinc
  rw [consumerBernoulliField_eq]
  exact thinPlanar_of_dense (p := p) (ε := (1 - p) / 2)
    (by linarith) (by linarith) hdense hKD hsite hA hinc

end LatticeProb.Percolation
