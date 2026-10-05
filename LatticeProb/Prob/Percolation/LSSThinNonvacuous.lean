/-
# Non-vacuity of the conditional discharge at a concrete witness

The conditional discharge `rotorThin_discharge` turns the dense domination hypothesis into the
frozen thin statement.  This module pairs that discharge with the concrete witness of
`denseHypothesis_witness`: the product Bernoulli field of density `7/8` is a legitimate
probability measure on the planar carrier that is `2`-dependent, has one-site probability `7/8`,
and satisfies the domination conclusion.  The witness shows the dense hypothesis is inhabited, so
the conditional discharge is not vacuous; and the discharge, instantiated at `p = 7/8`, is the
frozen-shaped statement.

The pairing is abstract inside the library, with no rotor import and no rotor file touched; no
domination statement is proved and no `Prop` is frozen.
-/

import LatticeProb.Prob.Percolation.LSSThinVacuity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- **The frozen thin statement is non-vacuous at the `7/8` witness.**  The product Bernoulli
field of density `7/8` is a legitimate probability measure on `ℤ × ℤ → Bool` that is
`2`-dependent, has every one-site probability `7/8`, and satisfies the domination conclusion; and
at that density the conditional discharge produces the frozen-shaped statement.  Together these
exhibit the frozen statement non-vacuously at that object. -/
theorem frozenStatement_nonvacuous :
    (∃ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν ∧ KDependentPlanar 2 ν ∧
        (∀ s : PlanarCarrier, ENNReal.ofReal (7 / 8) ≤ ν {ω | ω s = true}) ∧
        DenseLower (bernoulliFieldPlanar (7 / 8) seven_eighths_le_one) ν) ∧
      (DenseSevenEighths (7 / 8) →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
            (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
            ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
              μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A) := by
  refine ⟨?_, fun hdense => rotorThin_discharge (by norm_num) hdense⟩
  refine ⟨bernoulliFieldPlanar (7 / 8) seven_eighths_le_one, inferInstance,
    kDependentPlanar_bernoulliFieldPlanar 2 (7 / 8) seven_eighths_le_one, ?_, ?_⟩
  · intro s
    rw [bernoulliFieldPlanar_oneSite]
    norm_num
  · intro C _ _
    exact le_rfl

/-- The discharge at the concrete `7/8` witness, with the threshold `ε = 1/16` made explicit so
that `2ε = 7/8` matches the witness's one-site probability. -/
theorem frozenStatement_at_eighth (hdense : DenseSevenEighths (7 / 8)) :
    (0 : ℝ) < 1 / 16 ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → consumerKDependent 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (1 / 8)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → consumerIsIncreasing A →
          μ A ≤ consumerBernoulliField (1 / 8) one_eighth_le_one A := by
  obtain ⟨hpos, hbody⟩ := rotorThin_discharge_witness (p := (7 : ℝ) / 8) (by norm_num) hdense
  refine ⟨by norm_num, fun μ hμ hKD hsite A hA hinc => ?_⟩
  have hsite' : ∀ z : PlanarCarrier,
      μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ((1 - (7 : ℝ) / 8) / 2)) := by
    intro z
    rw [show 2 * ((1 - (7 : ℝ) / 8) / 2) = 1 / 8 by norm_num]
    exact hsite z
  exact hbody μ hμ hKD hsite' A hA hinc

end LatticeProb.Percolation
