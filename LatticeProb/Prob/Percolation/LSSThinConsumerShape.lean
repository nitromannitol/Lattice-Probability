/-
# The thin-form domination statement in the consumer shape

The complement bridge yields a domination statement for a `2`-dependent planar field that is
thin, conditional on the dense half of Liggett--Schonmann--Stacey.  This module packages that
conditional result in the exact shape a consumer expects: there is `ε > 0` such that every
probability `2`-dependent field on `ℤ × ℤ` whose one-site probability is at most `2ε` is dominated
on increasing events by the product Bernoulli field of density `1/8`.

The carrier, the dependence predicate, the increasing events and the Bernoulli product field are
the planar ones already identified with their paper counterparts: `KDependentPlanar 2` is the
`ℓ^∞` finite-range predicate used by the rotor statement, `bernoulliFieldPlanar (1/8)` is the
product Bernoulli field of density `1/8`, and `StrassenAux.IsIncreasingSet` is closure under
increasing a `{0,1}`-field coordinatewise.

The dense half is an explicit hypothesis; no domination statement is proved here, no `Prop` is
frozen and nothing is claimed unconditionally about `Rotor.External.LSS`.
-/

import LatticeProb.Prob.Percolation.LSSThinPlanar

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Percolation

/-- **The conditional consumer-shape capstone.**  Assume the dense domination hypothesis
`DenseSevenEighths p` at some density `p < 1` on the planar carrier.  Then there is `ε > 0`
with `p = 1 - 2ε` such that every probability `2`-dependent planar field whose one-site
probability is at most `2ε` satisfies `μ A ≤ bernoulliField(1/8) A` for every measurable
increasing `A`.  This is the shape in which the rotor percolation argument consumes the thin LSS
input, with `ε` and the bound uniform over the field law. -/
theorem exists_thinPlanar_of_dense {p : ℝ} (hp : p < 1) (hdense : DenseSevenEighths p) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
        (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
        ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
          μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  refine ⟨(1 - p) / 2, by linarith, ?_⟩
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  exact thinPlanar_of_dense (p := p) (ε := (1 - p) / 2)
    (by linarith) (by linarith) hdense hKD hsite hA hinc

/-- The same capstone with the dense hypothesis left as an argument, so that a caller who has
already fixed the dense threshold `ε` recovers the statement directly. -/
theorem thinPlanar_of_dense_consumer {p ε : ℝ} (hε : 0 < ε) (hp : p ≤ 1 - 2 * ε)
    (hdense : DenseSevenEighths p) :
    ∀ (μ : Measure (PlanarCarrier → Bool)), IsProbabilityMeasure μ → KDependentPlanar 2 μ →
      (∀ z : PlanarCarrier, μ {ω | ω z = true} ≤ ENNReal.ofReal (2 * ε)) →
      ∀ A : Set (PlanarCarrier → Bool), MeasurableSet A → StrassenAux.IsIncreasingSet A →
        μ A ≤ bernoulliFieldPlanar (1 / 8) one_eighth_le_one A := by
  intro μ hμ hKD hsite A hA hinc
  haveI := hμ
  exact thinPlanar_of_dense (p := p) (ε := ε) hε.le hp hdense hKD hsite hA hinc

end LatticeProb.Percolation
