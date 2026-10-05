import Mathlib

/-!
# The one-dimensional Berry-Esseen theorem: comparator challenge

Mathlib-only comparator challenge for the Berry-Esseen theorem for independent, centred,
non-identically distributed summands with finite third absolute moments,
`LatticeProb.berryEsseen_oneDim` in `LatticeProb/Prob/BerryEsseenOneDim.lean`.

Content: there is an absolute constant `C > 0` such that for every finite family of probability
laws `ν i` on `ℝ` with mean `0`, finite third absolute moments and total variance `V > 0`, the
distribution function of the sum of independent variables with these laws (the image of the product
measure under `y ↦ ∑ i, y i`) differs from the distribution function of `N(0, V)` by at most
`C ∑ᵢ ∫ |z|³ dνᵢ / V^{3/2}`, at every point.

Only Mathlib is imported, and no definition is needed: the law of the sum is written out as
`Measure.map (fun y => ∑ i, y i) (Measure.pi ν)`.  The sole intentional `sorry` is the proof of the
final theorem.

## Presentation deltas

The library names the law of the sum `LatticeProb.sumLaw ν`; the challenge writes out its body.
The library proves it with `C = 100`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProbAudit

/-- **Berry-Esseen in one dimension** for independent non-identical summands. -/
theorem berry_esseen_one_dim :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
        (∀ i, ∫ z, z ∂(ν i) = 0) →
        (∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i)) →
        0 < ∑ i, variance id (ν i) →
        ∀ x : ℝ,
          |((Measure.map (fun y : ι → ℝ => ∑ i, y i) (Measure.pi ν)) (Set.Iic x)).toReal -
              (gaussianReal 0 (∑ i, variance id (ν i)).toNNReal (Set.Iic x)).toReal|
            ≤ C * (∑ i, ∫ z, |z| ^ 3 ∂(ν i)) / (∑ i, variance id (ν i)) ^ ((3 : ℝ) / 2) := by
  sorry

end LatticeProbAudit
