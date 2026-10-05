import Mathlib
import LatticeProb.Prob.BerryEsseenOneDim

/-!
# Solution: BerryEsseen

The challenge module `LatticeProbAudit/BerryEsseen/Challenge.lean` imports only Mathlib and states
the one-dimensional Berry-Esseen theorem with one intentional `sorry`.  This solution proves the
byte-identical statement by `LatticeProb.berryEsseen_oneDim`, whose statement is the challenge's
after unfolding `LatticeProb.sumLaw`.
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
  exact LatticeProb.berryEsseen_oneDim

end LatticeProbAudit
