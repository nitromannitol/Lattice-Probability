import LatticeProb.Probability.Percolation.EdgeCrossing
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWProofs

/-!
# Critical square crossing probability

The probability of a horizontal crossing of an inclusive square under the critical
edge-indexed Bernoulli bond law is at least one half.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

namespace EdgeCrossing

/-- At parameter one half, the probability of crossing an inclusive square is at least one half. -/
theorem half_le_square_crossing (n : ℕ) :
    (1 / 2 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real (crossing n n) := by
  rw [crossing_probability]
  exact half_le_crossingProb_self crossingProb_half_succ_self_holds n

end EdgeCrossing
