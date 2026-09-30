import Mathlib
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.Ball

/-!
# The asymptotics of the lattice Green function and potential kernel

The classical expansion of the Green function of the simple random walk on `ℤ^d`, from
Lawler and Limic, *Random Walk: A Modern Introduction*, Theorem 4.3.1 for `d ≥ 3` and
Theorem 4.4.4 for `d = 2`.

For `d ≥ 3` the Green function `G(x) = ∑_j P^j(0, x)` is
`2 / ((d - 2) ω_d) · |x|^{2-d} + O(|x|^{-d})`, where `ω_d` is the volume of the unit ball
of `ℝ^d`. For `d = 2` the partial sums `∑_{j<M} [P^j(0,0) - P^j(0,x)]` converge, for every
`x`, to the potential kernel `b(x)`, and `b(x) = (2/π) log |x| + κ + O(|x|^{-2})` for a
constant `κ`.

The statement is recorded here as a proposition so that a formalization citing the
expansion can carry it as an explicit hypothesis. The gradient estimate, their
Corollary 4.3.3, is not part of it.
-/

open MeasureTheory Filter Topology

namespace LatticeProb.External

/-- **The lattice Green function and potential kernel asymptotics** (Lawler–Limic,
Theorems 4.3.1 and 4.4.4), in dimension `d`. For `d = 2`: the partial sums
`srwGreen 2 M 0 - srwGreen 2 M x` converge to a kernel `b x`, and
`b x = (2/π) log |x| + κ + O(|x|^{-2})`. For `d ≥ 3`: the Green function `srwGreenInf d x`
is `2 / ((d - 2) ω_d) |x|^{2-d} + O(|x|^{-d})`, with `ω_d` the volume of the unit ball. -/
def PotentialKernelAsymptotics (d : ℕ) : Prop :=
  (d = 2 →
    ∃ b : Site 2 → ℝ,
      (∀ x, Tendsto (fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M x) atTop (𝓝 (b x))) ∧
      ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
        |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ C * euclidNorm x ^ (-2 : ℝ)) ∧
  (3 ≤ d →
    ∃ C R : ℝ, 1 ≤ R ∧ ∀ x : Site d, R ≤ euclidNorm x →
      |srwGreenInf d x
          - 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
            * euclidNorm x ^ (2 - (d : ℝ))|
        ≤ C * euclidNorm x ^ (-(d : ℝ)))

end LatticeProb.External
