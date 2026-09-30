import LatticeProb.Walk.GreenTwoSided.Kernels
import LatticeProb.Walk.GreenTwoSided.PointwiseBounds
import LatticeProb.Walk.GreenTwoSided.UpperBound
import LatticeProb.Walk.GreenTwoSided.LazyWalk
import LatticeProb.Walk.GreenTwoSided.FreeLazyKernel
import LatticeProb.Walk.GreenTwoSided.ChainingBound
import LatticeProb.Walk.GreenTwoSided.LowerBound

/-!
# Two-sided bounds for the killed Green function of a box in `ℤ^d`

Aggregator for the two public results proved in the child modules of this directory, for all
`d ≥ 1`. Normalization: `Graph.killedGreenReal (lattice d) B x y = (∑' k, killedHeat k x y) /
(2d)` (`Network.killedGreenReal_eq_tsum`), i.e. expected visits to `y` before leaving `B`, over
`2d`.

Upper bound (`killedGreenReal_le_box`, in `UpperBound`): for `B ⊆ box d L` and `x ≠ y`, `r =
graphNorm (x - y)`, `g_B(x,y) ≤ C(L+1)^2 (r^{-d} + (L+1)^{-d})`, proved in the time domain from
the Gaussian heat-kernel bounds of `Kernels` and `PointwiseBounds` (no potential kernel,
uniform in `d`).

Lower bound (`killedGreenReal_ge_box`, in `LowerBound`): for `m ≤ Kρ`, `box d (m+ρ) ⊆ B`, `x, y
∈ box d m`, `g_B(x,y) ≥ c(K) ρ^{2-d}`, proved via the killed lazy walk of `LazyWalk`, the free
lazy kernel's near-diagonal lower bound of `FreeLazyKernel`, and the chaining argument of
`ChainingBound` (small `ρ` by a monotone lattice path).

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
