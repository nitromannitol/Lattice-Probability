import LatticeProb.Walk.Harnack.G1_Basics
import LatticeProb.Walk.Harnack.G2_Dirichlet
import LatticeProb.Walk.Harnack.G3_GreenEstimates
import LatticeProb.Walk.Harnack.G4_SmallR

/-!
# The Harnack inequality for nonnegative harmonic functions on a box of `ℤ^d`

Aggregator for the child modules of this directory, which together prove `harnack` (in
`G4_SmallR`): for `d ≥ 1` there is `C > 0` such that for every `R ≥ 1` and every `u : Site d → ℝ`
that is nonnegative on `box d (2R)` and harmonic on `box d (2R-1)` (`nbrSum u x = 2d u x`), one
has `u x ≤ C u y` for all `x, y ∈ box d R`.

Route (balayage / Riesz decomposition, Barlow, *Random Walks and Heat Kernels on Graphs*, §7).
Write `B = box (2R-1)`, `K = box (R + R/2)`, and let `v` be the Dirichlet extension of `u|K`
(`G2_Dirichlet`) that is harmonic on `B \ K` and `0` off `B`. The minimum principle gives `v ≤ u`,
so the charge `ν = 2d·v − nbrSum v ≥ 0` lives on the shell `∂_in K`, and `u(x) = ∑_{y ∈ shell}
g_B(x,y) ν(y)` on `box R` (`G3_GreenEstimates`). The Harnack inequality then follows from the
two-sided bound `g_B(x,y) ≍ R^{2-d}` uniformly for `x ∈ box R`, `y ∈ shell`, which is
`LatticeProb.GreenTwoSided.killedGreenReal_{le,ge}_box`. For small `R < 4` the neighbour chain
`u(x ± e_i) ≤ 2d·u(x)` gives `u x ≤ (2d)^{2Rd} u y` (`G4_SmallR`).

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
