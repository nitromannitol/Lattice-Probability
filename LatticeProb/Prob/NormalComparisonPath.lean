/-
# Normal comparison (Li--Shao): the smart path, entries, definiteness, derivative

Route: `scratch/pk/normalcompare-route.md`, item 2.  The smart path
`S_t = (1 - t) • (v • 1) + t • S` of `LatticeProb/Prob/NormalComparison.lean` joins the product
law `v • 1` at `t = 0` to the covariance `S` at `t = 1`.  This file lands the facts about the
path that the differentiation of the orthant probability (route item 3) and the final assembly
(route item 8) consume.

* Entries: the off-diagonal entry is `t * S i j`; the diagonal entry is
  `(1 - t) * v + t * S i i`; in closed form `S_t i j = c + t * (S i j - c)` with
  `c = (v • 1) i j`, affine in `t`.
* Definiteness: for `t ∈ [0,1]`, `v ≥ 0`, `S` positive semidefinite, `S_t` is positive
  semidefinite (`PosSemidef.one`, `PosSemidef.smul`, `PosSemidef.add`).  For `v > 0` and
  `t ∈ [0,1)` it is positive definite (`PosDef.one`, `PosDef.smul`, `PosDef.add_posSemidef`),
  the weight `(1 - t) v` on the identity being strictly positive.
* Derivative: each entry of the path is affine in `t`, hence `HasDerivAt` with derivative
  `S i j - (v • 1) i j` (so `S i j` off the diagonal, and `0` on the diagonal when `S` has
  constant diagonal `v`), and continuous in `t`.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonBoundary

-- The smart-path lemmas of this route item are provided by `NormalComparisonBoundary`.
