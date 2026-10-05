import LatticeProb.Prob.AkcogluKrengelAE.Defs
import LatticeProb.Prob.AkcogluKrengelAE.BoxCombinatorics
import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic
import LatticeProb.Prob.AkcogluKrengelAE.UpperBound
import LatticeProb.Prob.AkcogluKrengelAE.Defect
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityDyadic
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityPartition
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCovering
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCore
import LatticeProb.Prob.AkcogluKrengelAE.UnitScaleLowerBound
import LatticeProb.Prob.AkcogluKrengelAE.CoarseGraining
import LatticeProb.Prob.AkcogluKrengelAE.Assembly
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMaximal

/-!
# The almost-everywhere Akcoglu-Krengel subadditive ergodic theorem

The multiparameter subadditive ergodic theorem of Akcoglu and Krengel, along cubes: the almost
sure half.

A set function `f` on boxes of `ℤ^d`, stationary under a measure-preserving action `τ` of the
lattice, bounded by a multiple of the volume, and subadditive when a box splits into two boxes,
has a volume-normalised limit along the cubes `[0, n)^d` almost surely: `akcoglu_krengel` proves
`f (latticeCube d n) ω / n^d → L ω` for a.e. `ω`. The mean half is
`LatticeProb.akcoglu_krengel_mean` (`LatticeProb/Prob/AkcogluKrengel.lean`), proved there by a
multiparameter Fekete argument; the one-parameter theorem is `LatticeProb.Prob.Kingman`.

This file only imports its children, one per proof step, under `LatticeProb/Prob/AkcogluKrengelAE/`.

## Route

* Box combinatorics (`Defs`, `BoxCombinatorics`): splitting a box along one coordinate is an
  `IsBoxSplit`; hence `f` of a box is at most `f` of a nested box plus `C` times the volume
  difference, and `f` of the cube `[0, k m)^d` is at most the sum of `f` over the `k^d` grid
  cubes of side `m`.
* A multiparameter pointwise ergodic theorem for bounded functions along cubes
  (`BoundedErgodic`), for any measure-preserving additive action `σ` of `ℤ^d`, by iterating the
  one-parameter Birkhoff theorem of the library one coordinate at a time. Boundedness makes the
  iteration elementary: if `g n → G` a.e. with `|g n| ≤ M`, then the Birkhoff averages of `g n`
  converge to the Birkhoff limit of `G`.
* Upper bound (`UpperBound`): applying the bounded ergodic theorem to the sublattice action
  `z ↦ τ (m • z)` and the grid bound gives the a.e. upper bound `limsup_n cubeRatio f n ≤ G_m`
  (`ae_limsup_cubeRatio_le`) for every `m`, with `∫ G_m = ∫ cubeRatio f m`
  (`integral_limsup_cubeRatio_le_integral_cubeRatio`).
* Lower bound (`Defect` through `Assembly`; DEEP): `∫ liminf_n cubeRatio f n ≥ inf_m ∫ cubeRatio
  f m` (`exists_integral_cubeRatio_le_integral_liminf_add`). The maximal inequality
  `measureReal_exists_heavy_le_akMaxConst_mul_div` bounds the probability that some cube `Q_k`
  (`k ≥ 1`) is `α k^d`-heavy by `akMaxConst d * ρ / α`, where `ρ` bounds the normalised means; it
  is proved by a dyadic covering argument: a heavy cube of side `k` is covered by a dyadic cell
  of side `2^j` with `2^j < 4 d k` (`heavy_dyCell_of_heavy_cube`), the cells are grouped into a
  pairwise disjoint maximal subfamily (`mul_card_biUnion_le_apply_dyBig_of_heavy`), and each
  heavy cell is covered by at least half of the offsets of a grid of side `2^J`
  (`pow_le_two_mul_card_filter_dyCell`), so the count of bad sites is controlled by the mean of
  the box sums (`card_filter_bad_le_akMaxConst_mul_avg_dyBig`).
* Assembly (`Assembly`): `∫ (limsup - liminf) ≤ 0` from the upper and lower bounds, so
  `limsup = liminf` a.e. (`liminf_cubeRatio_eq_limsup_cubeRatio_ae`), giving `akcoglu_krengel`.

Junk values: `latticeCube d 0 = ∅`, `(0 : ℝ)^d = 0` for `d ≥ 1`, `x / 0 = 0`; `bAvg T g 0 = 0`.
-/
