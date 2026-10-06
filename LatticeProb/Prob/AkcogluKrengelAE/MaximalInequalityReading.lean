import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCore
import LatticeProb.Prob.AkcogluKrengelAE.UpperBound
import LatticeProb.Prob.AkcogluKrengelAE.Assembly
import LatticeProb.Prob.AkcogluKrengel

/-!
# Reading of the multiparameter maximal-inequality machinery

The modules considered are
`LatticeProb/Prob/AkcogluKrengelAE/{MaximalInequalityCore,MaximalInequalityCovering,
MaximalInequalityDyadic,MaximalInequalityPartition,UpperBound}.lean`.

## What the directory does prove

* `LatticeProb.measureReal_exists_heavy_le_akMaxConst_mul_div`
  (`MaximalInequalityCore.lean:443`) is a genuine multiparameter maximal inequality, but for the
  **anchored-cube** set function `R (latticeCube d k)`: for a stationary, monotone, subadditive,
  bounded `R` with `∫ R (cube N) ≤ ρ N^d`,
  `μ.real {ω | ∃ k ≥ 1, α k^d < R (cube k) ω} ≤ akMaxConst d * ρ / α`.
  Its finite-`N` form is `measureReal_bad_le_K_le_akMaxConst_div_mul_pow_div_pow`
  (`MaximalInequalityCore.lean:329`).
* `LatticeProb.cubeRatio_le_gridAvg_add_defect` (`UpperBound.lean:103`) is the cube **tiling** bound:
  `cubeRatio f n ≤ gridAvg (τ (m • ·)) (cubeRatio f m) (n/m) + C (1 - (n/m*m)^d/n^d)`.  With
  `ae_limsup_cubeRatio_le` (`:171`) and `exists_ae_tendsto_gridAvg_smul_cubeRatio` (`:231`) it gives
  the a.e. theorem for **cubes**.
* `LatticeProb.akcoglu_krengel_mean` (`AkcogluKrengel.lean:730`) is the mean (`L¹`) multiparameter
  ergodic theorem along cubes; `LatticeProb.akcoglu_krengel` (`Assembly.lean:375`) is its a.e.
  subadditive form.

## What is missing for the anchored **box** theorem

Every statement above is indexed by `latticeCube d k` (all sides equal).  The anchored-box theorem
`AnchoredBoxErgodic d` needs `∏ᵢ [0, ⌈N cᵢ⌉)` with **coordinate-dependent** sides.  The cube tiling
bound has no box analogue, and the maximal inequality controls `sup_k R (cube k)` at one point, not
the sup over the tiles of a rectangular partition.  The exact missing statement is the box maximal
inequality: for every bounded measurable `h` with `∫ h = 0` and every `c ≥ 0`, `ω ↦ sup over the
tiling cubes of the partial-grid average` is controlled in `L¹`.  With it the anchored-box theorem
follows from `akcoglu_krengel_mean` (the density half) by dominated convergence; without it, the
number of tiles `(N/s)^d` defeats the pointwise cube theorem.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

-- The cube maximal inequality (anchored cubes only).
#check @LatticeProb.measureReal_exists_heavy_le_akMaxConst_mul_div
#check @LatticeProb.measureReal_bad_le_K_le_akMaxConst_div_mul_pow_div_pow
-- The cube tiling / grid bound.
#check @LatticeProb.cubeRatio_le_gridAvg_add_defect
#check @LatticeProb.ae_limsup_cubeRatio_le
#check @LatticeProb.exists_ae_tendsto_gridAvg_smul_cubeRatio
-- The mean and a.e. subadditive multiparameter theorems.
#check @LatticeProb.akcoglu_krengel_mean
#check @LatticeProb.akcoglu_krengel
-- The anchored box / rectangle targets.
#check @LatticeProb.AnchoredBoxErgodic
#check @LatticeProb.RectangleErgodic_of_AnchoredBox

end LatticeProb
