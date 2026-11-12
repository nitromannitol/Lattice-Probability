import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMean
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCore
import LatticeProb.Prob.AkcogluKrengelAE.Assembly
import LatticeProb.Prob.AkcogluKrengel

/-!
# The normalized anchored-box average

The maximal-inequality directory
proves a maximal inequality only for the **anchored-cube** set function
(`LatticeProb.measureReal_exists_heavy_le_akMaxConst_mul_div`,
`MaximalInequalityCore.lean:443`) and a cube tiling bound
(`LatticeProb.cubeRatio_le_gridAvg_add_defect`, `UpperBound.lean:103`).  Neither covers
coordinate-dependent boxes `∏ᵢ [0, ⌈N cᵢ⌉)`.  This module provides the normalized average
`anchoredBoxAvg` over such boxes.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average of `h` at scale `N`. -/
noncomputable def anchoredBoxAvg (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (τ x ω)


end LatticeProb
