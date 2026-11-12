import Mathlib
import LatticeProb.LQG.CurveLengthLimit

/-!
# The length of a curve up to its endpoint, for parameters in `[0, 1)`

The form of `LatticeProb.LQG.IsEuclideanLengthMetric.curveLength_le_iSup_of_tendsto_of_mem_Icc` for a sequence
`aₙ ∈ [0, 1)` tending to `1`.
-/

open Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

/-- **The length of a curve up to its endpoint.** Let `D` be a Euclidean length metric, `p` continuous on `[0, 1]`
and `aₙ ∈ [0, 1)` with `aₙ → 1`. Then `len(p; D)` on `[0, 1]` is at most `sup_n len(p|[0, aₙ]; D)`. -/
theorem IsEuclideanLengthMetric.curveLength_le_iSup_of_tendsto {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {p : ℝ → ℂ} (hp : ContinuousOn p (Set.Icc 0 1)) {a : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n < 1) (ha : Filter.Tendsto a Filter.atTop (nhds 1)) :
    curveLength D p 0 1 ≤ ⨆ n, curveLength D p 0 (a n) :=
  hD.curveLength_le_iSup_of_tendsto_of_mem_Icc hp (fun n => ⟨ha0 n, (ha1 n).le⟩) ha

end LatticeProb.LQG
