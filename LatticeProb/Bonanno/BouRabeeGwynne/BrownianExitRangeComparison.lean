/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitRangeComparison at commit fdb5cad; selected declaration; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionRange
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel
import Mathlib.Topology.MetricSpace.Thickening

/-! Exit-time comparisons control every point of the original stopped curve. -/

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma mem_closure_of_le_continuousExitTime {d : ℕ} {V : Set (Euc d)}
    (hV : IsOpen V) {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ V)
    (hfinite : continuousExitTime V z ω ≠ ∞) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime V z ω) : z + ω t ∈ closure V := by
  have ht' : t ≤ (continuousExitTime V z ω).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hfinite] using ht
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianRepresentative V z ω ht'
  exact hu ▸ stoppedBrownianRepresentative_mem_closure hV hstart hfinite u


end BouRabeeGwynne
