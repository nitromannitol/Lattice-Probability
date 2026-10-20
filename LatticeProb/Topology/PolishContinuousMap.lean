/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/PolishContinuousMap.lean.
-/
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Polish

/-!
# `C(X, Y)` is Polish

For `X` locally compact and second countable and `Y` Polish, the space `C(X, Y)` of continuous
maps with the compact-open topology (= topology of local uniform convergence) is Polish.

Everything is in mathlib: after choosing a complete metric on `Y`
(`TopologicalSpace.upgradeIsCompletelyMetrizable`), `C(X, Y)` carries the compact-convergence
uniformity, which is complete (`ContinuousMap.instCompleteSpaceOfCompactlyCoherentSpace`) and
countably generated (σ-compact `X`), hence completely metrizable
(`IsCompletelyMetrizableSpace.of_completeSpace_metrizable`), and `C(X, Y)` is separable
(`ContinuousMap.instSeparableSpace`, Topology/ContinuousMap/SecondCountableSpace.lean).
-/

namespace LatticeProb

/-- `C(X, Y)` (compact-open topology) is Polish for `X` locally compact second countable and
`Y` Polish. -/
theorem polishSpace_continuousMap (X Y : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [PolishSpace Y] :
    PolishSpace C(X, Y) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  infer_instance

end LatticeProb
