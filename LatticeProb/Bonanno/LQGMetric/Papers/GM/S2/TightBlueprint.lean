/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightBlueprint at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.Moments.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.Algebra.Order.Field.GeomSum
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.MeasureTheory.Integral.CircleIntegral
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The Blueprint Props `Blueprint.GMS2_4a`, `GMS2_4b`, `GMS2_4c` (GM U:449–452, decision D14 =
DEC-A D-A3; constants before `(Ω, P, h)`, decision D56) follow from the proved
`GM.Tight.gm_S2_4a`, `gm_S2_4a_sep`, `gm_S2_4b`, `gm_S2_4c` (own proofs, D-A3) by rewriting the
events: `rK + z = scaleSet r z K`, `‖(ru + z) − (rv + z)‖ = r‖u − v‖`,
`𝔠_r e^{ξh_r(z)} = scaleFac`, and `setDist`/`internalDiam` as an infimum/supremum over pairs.
For `GMS2_4c`, an empty `U` (allowed by `IsPreconnected`) forces `K = ∅`, and the internal
diameter of the empty set is `0`.

`GMS2_4e` follows from `gm_S2_4e` (which assumes `DFGPSScaling` and `LMLem3_1a`, D14) by
compactness: on `B̄_r(z) × B̄_r(z)` the continuous `D_h` attains a maximum `< M`, while
`D_h(x, y) > M` for `x ∈ B_r(z)`, `y ∈ ∂B_{Rr}(z)`.

`GMS2_4d` follows from `gm_S2_4d` (the distance around the annulus, `ContMetric.aroundDist`, is at
most `A·D_h(x, y)` for all `x, y` on the two boundary circles): then `aroundDist ≤ A·D_h(∂B_{αr},
∂B_r) < (2A + 2)·D_h(∂B_{αr}, ∂B_r)` (the set distance is positive and finite), so some
disconnecting path in the annulus has length `≤ (2A + 2)·D_h(∂B_{αr}, ∂B_r)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric
namespace GM
namespace Tight

end Tight
end GM
end LQGMetric
