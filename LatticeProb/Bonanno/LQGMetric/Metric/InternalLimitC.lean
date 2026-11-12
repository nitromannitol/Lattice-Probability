/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.InternalLimitC at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.Order.Compact

/-!
# DFGPS Lemma 2.11: limits of internal metrics (`lem-internal-conv`)

**DFGPS Lemma 2.11** (Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first
passage percolation*,
arXiv:1905.00380, `lqg-metric-estimates-final.tex`:971–988). Let `V ⊂ ℂ` be open, `Dⁿ` continuous
length metrics on `ℂ` converging locally uniformly to a continuous metric `D`, and suppose
`Dⁿ(·,·;V̄)` converges (pointwise suffices) to a metric `D̃` on `V̄` inducing the Euclidean
topology. Then `D(·,·;V) = D̃(·,·;V)` (`ContMetric.internal_eq_of_tendsto_internal_closure`).

Proof, following DFGPS tex:980–988: for `u, v` near a point `z ∈ V`, the `Dⁿ`-distance from `u`
to `v` is smaller than the `Dⁿ`-distance from `u` to a small circle around `z`, uniformly for
large `n`; since `Dⁿ` is a length metric, `Dⁿ(u, v) = Dⁿ(u, v; V̄)`
(`ContMetric.eventually_internal_closure_eq`). Passing to the limit, `D = D̃` near every point
of `V`, so the identity `V → V` is a local isometry and preserves internal metrics
(`internalEDist_eq_of_isLocalIsometryOn`). Deviation from DFGPS: the hypotheses are weaker (the
lemma uses neither that `D`, `D̃` are length metrics nor uniform convergence of `Dⁿ(·,·;V̄)`);
DFGPS apply the lemma (tex:1013) to a `D` not yet known to be a length metric, which this version
covers. `U = ℂ` (the only case used, tex:1013, 1018).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

namespace ContMetric

theorem edist_pt (D : ContMetric) (z w : ℂ) :
    edist (D.pt z) (D.pt w) = ENNReal.ofReal (D.1 (z, w)) := edist_dist _ _

end ContMetric

end LQGMetric
