/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.Disconnects
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LiminfLimsup
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCFun
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Normed.Module.Connected
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreC
import Mathlib.Topology.Metrizable.Basic
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3B
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36Conf
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLFPPMetricMeas
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.LFPP

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.LFPP
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def normalizedContLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) : ContMetric :=
  (lfppContMetric ξ φ φ.continuous).smulPos (a : ℝ)⁻¹
    (inv_pos.mpr a.property)

end SupercriticalLQGUniqueness.B2.DG20Lim
