/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.SLUMetricAPI
import LatticeProb.Bonanno.SLUFieldSupport
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6




 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF IsGFFPlusCont addConst affineComp circleAvg)

private theorem testTranslate_eq_testAffinePull_one (z : ℂ) (φ : LQGMetric.TestC) :
    testTranslate z φ = LQGMetric.testAffinePull 1 z φ := by
  ext x
  rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
  simp only [Complex.ofReal_one, div_one]
  rfl

 
theorem translateDist_eq_affineComp_one (z : ℂ) (g : DistC) :
    translateDist z g = affineComp 1 z g := by
  ext φ
  rw [LQGMetric.GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  exact congrArg g (testTranslate_eq_testAffinePull_one z φ)

 
end SupercriticalLQGUniqueness

