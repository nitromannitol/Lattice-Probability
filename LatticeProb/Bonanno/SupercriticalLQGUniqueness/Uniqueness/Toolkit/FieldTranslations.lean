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

 
theorem map_eq_of_candidate_normalized {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsNormalizedWholePlaneGFF h P)
    (hh' : IsNormalizedWholePlaneGFF h' P') :
    P.map h = P'.map h' :=
  LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF
    (isNormalizedWholePlaneGFF_iff_old.mp hh)
    (isNormalizedWholePlaneGFF_iff_old.mp hh')

 
theorem map_affine_normalized_of_candidate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => addConst (affineComp r z (h ω))
      (-circleAvg (affineComp r z (h ω)) 1 0)) = P.map h :=
  LQGMetric.CircleAvg.map_affine_normalized
    (isNormalizedWholePlaneGFF_iff_old.mp hh) hr z

 
theorem normalized_translate_sub_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    IsNormalizedWholePlaneGFF
      (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) P := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have htrans : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  have hc : Measurable (fun ω => -circleAvg (h ω) 1 z) :=
    ((LQGMetric.measurable_circleAvg_left 1 z).comp hh.1.measurable).neg
  have hwhole := htrans.addConst hc
  apply isNormalizedWholePlaneGFF_iff_old.mpr
  refine ⟨hwhole, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 one_pos]
    with ω hca
  rw [hca, translateDist_eq_affineComp_one,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  ring

 
theorem map_normalized_translate_sub_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) :
    P.map (fun ω => addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) =
      P.map h := by
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  simp only [translateDist_eq_affineComp_one]
  exact LQGMetric.CircleAvg.map_affine_sub_circleAvg hold one_pos z

 
theorem ae_circleAvg_normalized_translate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      circleAvg (addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) r 0 =
        circleAvg (h ω) r z - circleAvg (h ω) 1 z := by
  have htrans : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 r.2]
    with ω hω
  rw [hω, translateDist_eq_affineComp_one,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  ring

 
end SupercriticalLQGUniqueness

