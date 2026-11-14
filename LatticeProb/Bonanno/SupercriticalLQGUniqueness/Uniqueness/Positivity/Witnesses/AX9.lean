/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux




 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses

open LQGMetric (DistC addConst circleAvg)
open SupercriticalLQGUniqueness

def annulusTranslate (A : EuclideanAnnulus) (z : ℂ) : EuclideanAnnulus :=
  ⟨(A.center + z, A.innerRadius, A.outerRadius), A.2⟩

theorem exists_canonical_normalized_law :
    ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧
      IsNormalizedWholePlaneGFF (id : DistC → DistC) μ := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  let μ : Measure DistC := P.map h
  haveI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 inferInstance
  have hold := isNormalizedWholePlaneGFF_iff_old.mp hh
  have hμold : LQGMetric.IsNormalizedWPGFF (id : DistC → DistC) μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1, ?_⟩
    have hS : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
      measurableSet_eq_fun (LQGMetric.measurable_circleAvg_left 1 0) measurable_const
    exact (ae_map_iff hh.1.measurable.aemeasurable hS).2 hold.2
  exact ⟨μ, inferInstance, isNormalizedWholePlaneGFF_iff_old.mpr hμold⟩

end SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses
