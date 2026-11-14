/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.LscTop.Limits at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory

namespace SupercriticalLQGUniqueness.B2.LscTop

instance instNonemptyLSCFun : Nonempty LSCFun := ⟨⟨fun _ => ⊤, lowerSemicontinuous_const⟩⟩

 
def euclideanLSCMetric : LSCMetric :=
  ⟨fun p => edist p.1 p.2,
    ⟨fun x => edist_self x, fun _ _ h => edist_eq_zero.1 h, fun x y => edist_comm x y,
      fun x y z => edist_triangle x y z⟩,
    continuous_edist.lowerSemicontinuous⟩

instance instNonemptyLSCMetric : Nonempty LSCMetric := ⟨euclideanLSCMetric⟩

 
theorem borelSpace_LSCMetric : BorelSpace LSCMetric := ⟨rfl⟩

 

variable {Ω : Type*} [MeasurableSpace Ω]

 

section LSCFun

variable [MeasurableSpace LSCFun] [BorelSpace LSCFun]

 

end LSCFun

 

section LSCMetric

 
theorem measurable_toLSCFun [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    Measurable LSCMetric.toLSCFun := by
  have := borelSpace_LSCMetric
  exact LSCMetric.isInducing_toLSCFun.continuous.measurable

 

theorem measurable_iff_toLSCFun [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {L : Ω → LSCMetric} : Measurable L ↔ Measurable fun ω => (L ω).toLSCFun := by
  refine ⟨fun h => measurable_toLSCFun.comp h, fun h => ?_⟩
  have hb : LSCMetric.instMeasurableSpace =
      MeasurableSpace.comap LSCMetric.toLSCFun ‹MeasurableSpace LSCFun› := by
    rw [BorelSpace.measurable_eq (α := LSCFun)]
    exact borel_comap
  rw [measurable_iff_comap_le, hb, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 h

 
end LSCMetric

end SupercriticalLQGUniqueness.B2.LscTop
