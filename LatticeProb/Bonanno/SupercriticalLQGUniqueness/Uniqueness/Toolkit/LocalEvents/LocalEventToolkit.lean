/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUFieldSupport
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom2
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46Meas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw




 







set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents

open LQGMetric (DistC DistOn restrictTo pairJ)

 

theorem isGFFPlusCont_addConst
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : LQGMetric.IsGFFPlusCont h P)
    {c : Ω → ℝ} (hc : Measurable c) :
    LQGMetric.IsGFFPlusCont (fun ω => LQGMetric.addConst (h ω) (c ω)) P := by
  obtain ⟨hm, f, hfm, hwhole⟩ := hh
  refine ⟨LQGMetric.DFGPS.L219.measurable_addConst_of hm hc, f, hfm, ?_⟩
  have he : (fun ω => LQGMetric.addConst (h ω) (c ω) - LQGMetric.ofCont (f ω)) =
      (fun ω => LQGMetric.addConst (h ω - LQGMetric.ofCont (f ω)) (c ω)) := by
    funext ω
    ext φ
    simp only [sub_apply, LQGMetric.GFFInv.addConst_apply]
    ring
  rw [he]
  exact hwhole.addConst hc

 
end SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents
