/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module NV1Evidence at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyUnif
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Prob.Median

 





set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF)

theorem isCircleAverage_old_of_exists {g : DistC} {r : Set.Ioi (0 : ℝ)} {z : ℂ}
    (h : ∃ a, IsCircleAverage g r z a) :
    IsCircleAverage g r z (LQGMetric.circleAvg g r z) := by
  obtain ⟨a, ha⟩ := h
  have heq : LQGMetric.circleAvg g r z = a := ha.limUnder_eq
  rw [heq]
  exact ha

theorem ae_isCircleAverage_old {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (LQGMetric.circleAvg (h ω) r z) :=
  (LQGMetric.CircleAvg.ae_tendsto_mollAvg hh z r.2).mono
    (fun _ hω => isCircleAverage_old_of_exists hω)

theorem isNormalizedWholePlaneGFF_iff_old {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} :
    IsNormalizedWholePlaneGFF h P ↔ LQGMetric.IsNormalizedWPGFF h P := by
  constructor
  · rintro ⟨hh, h0⟩
    exact ⟨hh, h0.mono (fun _ hω => hω.limUnder_eq)⟩
  · rintro ⟨hh, h0⟩
    refine ⟨hh, ((ae_isCircleAverage_old hh ⟨1, Set.mem_Ioi.mpr one_pos⟩ 0).and h0).mono ?_⟩
    intro ω hω
    simpa only [IsCircleAverage, Subtype.coe_mk, hω.2] using hω.1

end SupercriticalLQGUniqueness
