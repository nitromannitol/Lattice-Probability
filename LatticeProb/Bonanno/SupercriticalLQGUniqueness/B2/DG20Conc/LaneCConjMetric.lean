/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConjMetric at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLift
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousLimit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleWitness
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric Complex
open scoped ComplexConjugate

 


def laneCConjMetric (D : ContMetric) : ContMetric :=
  ⟨D.1.comp ⟨fun p => (conj p.1, conj p.2),
      (continuous_conj.comp continuous_fst).prodMk
        (continuous_conj.comp continuous_snd)⟩,
    { self_eq_zero := fun x => D.2.self_eq_zero _
      eq_of_eq_zero := fun x y h => by
        have heq := D.2.eq_of_eq_zero _ _ h
        simpa only [Complex.conj_conj] using congrArg conj heq
      symm := fun x y => D.2.symm _ _
      triangle := fun x y z => D.2.triangle _ _ _
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small (conj x) ε hε
        refine ⟨δ, hδ, fun y hy => ?_⟩
        have hh := h (conj y) hy
        simpa only [← map_sub, Complex.norm_conj] using hh }⟩

 

theorem laneC_conjMetric_len (D : ContMetric) (ρ : ℝ → ℂ) (a b : ℝ) :
    (laneCConjMetric D).len ρ a b =
      D.len (fun t => conj (ρ t)) a b := by
  unfold ContMetric.len MetricGeometry.curveLength
  symm
  exact MetricGeometry.eVariationOn_comp_eq_of_edist_eq
    (X := (laneCConjMetric D).Space) (Z := D.Space)
    (f := fun x => ((starRingEnd ℂ) (x : ℂ) : D.Space)) (P := ρ) (s := Set.Icc a b)
    (by intro x _ y _; rfl)

end SupercriticalLQGUniqueness.B2.DG20Conc
