/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.SLUFieldSupport
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalA
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.SLUMetricAPI2
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Normed.Module.Basic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 






















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC DistOn addConst restrictTo)

 
def shape12 : EuclideanAnnulus := ⟨(0, (1, 2)), by norm_num, by norm_num⟩

 
def ann12 (w : ℂ) (t : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  Positivity.Witnesses.annulusTranslate (shape12.dilate t t.2) w

@[simp] theorem ann12_center (w : ℂ) (t : Ioi (0 : ℝ)) : (ann12 w t).center = w := by
  change (t : ℝ) • (0 : ℂ) + w = w
  simp

@[simp] theorem ann12_innerRadius (w : ℂ) (t : Ioi (0 : ℝ)) : (ann12 w t).innerRadius = t := by
  change (t : ℝ) * 1 = t
  ring

@[simp] theorem ann12_outerRadius (w : ℂ) (t : Ioi (0 : ℝ)) :
    (ann12 w t).outerRadius = 2 * t := by
  change (t : ℝ) * 2 = 2 * t
  ring

 

theorem circleAvg_congr_restrict {U : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (he : restrictTo U g₁ = restrictTo U g₂) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hsU : sphere z r ⊆ U) : LQGMetric.circleAvg g₁ r z = LQGMetric.circleAvg g₂ r z := by
  obtain ⟨ε, hε, hthick⟩ := (isCompact_sphere z r).exists_thickening_subset_open U.isOpen hsU
  obtain ⟨N, hN⟩ := LQGMetric.CONF.exists_circBump_supp hr z (subset_refl _) hε
  have heq : (fun n => LQGMetric.CircleAvg.mollAvg g₁ n z r) =ᶠ[atTop]
      (fun n => LQGMetric.CircleAvg.mollAvg g₂ n z r) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [LQGMetric.CircleAvg.mollAvg_eq, LQGMetric.CircleAvg.mollAvg_eq]
    exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _ ((hN n hn).trans hthick)
  rw [LQGMetric.CircleAvg.circleAvg_eq_limUnder, LQGMetric.CircleAvg.circleAvg_eq_limUnder]
  unfold limUnder
  rw [Filter.map_congr heq]

 
end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
