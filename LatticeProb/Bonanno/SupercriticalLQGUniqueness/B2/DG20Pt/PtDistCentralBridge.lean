/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCentralBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOneArmPaths
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundBridge

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_selected_same_scale_bridge {ξ : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hxy : dist x y ≤ 3 * r) (p q : ℝ → ℂ) {L : ℝ≥0∞}
    (hp : AdmPath U (sphere x (r / 4)) (sphere x (16 * r)) p)
    (hq : AdmPath U (sphere y (r / 4)) (sphere y (16 * r)) q)
    (hloop : Inputs.HasAroundLoop ξ f x r hr L)
    (hball : ball x (8 * r) ⊆ U) :
    lfppDOn ξ f U (p 0) (q 0) ≤ lfppLen ξ f p + L + lfppLen ξ f q := by
  obtain ⟨a, ha, b, hb, hpPath, hpU⟩ := hp
  obtain ⟨c, hc, d, hd, hqPath, hqU⟩ := hq
  have hp0 : dist (p 0) x ≤ r / 4 := by
    rw [hpPath.source]
    exact (mem_sphere.mp ha).le
  have hp1 : 16 * r ≤ dist (p 1) x := by
    rw [hpPath.target]
    exact (mem_sphere.mp hb).ge
  have hq0 : dist (q 0) y ≤ r / 4 := by
    rw [hqPath.source]
    exact (mem_sphere.mp hc).le
  have hq1 : 16 * r ≤ dist (q 1) y := by
    rw [hqPath.target]
    exact (mem_sphere.mp hd).ge
  have hp' : IsPiecewiseC1Path p (p 0) (p 1) := by
    rw [hpPath.source, hpPath.target]
    exact hpPath
  have hq' : IsPiecewiseC1Path q (q 0) (q 1) := by
    rw [hqPath.source, hqPath.target]
    exact hqPath
  exact lfppDOn_le_of_hasAroundLoop hr hxy hloop hball p q
    hp' hq' hpU hqU hp0 hp1 hq0 hq1

end SupercriticalLQGUniqueness.B2.DG20Pt
