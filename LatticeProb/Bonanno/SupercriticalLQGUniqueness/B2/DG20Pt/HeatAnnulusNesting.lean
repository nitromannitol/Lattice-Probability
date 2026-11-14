/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusNesting at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_nested_annulus_cross_le
    (ξ : ℝ) (f : ℂ → ℝ) (z : ℂ)
    (K : Set ℂ) (a₀ a₁ b₁ b₀ R₁ : ℝ)
    (ha : a₀ < a₁) (hab : a₁ < b₁) (hb : b₁ < b₀)
    (hR : b₁ ≤ R₁) :
    crossLenIn ξ f (closedBall z R₁) (sphere z a₁) (sphere z b₁) ≤
      crossLenIn ξ f K (sphere z a₀) (sphere z b₀) := by
  apply le_crossLenIn
  intro p hp
  obtain ⟨u, hu, v, hv, hpPath, hpK⟩ := hp
  obtain ⟨σ, τ, hσ, hστ, hτ, hσrad, hτrad, hbetween⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.crossing_extract (z := z)
      (show (0 : ℝ) ≤ 1 by norm_num) hpPath.continuousOn
      hab
      (by rw [hpPath.source]; exact (mem_sphere.mp hu).trans_lt ha)
      (by rw [hpPath.target]; exact hb.trans_eq (mem_sphere.mp hv).symm)
  have hpath : IsPiecewiseC1Path (subPath p σ τ) (p σ) (p τ) :=
    isPiecewiseC1Path_subPath hpPath hσ hστ hτ
  have hadm : AdmPath (closedBall z R₁)
      (sphere z a₁) (sphere z b₁) (subPath p σ τ) := by
    refine ⟨p σ, mem_sphere.mpr (by simpa only [dist_comm z (p σ)] using hσrad),
      p τ, mem_sphere.mpr (by simpa only [dist_comm z (p τ)] using hτrad),
      hpath, ?_⟩
    intro t ht
    have ht' : (τ - σ) * t + σ ∈ Icc σ τ := by
      constructor <;> nlinarith [ht.1, ht.2, hστ]
    have hr := (hbetween _ ht').2
    change dist (p ((τ - σ) * t + σ)) z ≤ b₁ at hr
    simp only [subPath]
    apply mem_closedBall.mpr
    exact hr.trans hR
  calc
    crossLenIn ξ f (closedBall z R₁) (sphere z a₁) (sphere z b₁) ≤
      lfppLen ξ f (subPath p σ τ) := crossLenIn_le_lfppLen hadm
    _ ≤ lfppLen ξ f p := by
      rw [lfppLen_subPath p hστ, lfppLen_eq]
      exact lintegral_mono_set (Icc_subset_Icc hσ hτ)

end SupercriticalLQGUniqueness.B2.DG20Pt
