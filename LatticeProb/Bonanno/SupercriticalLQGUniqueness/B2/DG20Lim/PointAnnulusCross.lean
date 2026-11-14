/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Lim.PointAnnulusCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFixedAnnulus

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem annulus_cross_le_lfppDOn
    (ξ : ℝ) (f : ℂ → ℝ) (z x y : ℂ)
    (a b R : ℝ) (hxa : dist x z < a) (hab : a < b)
    (hbR : b < R) (hby : b < dist y z) :
    crossLenIn ξ f (closedBall z R) (sphere z a) (sphere z b) ≤
      lfppDOn ξ f univ x y := by
  change crossLenIn ξ f (closedBall z R) (sphere z a) (sphere z b) ≤
    ⨅ p : {p : ℝ → ℂ // IsPiecewiseC1Path p x y ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ univ}, lfppLen ξ f p.1
  apply le_iInf
  intro p
  obtain ⟨σ, τ, hσ, hστ, hτ, hσrad, hτrad, hbetween⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.crossing_extract
      (show (0 : ℝ) ≤ 1 by norm_num) p.2.1.continuousOn hab
      (by rw [p.2.1.source]; exact hxa)
      (by rw [p.2.1.target]; exact hby)
  have hpath : IsPiecewiseC1Path (subPath p.1 σ τ) (p.1 σ) (p.1 τ) :=
    isPiecewiseC1Path_subPath p.2.1 hσ hστ hτ
  have hadm : AdmPath (closedBall z R) (sphere z a) (sphere z b)
      (subPath p.1 σ τ) := by
    refine ⟨p.1 σ, mem_sphere.mpr (by simpa only [dist_comm z (p.1 σ)] using hσrad),
      p.1 τ, mem_sphere.mpr (by simpa only [dist_comm z (p.1 τ)] using hτrad),
      hpath, ?_⟩
    intro u hu
    have hv : (τ - σ) * u + σ ∈ Icc σ τ := by
      constructor <;> nlinarith [hu.1, hu.2, hστ]
    have hr := (hbetween _ hv).2
    change dist (p.1 ((τ - σ) * u + σ)) z ≤ b at hr
    simp only [subPath]
    apply mem_closedBall.mpr
    have hr' : dist z (p.1 ((τ - σ) * u + σ)) ≤ b := by
      simpa only [dist_comm] using hr
    linarith
  calc
    crossLenIn ξ f (closedBall z R) (sphere z a) (sphere z b) ≤
      lfppLen ξ f (subPath p.1 σ τ) := crossLenIn_le_lfppLen hadm
    _ ≤ lfppLen ξ f p.1 := by
      rw [lfppLen_subPath p.1 hστ, lfppLen_eq]
      exact lintegral_mono_set (Icc_subset_Icc hσ hτ)

end SupercriticalLQGUniqueness.B2.DG20Lim
