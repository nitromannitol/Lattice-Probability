/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushSmooth
import LatticeProb.Bonanno.LQGMetric.LFPP.PathAnalytic

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric

theorem laneC_outer_cluster_compact : IsCompact laneCOuterCluster := by
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem laneC_inwardPush_fderiv_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ d ∈ Icc (0 : ℝ) (1 / 1000), ∀ z ∈ laneCOuterCluster,
        ‖fderiv ℝ (laneCInwardPush d) z‖ ≤ M := by
  let K : Set (ℝ × ℂ) := (Icc (0 : ℝ) (1 / 1000)).prod laneCOuterCluster
  have hK : IsCompact K := isCompact_Icc.prod laneC_outer_cluster_compact
  have hcont : Continuous (fun p : ℝ × ℂ =>
      fderiv ℝ (laneCInwardPush p.1) p.2) :=
    laneC_inwardPush_fderiv_continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro d hd z hz
  exact (hM (d, z) ⟨hd, hz⟩).trans (le_max_left _ _)

theorem laneC_inwardPush_weight_bound (ξ : ℝ) (f : ℂ → ℝ)
    (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ d ∈ Icc (0 : ℝ) (1 / 1000), ∀ z ∈ laneCOuterCluster,
        Real.exp (ξ * f (laneCInwardPush d z)) ≤ B := by
  let K : Set (ℝ × ℂ) := (Icc (0 : ℝ) (1 / 1000)).prod laneCOuterCluster
  have hK : IsCompact K := isCompact_Icc.prod laneC_outer_cluster_compact
  have hcont : Continuous (fun p : ℝ × ℂ =>
      Real.exp (ξ * f (laneCInwardPush p.1 p.2))) :=
    Real.continuous_exp.comp (continuous_const.mul
      (hf.comp laneC_inwardPush_joint_contDiff.continuous))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro d hd z hz
  exact (le_abs_self _).trans ((hB (d, z) ⟨hd, hz⟩).trans (le_max_left _ _))

theorem laneC_piecewise_ae_differentiable {γ : ℝ → ℂ} {a b : ℂ}
    (hγ : IsPiecewiseC1Path γ a b) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ γ t := by
  obtain ⟨k, u, hu, hu0, hu1, hC⟩ := hγ.piecewise
  have hfin : (range u).Countable := (finite_range u).countable
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hfin.ae_notMem volume] with t ht htI
  have h0 : (0 : ℝ) ∈ range u := ⟨0, hu0⟩
  have h1 : (1 : ℝ) ∈ range u := ⟨Fin.last k, hu1⟩
  have htopen : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htI.1 (Ne.symm (fun he => ht (he ▸ h0))),
      lt_of_le_of_ne htI.2 (fun he => ht (he ▸ h1))⟩
  exact (LQGDimension.TreeIneqJ42.hasDerivAt_of_piece hu0 hu1 hC htopen ht).differentiableAt

end SupercriticalLQGUniqueness.B2.DG20Conc
