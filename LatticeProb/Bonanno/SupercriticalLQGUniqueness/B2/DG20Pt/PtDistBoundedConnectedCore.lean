/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBoundedConnectedCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingCoarseTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Bornology Metric
open LQGMetric LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_bounded_connected_core
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧
      Bornology.IsBounded V ∧ V ⊆ U ∧ z ∈ V ∧ w ∈ V := by
  obtain ⟨q, hq⟩ := t15_exists_isDGPath hU hUc hz hw
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn hq.continuousOn
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  let F : Set ℂ := U ∩ Metric.ball (0 : ℂ) R
  have hF : IsOpen F := hU.inter Metric.isOpen_ball
  have hKF : K ⊆ F := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨hq.mapsTo ht, hKR ⟨t, ht, rfl⟩⟩
  have hzK : z ∈ K := by
    refine ⟨0, by norm_num, ?_⟩
    exact hq.source
  have hwK : w ∈ K := by
    refine ⟨1, by norm_num, ?_⟩
    exact hq.target
  have hKconn : IsConnected K :=
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image q hq.continuousOn
  let V : Set ℂ := connectedComponentIn F z
  have hVF : V ⊆ F := connectedComponentIn_subset F z
  have hV : IsOpen V := hF.connectedComponentIn
  have hVc : IsConnected V :=
    isConnected_connectedComponentIn_iff.mpr (hKF hzK)
  have hVb : Bornology.IsBounded V := by
    apply (isBounded_iff_subset_ball (0 : ℂ)).2
    refine ⟨R, ?_⟩
    exact fun x hx => (hVF hx).2
  have hzV : z ∈ V :=
    mem_connectedComponentIn (hKF hzK)
  have hwV : w ∈ V :=
    hKconn.isPreconnected.subset_connectedComponentIn hzK hKF hwK
  exact ⟨V, hV, hVc, hVb, fun x hx => (hVF hx).1, hzV, hwV⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
