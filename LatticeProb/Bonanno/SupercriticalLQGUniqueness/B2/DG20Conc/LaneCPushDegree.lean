/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushDegree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushEstimate
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_closed_ring_norm_ge {z : ℂ} (hz : z ∈ laneCDoublePrimeCross) :
    3 / 2 ≤ ‖z - laneCSquareCenter‖ := by
  have hr := (laneC_closed_ring_radius z hz).1
  have hre : |laneCSquareX z| ≤ ‖z - laneCSquareCenter‖ := by
    simpa [laneCSquareX, laneCSquareCenter] using
      Complex.abs_re_le_norm (z - laneCSquareCenter)
  have him : |laneCSquareY z| ≤ ‖z - laneCSquareCenter‖ := by
    simpa [laneCSquareY, laneCSquareCenter] using
      Complex.abs_im_le_norm (z - laneCSquareCenter)
  exact hr.trans (max_le hre him)

 

theorem laneC_inwardPush_loopDeg_eq {d : ℝ} (hd : 0 < d)
    (hdsmall : d ≤ 1 / 1000) (P : C(unitInterval, ℂ))
    (hP : ∀ t, P t ∈ laneCDoublePrimeCross)
    (hclosed : P 0 = P 1) :
    loopDeg
      ⟨fun t => laneCInwardPush d (P t) - laneCSquareCenter,
        ((laneC_inwardPush_continuous d).comp P.continuous).sub continuous_const⟩
      (by
        intro t hzero
        have hz := (laneC_inwardPush_mem_open hd hdsmall (hP t)).2
        apply hz
        have hcenter : laneCSquareCenter ∈ laneCInnerCluster := by
          norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]
        exact (sub_eq_zero.mp hzero) ▸ hcenter) =
    loopDeg
      ⟨fun t => P t - laneCSquareCenter, P.continuous.sub continuous_const⟩
      (by
        intro t hzero
        have hnorm := laneC_closed_ring_norm_ge (hP t)
        change P t - laneCSquareCenter = 0 at hzero
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm) := by
  let γ : C(unitInterval, ℂ) :=
    ⟨fun t => laneCInwardPush d (P t) - laneCSquareCenter,
      ((laneC_inwardPush_continuous d).comp P.continuous).sub continuous_const⟩
  let δ : C(unitInterval, ℂ) :=
    ⟨fun t => P t - laneCSquareCenter, P.continuous.sub continuous_const⟩
  have hγ : ∀ t, γ t ≠ 0 := by
    intro t hzero
    have hz := (laneC_inwardPush_mem_open hd hdsmall (hP t)).2
    apply hz
    have hcenter : laneCSquareCenter ∈ laneCInnerCluster := by
      norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]
    exact (sub_eq_zero.mp hzero) ▸ hcenter
  have hδ : ∀ t, δ t ≠ 0 := by
    intro t hzero
    have hnorm := laneC_closed_ring_norm_ge (hP t)
    rw [show P t - laneCSquareCenter = 0 from hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hγc : γ 0 = γ 1 := by simp only [γ, ContinuousMap.coe_mk, hclosed]
  have hδc : δ 0 = δ 1 := by simp only [δ, ContinuousMap.coe_mk, hclosed]
  have hclose : ∀ t, ‖γ t - δ t‖ < ‖δ t‖ := by
    intro t
    have hdisp := laneC_inwardPush_dist_le hd.le (hP t)
    have hnorm := laneC_closed_ring_norm_ge (hP t)
    change ‖(laneCInwardPush d (P t) - laneCSquareCenter) -
      (P t - laneCSquareCenter)‖ < ‖P t - laneCSquareCenter‖
    have heq : (laneCInwardPush d (P t) - laneCSquareCenter) -
        (P t - laneCSquareCenter) = laneCInwardPush d (P t) - P t := by ring
    rw [heq, ← dist_eq_norm]
    have hs : 30 * d < 3 / 2 := by linarith
    exact hdisp.trans_lt (hs.trans_le hnorm)
  exact loopDeg_eq_of_norm_sub_lt γ δ hγ hδ hγc hδc hclose

end SupercriticalLQGUniqueness.B2.DG20Conc
