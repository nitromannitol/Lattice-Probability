/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusOsc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusGeometry

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
def laneBBlockAnnulus (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitUcross i

 
theorem laneB_small_radius_le_one {K : ℕ} (hK : 3 ≤ K) :
    5 * (2 : ℝ)⁻¹ ^ K ≤ 1 := by
  have hpow : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
  norm_num at hpow
  linarith

 
theorem laneB_block_annulus_subset_closedBall (i : Bool) (v : ℂ) (K : ℕ) :
    laneBBlockAnnulus i v K ⊆ closedBall v (5 * (2 : ℝ)⁻¹ ^ K) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  have hnorm := laneB_unit_small_annuli_radius i hy
  simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    mul_comm (5 : ℝ),
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ K)] using
    (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ K))

 

end SupercriticalLQGUniqueness.B2.DG20Conc
