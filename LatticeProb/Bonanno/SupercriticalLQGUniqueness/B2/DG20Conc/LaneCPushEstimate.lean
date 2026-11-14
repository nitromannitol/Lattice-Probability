/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPushEstimate at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInwardPush
import Mathlib.Topology.MetricSpace.Pseudo.Basic

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_inwardPush_sub_eq (d : ℝ) (z : ℂ) :
    laneCInwardPush d z - z =
      (d * (5 - laneCSquareNormSq z)) • (z - laneCSquareCenter) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.smul_re]
    change (1 / 2 + (1 + d * (5 - laneCSquareNormSq z)) * laneCSquareX z) - z.re =
      (d * (5 - laneCSquareNormSq z)) * (z.re - 1 / 2)
    dsimp [laneCSquareX]
    ring
  · simp only [Complex.sub_im, Complex.smul_im]
    change (1 / 2 + (1 + d * (5 - laneCSquareNormSq z)) * laneCSquareY z) - z.im =
      (d * (5 - laneCSquareNormSq z)) * (z.im - 1 / 2)
    dsimp [laneCSquareY]
    ring

 
theorem laneC_inwardPush_dist_le {d : ℝ} (hd : 0 ≤ d)
    {z : ℂ} (hz : z ∈ laneCDoublePrimeCross) :
    dist (laneCInwardPush d z) z ≤ 30 * d := by
  obtain ⟨_, hrhi, _, hqhi⟩ := laneC_closed_ring_radius z hz
  have hq0 : 0 ≤ laneCSquareNormSq z := by
    unfold laneCSquareNormSq
    positivity
  have hqmax : laneCSquareNormSq z ≤ 25 / 2 := by nlinarith
  have hwabs : |5 - laneCSquareNormSq z| ≤ 15 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hx : |laneCSquareX z| ≤ 5 / 2 :=
    (le_max_left _ _).trans hrhi
  have hy : |laneCSquareY z| ≤ 5 / 2 :=
    (le_max_right _ _).trans hrhi
  have hnorm : ‖z - laneCSquareCenter‖ ≤ 4 := by
    have hsq : ‖z - laneCSquareCenter‖ ^ 2 = laneCSquareNormSq z := by
      simp [Complex.sq_norm, Complex.normSq_apply, laneCSquareNormSq,
        laneCSquareX, laneCSquareY, laneCSquareCenter]
      ring
    nlinarith [norm_nonneg (z - laneCSquareCenter), hsq]
  rw [dist_eq_norm, laneC_inwardPush_sub_eq, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg hd]
  have hm : |5 - laneCSquareNormSq z| * ‖z - laneCSquareCenter‖ ≤
      (15 / 2 : ℝ) * 4 :=
    mul_le_mul hwabs hnorm (norm_nonneg _) (by positivity)
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hm)]

 
end SupercriticalLQGUniqueness.B2.DG20Conc
