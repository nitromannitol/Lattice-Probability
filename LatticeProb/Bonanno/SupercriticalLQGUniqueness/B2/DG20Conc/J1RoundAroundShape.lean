/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundAroundShape at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperPoint

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_round_around_image (r R : ℝ) (hr : 0 < r) (c : ℂ) :
    (fun z : ℂ => (r : ℂ) * z + c) ''
      {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} =
    {w : ℂ | r * R < dist w c ∧ dist w c < r * (2 * R)} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change R < dist z 0 ∧ dist z 0 < 2 * R at hz
    change r * R < dist ((r : ℂ) * z + c) c ∧
      dist ((r : ℂ) * z + c) c < r * (2 * R)
    rw [j1_affine_dist r hr c z]
    exact ⟨mul_lt_mul_of_pos_left hz.1 hr,
      mul_lt_mul_of_pos_left hz.2 hr⟩
  · intro hw
    obtain ⟨z, rfl⟩ := j1_affine_surj hr c w
    refine ⟨z, ?_, rfl⟩
    change r * R < dist ((r : ℂ) * z + c) c ∧
      dist ((r : ℂ) * z + c) c < r * (2 * R) at hw
    change R < dist z 0 ∧ dist z 0 < 2 * R
    rw [j1_affine_dist r hr c z] at hw
    exact ⟨(mul_lt_mul_iff_of_pos_left hr).mp hw.1,
      (mul_lt_mul_iff_of_pos_left hr).mp hw.2⟩

theorem j1_round_around_image_source {K m : ℕ} (hmK : m ≤ K)
    (b : ℤ × ℤ) :
    (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z +
      LQGMetric.DDDF.T20.dyCenter K b) ''
        {z : ℂ | (2 : ℝ)^m < dist z 0 ∧
          dist z 0 < 2 * (2 : ℝ)^m} =
      LaneCInputs.sourceAround K m b := by
  rw [j1_round_around_image _ _ (by positivity)]
  rw [j1_round_radius_eq hmK]
  have heq : (2 : ℝ)⁻¹ ^ K * (2 * 2 ^ m) =
      2 * LaneCInputs.sourceRadius K m := by
    rw [← j1_round_radius_eq hmK]
    ring
  rw [heq]
  rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
