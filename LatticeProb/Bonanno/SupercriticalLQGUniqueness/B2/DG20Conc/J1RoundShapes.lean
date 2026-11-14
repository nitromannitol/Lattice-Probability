/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_round_radius_eq {K m : ℕ} (hmK : m ≤ K) :
    (2 : ℝ)⁻¹ ^ K * (2 : ℝ) ^ m =
      LaneCInputs.sourceRadius K m := by
  have hpow : (2 : ℝ)⁻¹ ^ K =
      (2 : ℝ)⁻¹ ^ (K - m) * (2 : ℝ)⁻¹ ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmK]
  rw [hpow]
  simp only [LaneCInputs.sourceRadius]
  have hc : (2 : ℝ)⁻¹ ^ m * 2 ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ)⁻¹ ^ (K - m) * (2 : ℝ)⁻¹ ^ m * 2 ^ m =
        (2 : ℝ)⁻¹ ^ (K - m) * ((2 : ℝ)⁻¹ ^ m * 2 ^ m) := by ring
    _ = (2 : ℝ)⁻¹ ^ (K - m) := by rw [hc, mul_one]

theorem j1_affine_dist (r : ℝ) (hr : 0 < r) (c z : ℂ) :
    dist ((r : ℂ) * z + c) c = r * dist z 0 := by
  rw [dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, dist_zero_right]

theorem j1_affine_surj {r : ℝ} (hr : 0 < r) (c w : ℂ) :
    ∃ z : ℂ, (r : ℂ) * z + c = w := by
  refine ⟨(r : ℂ)⁻¹ * (w - c), ?_⟩
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hr0, one_mul, sub_add_cancel]

theorem j1_round_cross_image (r R : ℝ) (hr : 0 < r) (c : ℂ) :
    (fun z : ℂ => (r : ℂ) * z + c) '' j1RoundCross R =
      {w | dist w c ∈ Icc (r * R) (r * (2 * R))} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change dist z 0 ∈ Icc R (2 * R) at hz
    change dist ((r : ℂ) * z + c) c ∈ Icc (r * R) (r * (2 * R))
    rw [j1_affine_dist r hr c z]
    exact ⟨mul_le_mul_of_nonneg_left hz.1 hr.le,
      mul_le_mul_of_nonneg_left hz.2 hr.le⟩
  · intro hw
    obtain ⟨z, rfl⟩ := j1_affine_surj hr c w
    refine ⟨z, ?_, rfl⟩
    change dist ((r : ℂ) * z + c) c ∈ Icc (r * R) (r * (2 * R)) at hw
    change dist z 0 ∈ Icc R (2 * R)
    rw [j1_affine_dist r hr c z] at hw
    exact ⟨(mul_le_mul_iff_of_pos_left hr).mp hw.1,
      (mul_le_mul_iff_of_pos_left hr).mp hw.2⟩

theorem j1_round_sphere_image (r R : ℝ) (hr : 0 < r) (c : ℂ) :
    (fun z : ℂ => (r : ℂ) * z + c) '' sphere (0 : ℂ) R =
      sphere c (r * R) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_sphere, j1_affine_dist r hr c z, mem_sphere.mp hz]
  · intro hw
    obtain ⟨z, rfl⟩ := j1_affine_surj hr c w
    refine ⟨z, ?_, rfl⟩
    rw [mem_sphere, j1_affine_dist r hr c z] at hw
    exact (mul_left_cancel₀ hr.ne' hw)

def j1SourceCross (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  {z | dist z (LQGMetric.DDDF.T20.dyCenter K b) ∈
    Icc (LaneCInputs.sourceRadius K m)
      (2 * LaneCInputs.sourceRadius K m)}

theorem j1_round_cross_image_source {K m : ℕ} (hmK : m ≤ K)
    (b : ℤ × ℤ) :
    (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z +
      LQGMetric.DDDF.T20.dyCenter K b) '' j1RoundCross ((2 : ℝ)^m) =
      j1SourceCross K m b := by
  rw [j1_round_cross_image _ _ (by positivity)]
  rw [j1_round_radius_eq hmK]
  have heq : (2 : ℝ)⁻¹ ^ K * (2 * 2 ^ m) =
      2 * LaneCInputs.sourceRadius K m := by
    rw [← j1_round_radius_eq hmK]
    ring
  rw [heq]
  rfl

theorem j1_round_inner_image_source {K m : ℕ} (hmK : m ≤ K)
    (b : ℤ × ℤ) :
    (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z +
      LQGMetric.DDDF.T20.dyCenter K b) '' sphere (0 : ℂ) ((2 : ℝ)^m) =
      LaneCInputs.sourceInner K m b := by
  rw [j1_round_sphere_image _ _ (by positivity), j1_round_radius_eq hmK]
  rfl

theorem j1_round_outer_image_source {K m : ℕ} (hmK : m ≤ K)
    (b : ℤ × ℤ) :
    (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z +
      LQGMetric.DDDF.T20.dyCenter K b) '' sphere (0 : ℂ) (2 * (2 : ℝ)^m) =
      LaneCInputs.sourceOuter K m b := by
  rw [j1_round_sphere_image _ _ (by positivity)]
  have heq : (2 : ℝ)⁻¹ ^ K * (2 * 2 ^ m) =
      2 * LaneCInputs.sourceRadius K m := by
    rw [← j1_round_radius_eq hmK]
    ring
  rw [heq]
  rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
