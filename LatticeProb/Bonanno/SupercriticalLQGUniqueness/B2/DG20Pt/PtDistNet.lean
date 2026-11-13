/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23Disc

 




set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem exists_pt_dist_net (V : Set ℂ) (hV : Bornology.IsBounded V) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, ∃ F : Finset ℂ,
      F.card ≤ C * 4 ^ k ∧
      ∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2) := by
  obtain ⟨R, hVR⟩ := hV.subset_ball (0 : ℂ)
  let B : ℝ := max R 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hnorm : ∀ z ∈ V, ‖z‖ ≤ B := by
    intro z hz
    exact (le_of_lt (by simpa [dist_zero_right] using hVR hz)).trans
      (le_max_left R 1)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (8 * B) (by norm_num : (1 : ℝ) < 2)
  let H : ℂ → ℂ := fun z => ⟨(z.re + B) / (2 * B), (z.im + B) / (2 * B)⟩
  let J : ℂ → ℂ := fun c => (2 * B : ℝ) * c - ⟨B, B⟩
  have hH : ∀ z ∈ V, H z ∈ L23.sq01 := by
    intro z hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans (hnorm z hz))
    have him := abs_le.mp ((Complex.abs_im_le_norm z).trans (hnorm z hz))
    apply L23.mem_sq01.mpr
    dsimp [H]
    simp only [mem_Icc]
    constructor <;> constructor
    · apply div_nonneg <;> linarith
    · apply (div_le_one (by positivity : 0 < 2 * B)).2
      linarith
    · apply div_nonneg <;> linarith
    · apply (div_le_one (by positivity : 0 < 2 * B)).2
      linarith
  have hJH (z : ℂ) : J (H z) = z := by
    apply Complex.ext
    · dsimp [J, H]
      simp only [Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      field_simp
      ring
    · dsimp [J, H]
      simp only [Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      field_simp
      ring
  have hcoef : 2 * B * ((2 : ℝ)⁻¹) ^ m < ((2 : ℝ)⁻¹) ^ 2 := by
    rw [inv_pow]
    norm_num
    calc
      2 * B * ((2 : ℝ) ^ m)⁻¹ = (2 * B) / ((2 : ℝ) ^ m) := by ring
      _ < 1 / 4 := (div_lt_iff₀ (by positivity)).2 (by nlinarith [hm])
  let C : ℕ := 4 ^ m
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k
  let F : Finset ℂ := (L23.grid (k + m)).image J
  refine ⟨F, ?_, ?_⟩
  · have hcard : F.card ≤ 4 ^ (k + m) := by
      calc
        F.card ≤ (L23.grid (k + m)).card := Finset.card_image_le
        _ ≤ ((Finset.range (2 ^ (k + m)) ×ˢ Finset.range (2 ^ (k + m))).card) :=
          Finset.card_image_le
        _ = 4 ^ (k + m) := by
          simp only [Finset.card_product, Finset.card_range]
          rw [← mul_pow]
          norm_num
    simpa only [C, pow_add, mul_comm] using hcard
  · intro z hz
    obtain ⟨c, hc, hnear⟩ := L23.exists_grid_near (k + m) (hH z hz)
    refine ⟨J c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
    have hdiff : z - J c = (2 * B : ℝ) * (H z - c) := by
      nth_rewrite 1 [← hJH z]
      dsimp [J]
      ring
    have hdist : dist z (J c) = (2 * B) * ‖H z - c‖ := by
      rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hradius :
        (2 * B) * (((2 : ℝ)⁻¹) ^ (k + m)) < ((2 : ℝ)⁻¹) ^ (k + 2) := by
      simp only [pow_add]
      calc
        2 * B * (((2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹) ^ m) =
            ((2 : ℝ)⁻¹) ^ k * (2 * B * ((2 : ℝ)⁻¹) ^ m) := by ring
        _ < ((2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹) ^ 2 :=
          mul_lt_mul_of_pos_left hcoef (by positivity)
    rw [hdist]
    exact (mul_le_mul_of_nonneg_left hnear (by positivity)).trans_lt hradius

end SupercriticalLQGUniqueness.B2.DG20Pt
