/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupportAnnulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupport

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 


theorem laneC_hoBlock_subset_center_ball (K : ℕ) (b : ℤ × ℤ) :
    T20B.hoBlock K b ⊆
      closedBall (T20.dyCenter K b) ((2 : ℝ)⁻¹ ^ K) := by
  intro x hx
  have hpos : 0 < (2 : ℝ) ^ K := by positivity
  have hinv : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  have hsmall : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  have hmul (v : ℝ) : (v * (2 : ℝ) ^ K) * (2 : ℝ)⁻¹ ^ K = v := by
    rw [mul_assoc, hinv, mul_one]
  have hre₁ := Int.floor_le (x.re * (2 : ℝ) ^ K)
  have hre₂ := Int.lt_floor_add_one (x.re * (2 : ℝ) ^ K)
  have him₁ := Int.floor_le (x.im * (2 : ℝ) ^ K)
  have him₂ := Int.lt_floor_add_one (x.im * (2 : ℝ) ^ K)
  rw [hx.1] at hre₁ hre₂
  rw [hx.2] at him₁ him₂
  have hre_lo : (b.1 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.re := by
    calc _ ≤ (x.re * (2 : ℝ) ^ K) * (2 : ℝ)⁻¹ ^ K :=
          mul_le_mul_of_nonneg_right hre₁ hsmall.le
      _ = _ := hmul _
  have hre_hi : x.re ≤ ((b.1 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by
    calc _ = (x.re * (2 : ℝ) ^ K) * (2 : ℝ)⁻¹ ^ K := (hmul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hre₂.le hsmall.le
  have him_lo : (b.2 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ x.im := by
    calc _ ≤ (x.im * (2 : ℝ) ^ K) * (2 : ℝ)⁻¹ ^ K :=
          mul_le_mul_of_nonneg_right him₁ hsmall.le
      _ = _ := hmul _
  have him_hi : x.im ≤ ((b.2 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by
    calc _ = (x.im * (2 : ℝ) ^ K) * (2 : ℝ)⁻¹ ^ K := (hmul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right him₂.le hsmall.le
  have hreal : |(x - T20.dyCenter K b).re| ≤ (2 : ℝ)⁻¹ ^ K / 2 := by
    rw [abs_le]
    simp only [Complex.sub_re, T20.dyCenter]
    constructor <;> nlinarith
  have himag : |(x - T20.dyCenter K b).im| ≤ (2 : ℝ)⁻¹ ^ K / 2 := by
    rw [abs_le]
    simp only [Complex.sub_im, T20.dyCenter]
    constructor <;> nlinarith
  change dist x (T20.dyCenter K b) ≤ (2 : ℝ)⁻¹ ^ K
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

 

theorem laneC_outer_region_subset_farSet
    {B : Set ℂ} {c : ℂ} {d s r : ℝ}
    (hB : B ⊆ closedBall c d) (hr : d + 2 * s ≤ r) :
    {x : ℂ | r ≤ dist x c} ⊆ T20B.farSet B s := by
  intro x hx y hy
  change r ≤ dist x c at hx
  have hyc : dist y c ≤ d := hB hy
  have htri : dist x c ≤ dist x y + dist y c := dist_triangle x y c
  change 2 * s ≤ ‖x - y‖
  rw [← dist_eq_norm]
  linarith

 


theorem laneC_resampled_field_eq_on_outer_region
    (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    {s : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
        (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (c : ℤ × ℤ → ℂ) (d r : ℝ)
    (hblock : ∀ b ∈ T20B.nearIdx K,
      T20B.hoBlock K b ⊆ closedBall (c b) d)
    (hr : d + 2 * s ≤ r) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      ∀ x : ℂ, r ≤ dist x (c b) →
        psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2 = psiMN Q W P 0 n x z.1 := by
  filter_upwards [laneC_resampled_field_eq_outside_support hW Q hKn hσ]
    with z hz b hb x hx
  exact hz b hb x (laneC_outer_region_subset_farSet (hblock b hb) hr hx)

 


end SupercriticalLQGUniqueness.B2.DG20Conc
