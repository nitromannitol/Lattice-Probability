/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGridRadius at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSquareRing

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

def laneBGridRadius (R : ℝ) : ℤ := ⌈(9 / 8 : ℝ) * R⌉

def laneBSquareGauge (z : ℂ) : ℝ := max |z.re| |z.im|

theorem laneB_squareGauge_continuous : Continuous laneBSquareGauge := by
  unfold laneBSquareGauge
  exact (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

theorem laneB_grid_radius_bounds {R : ℝ} (hR : 24 ≤ R) :
    R + 1 < (laneBGridRadius R : ℝ) ∧
    (laneBGridRadius R : ℝ) + 2 ≤ (5 / 4 : ℝ) * R := by
  have hlo : (9 / 8 : ℝ) * R ≤ (laneBGridRadius R : ℝ) :=
    Int.le_ceil _
  have hhi : (laneBGridRadius R : ℝ) < (9 / 8 : ℝ) * R + 1 :=
    Int.ceil_lt_add_one _
  constructor <;> dsimp [laneBGridRadius] at * <;> linarith

theorem laneB_grid_buffer_inner {R : ℝ} (hR : 24 ≤ R) :
    (17 / 16 : ℝ) * R ≤ (laneBGridRadius R : ℝ) - 1 := by
  have hlo : (9 / 8 : ℝ) * R ≤ (laneBGridRadius R : ℝ) :=
    Int.le_ceil _
  linarith

 


theorem laneB_crossing_hits_grid_square
    {R : ℝ} (hR : 24 ≤ R) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hstart : ‖γ 0‖ = R) (hend : ‖γ 1‖ = 2 * R) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      laneBSquareGauge (γ t) = (laneBGridRadius R : ℝ) := by
  let m : ℝ := laneBGridRadius R
  have hb := laneB_grid_radius_bounds hR
  have hm0 : 0 < m := by dsimp [m]; linarith [hb.1]
  have hR0 : 0 < R := by linarith
  have hbegin : laneBSquareGauge (γ 0) ≤ m := by
    unfold laneBSquareGauge
    apply max_le
    · exact (Complex.abs_re_le_norm _).trans (by rw [hstart]; linarith [hb.1])
    · exact (Complex.abs_im_le_norm _).trans (by rw [hstart]; linarith [hb.1])
  have hend' : m ≤ laneBSquareGauge (γ 1) := by
    by_contra hnot
    have hmax : laneBSquareGauge (γ 1) ≤ m := le_of_lt (not_le.mp hnot)
    have hre : |(γ 1).re| ≤ m := (max_le_iff.mp hmax).1
    have him : |(γ 1).im| ≤ m := (max_le_iff.mp hmax).2
    have hsqr : ‖γ 1‖ ^ 2 = (γ 1).re ^ 2 + (γ 1).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hre2 : (γ 1).re ^ 2 ≤ m ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hre)
        (add_nonneg (abs_nonneg (γ 1).re) hm0.le), sq_abs (γ 1).re]
    have him2 : (γ 1).im ^ 2 ≤ m ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr him)
        (add_nonneg (abs_nonneg (γ 1).im) hm0.le), sq_abs (γ 1).im]
    have hm2 : m ^ 2 ≤ ((5 / 4 : ℝ) * R) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2)
        (add_nonneg hm0.le (by positivity : 0 ≤ (5 / 4 : ℝ) * R))]
    nlinarith [sq_pos_of_pos hR0]
  have hcont : ContinuousOn (laneBSquareGauge ∘ γ) (Set.Icc 0 1) :=
    laneB_squareGauge_continuous.comp_continuousOn hγ
  obtain ⟨t, ht, hval⟩ :=
    intermediate_value_Icc zero_le_one hcont ⟨hbegin, hend'⟩
  exact ⟨t, ht, hval⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
