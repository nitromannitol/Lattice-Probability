/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7Gauss1D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareL1
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareImg

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Real Set
open LQGMetric LQGMetric.HeatSq

namespace SupercriticalLQGUniqueness.B2.QPos.P7

lemma gauss1_neg (s z : ℝ) : gauss1 s (-z) = gauss1 s z := by
  unfold gauss1; rw [neg_sq]

lemma gauss1_sub_comm (s u w : ℝ) : gauss1 s (w - u) = gauss1 s (u - w) := by
  rw [← neg_sub, gauss1_neg]

lemma gauss1_pos {s : ℝ} (hs : 0 < s) (z : ℝ) : 0 < gauss1 s z := by
  unfold gauss1
  have : 0 < Real.sqrt (2 * π * s) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma integrable_gauss1_sub {s : ℝ} (hs : 0 < s) (u : ℝ) :
    Integrable (fun w => gauss1 s (u - w)) :=
  Integrable.of_integral_ne_zero (by rw [integral_gauss1_sub hs]; exact one_ne_zero)

 
lemma integral_gauss1_sub_sq {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ∫ w, gauss1 s (u - w) ^ 2 = gauss1 (2 * s) 0 := by
  have h := integral_gauss1_mul_gauss1 s s hs hs u u
  rw [show s + s = 2 * s by ring, sub_self] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [sq, gauss1_sub_comm s u w]

lemma integrable_gauss1_sub_sq {s : ℝ} (hs : 0 < s) (u : ℝ) :
    Integrable (fun w => gauss1 s (u - w) ^ 2) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_gauss1_sub_sq hs]; exact (gauss1_pos (by positivity) 0).ne')

lemma hasDerivAt_gauss1 {s : ℝ} (hs : 0 < s) (z : ℝ) :
    HasDerivAt (gauss1 s) (-(z / s) * gauss1 s z) z := by
  have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / (2 * s)) (-(2 * z) / (2 * s)) z := by
    have := ((hasDerivAt_pow 2 z).neg).div_const (2 * s)
    simpa using this
  have h2 := ((Real.hasDerivAt_exp _).comp z h1).const_mul (Real.sqrt (2 * π * s))⁻¹
  have e : -(z / s) * gauss1 s z = (Real.sqrt (2 * π * s))⁻¹ *
      (Real.exp (-z ^ 2 / (2 * s)) * (-(2 * z) / (2 * s))) := by
    unfold gauss1; field_simp
  rw [e]
  exact h2

 
lemma abs_deriv_gauss1_le {s : ℝ} (hs : 0 < s) {ξ z : ℝ} (h : |ξ - z| ≤ Real.sqrt s) :
    |(-(ξ / s) * gauss1 s ξ)| ≤ 4 * (Real.sqrt s)⁻¹ * gauss1 (4 * s) z := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hπ := Real.pi_pos
  
  have hx1 : ξ ^ 2 ≤ 2 * s * Real.exp (ξ ^ 2 / (2 * s)) := by
    have := Real.add_one_le_exp (ξ ^ 2 / (2 * s))
    have h0 : 0 ≤ ξ ^ 2 / (2 * s) := by positivity
    have e : ξ ^ 2 = 2 * s * (ξ ^ 2 / (2 * s)) := by field_simp
    nlinarith
  have hx2 : |ξ| ≤ Real.sqrt 2 * Real.sqrt s * Real.exp (ξ ^ 2 / (4 * s)) := by
    have hr : (Real.sqrt 2 * Real.sqrt s * Real.exp (ξ ^ 2 / (4 * s))) ^ 2 =
        2 * s * Real.exp (ξ ^ 2 / (2 * s)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hsq, ← Real.exp_nat_mul]
      congr 2; push_cast; field_simp; ring
    refine (pow_le_pow_iff_left₀ (abs_nonneg ξ) (by positivity) two_ne_zero).mp ?_
    rw [sq_abs, hr]; exact hx1
  
  have hshift : z ^ 2 / 2 - s ≤ ξ ^ 2 := by
    have h2 : (ξ - z) ^ 2 ≤ s := by
      rw [← sq_abs, ← hsq]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [sq_nonneg (ξ + z), sq_nonneg (2 * ξ - z)]
  have hexp : Real.exp (-ξ ^ 2 / (2 * s)) * Real.exp (ξ ^ 2 / (4 * s)) ≤
      Real.exp (1 / 4) * Real.exp (-z ^ 2 / (8 * s)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : -ξ ^ 2 / (2 * s) + ξ ^ 2 / (4 * s) = -ξ ^ 2 / (4 * s) := by field_simp; ring
    rw [this]
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have he14 : Real.exp (1 / 4) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by positivity) (by norm_num), ← Real.exp_nat_mul]
    have h := Real.add_one_le_exp (-1 / 2 : ℝ)
    have hpos := Real.exp_pos (-1 / 2 : ℝ)
    have e : Real.exp ((2 : ℕ) * (1 / 4 : ℝ)) * Real.exp (-1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hg4 : gauss1 (4 * s) z = (2 : ℝ)⁻¹ * (Real.sqrt (2 * π * s))⁻¹ *
      Real.exp (-z ^ 2 / (8 * s)) := by
    unfold gauss1
    rw [show 2 * π * (4 * s) = 2 ^ 2 * (2 * π * s) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      show 2 * (4 * s) = 8 * s by ring, mul_inv]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have key : |ξ| * Real.exp (-ξ ^ 2 / (2 * s)) ≤
      2 * Real.sqrt s * Real.exp (-z ^ 2 / (8 * s)) := by
    calc |ξ| * Real.exp (-ξ ^ 2 / (2 * s))
        ≤ (Real.sqrt 2 * Real.sqrt s * Real.exp (ξ ^ 2 / (4 * s))) *
            Real.exp (-ξ ^ 2 / (2 * s)) :=
          mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
      _ = Real.sqrt 2 * Real.sqrt s *
            (Real.exp (-ξ ^ 2 / (2 * s)) * Real.exp (ξ ^ 2 / (4 * s))) := by ring
      _ ≤ Real.sqrt 2 * Real.sqrt s * (Real.sqrt 2 * Real.exp (-z ^ 2 / (8 * s))) := by
          exact mul_le_mul_of_nonneg_left
            (hexp.trans (mul_le_mul_of_nonneg_right he14 (Real.exp_pos _).le)) (by positivity)
      _ = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt s * Real.exp (-z ^ 2 / (8 * s)) := by ring
      _ = 2 * Real.sqrt s * Real.exp (-z ^ 2 / (8 * s)) := by rw [hsqrt2]
  rw [abs_mul, abs_neg, abs_div, abs_of_pos hs, abs_of_pos (gauss1_pos hs ξ), hg4]
  unfold gauss1
  have hA : 0 < Real.sqrt (2 * π * s) := Real.sqrt_pos.mpr (by positivity)
  calc |ξ| / s * ((Real.sqrt (2 * π * s))⁻¹ * Real.exp (-ξ ^ 2 / (2 * s)))
      = (Real.sqrt (2 * π * s))⁻¹ * (|ξ| * Real.exp (-ξ ^ 2 / (2 * s))) / s := by ring
    _ ≤ (Real.sqrt (2 * π * s))⁻¹ * (2 * Real.sqrt s * Real.exp (-z ^ 2 / (8 * s))) / s := by
        gcongr
    _ = 2 * (Real.sqrt (2 * π * s))⁻¹ * Real.exp (-z ^ 2 / (8 * s)) *
          (Real.sqrt s / s) := by ring
    _ = 4 * (Real.sqrt s)⁻¹ * ((2 : ℝ)⁻¹ * (Real.sqrt (2 * π * s))⁻¹ *
          Real.exp (-z ^ 2 / (8 * s))) := by
        rw [Real.sqrt_div_self']; ring

 

theorem abs_gauss1_sub_le {s : ℝ} (hs : 0 < s) {z z' : ℝ} (h : |z - z'| ≤ Real.sqrt s) :
    |gauss1 s z - gauss1 s z'| ≤ 4 * (Real.sqrt s)⁻¹ * gauss1 (4 * s) z' * |z - z'| := by
  have hconv : Convex ℝ (uIcc z' z) := convex_uIcc z' z
  have hd : ∀ ξ ∈ uIcc z' z, HasDerivWithinAt (gauss1 s) (-(ξ / s) * gauss1 s ξ) (uIcc z' z) ξ :=
    fun ξ _ => (hasDerivAt_gauss1 hs ξ).hasDerivWithinAt
  have hb : ∀ ξ ∈ uIcc z' z, ‖-(ξ / s) * gauss1 s ξ‖ ≤ 4 * (Real.sqrt s)⁻¹ * gauss1 (4 * s) z' := by
    intro ξ hξ
    rw [Real.norm_eq_abs]
    refine abs_deriv_gauss1_le hs ?_
    refine le_trans ?_ h
    rw [mem_uIcc] at hξ
    rcases hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_uIcc) (right_mem_uIcc)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

end SupercriticalLQGUniqueness.B2.QPos.P7
