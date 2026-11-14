/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRectMotion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwelveNear
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Blocks

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

private theorem laneC_translate_set (x y a b : ℝ) :
    (fun z : ℂ => z + (⟨x, y⟩ : ℂ)) '' (rectAB a b).toSet =
      (⟨x, y, a, b, true⟩ : MarkedRect).toSet := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, mem_Icc,
      Complex.add_re, Complex.add_im] at hw ⊢
    rcases hw with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · intro hz
    refine ⟨z - ⟨x, y⟩, ?_, by ring⟩
    simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, mem_Icc,
      Complex.sub_re, Complex.sub_im] at hz ⊢
    rcases hz with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem laneC_translate_side₁ (x y a b : ℝ) :
    (fun z : ℂ => z + (⟨x, y⟩ : ℂ)) '' (rectAB a b).side₁ =
      (⟨x, y, a, b, true⟩ : MarkedRect).side₁ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp [rectAB, MarkedRect.side₁, Complex.add_re, Complex.add_im] at hw ⊢
    rcases hw with ⟨h₁, ⟨h₂, h₃⟩⟩
    have hwre : w.re = 0 := h₁
    change w.re + x = x ∧ y ≤ w.im + y ∧ w.im + y ≤ y + b
    exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩
  · intro hz
    refine ⟨z - ⟨x, y⟩, ?_, by ring⟩
    simp [rectAB, MarkedRect.side₁, Complex.sub_re, Complex.sub_im] at hz ⊢
    rcases hz with ⟨h₁, ⟨h₂, h₃⟩⟩
    have hzre : z.re = x := h₁
    change z.re - x = 0 ∧ 0 ≤ z.im - y ∧ z.im - y ≤ b
    exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩

private theorem laneC_translate_side₂ (x y a b : ℝ) :
    (fun z : ℂ => z + (⟨x, y⟩ : ℂ)) '' (rectAB a b).side₂ =
      (⟨x, y, a, b, true⟩ : MarkedRect).side₂ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp [rectAB, MarkedRect.side₂, Complex.add_re, Complex.add_im] at hw ⊢
    rcases hw with ⟨h₁, ⟨h₂, h₃⟩⟩
    have hwre : w.re = a := h₁
    change w.re + x = x + a ∧ y ≤ w.im + y ∧ w.im + y ≤ y + b
    exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩
  · intro hz
    refine ⟨z - ⟨x, y⟩, ?_, by ring⟩
    simp [rectAB, MarkedRect.side₂, Complex.sub_re, Complex.sub_im] at hz ⊢
    rcases hz with ⟨h₁, ⟨h₂, h₃⟩⟩
    have hzre : z.re = x + a := h₁
    change z.re - x = a ∧ 0 ≤ z.im - y ∧ z.im - y ≤ b
    exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩

private theorem laneC_rotate_set (x y a b : ℝ) :
    (fun z : ℂ => (circI : ℂ) * z + (⟨x + b, y⟩ : ℂ)) '' (rectAB a b).toSet =
      (⟨x, y, b, a, false⟩ : MarkedRect).toSet := by
  ext z
  rw [mem_image_motion]
  simp only [coe_circI, Complex.inv_I, MarkedRect.toSet, rectAB,
    Complex.mem_reProdIm, mem_Icc, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, sub_zero, zero_sub, neg_mul,
    one_mul, neg_neg]
  constructor <;> intro h <;> rcases h with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem laneC_rotate_side₁ (x y a b : ℝ) :
    (fun z : ℂ => (circI : ℂ) * z + (⟨x + b, y⟩ : ℂ)) '' (rectAB a b).side₁ =
      (⟨x, y, b, a, false⟩ : MarkedRect).side₁ := by
  ext z
  rw [mem_image_motion]
  simp only [coe_circI, Complex.inv_I, MarkedRect.side₁, rectAB,
    ite_true, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
    mem_Icc, mem_singleton_iff, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, sub_zero, zero_sub, neg_mul,
    one_mul, neg_neg]
  constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;>
    (try constructor) <;> linarith [h.1, h.2]

private theorem laneC_rotate_side₂ (x y a b : ℝ) :
    (fun z : ℂ => (circI : ℂ) * z + (⟨x + b, y⟩ : ℂ)) '' (rectAB a b).side₂ =
      (⟨x, y, b, a, false⟩ : MarkedRect).side₂ := by
  ext z
  rw [mem_image_motion]
  simp only [coe_circI, Complex.inv_I, MarkedRect.side₂, rectAB,
    ite_true, Bool.false_eq_true, ite_false, Complex.mem_reProdIm,
    mem_Icc, mem_singleton_iff, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
    zero_mul, zero_add, add_zero, sub_zero, zero_sub, neg_mul,
    one_mul, neg_neg]
  constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;>
    (try constructor) <;> linarith [h.1, h.2]

theorem laneC_rectLen_mrect_horizontal {ξ : ℝ} {f : ℂ → ℝ}
    (x y a b : ℝ) :
    (rectLen ξ f ⟨x, y, a, b, true⟩).toReal =
      T20B.mrectLen ξ f 0 1 (⟨x, y⟩ : ℂ) a b := by
  unfold rectLen T20B.mrectLen
  have hm : T20B.mot 0 1 (⟨x, y⟩ : ℂ) =
      (fun z : ℂ => z + (⟨x, y⟩ : ℂ)) := by
    funext z
    simp [T20B.mot]
  rw [hm, laneC_translate_set, laneC_translate_side₁, laneC_translate_side₂]

theorem laneC_rectLen_mrect_vertical {ξ : ℝ} {f : ℂ → ℝ}
    (x y a b : ℝ) :
    (rectLen ξ f ⟨x, y, b, a, false⟩).toReal =
      T20B.mrectLen ξ f 0 circI (⟨x + b, y⟩ : ℂ) a b := by
  unfold rectLen T20B.mrectLen
  have hm : T20B.mot 0 circI (⟨x + b, y⟩ : ℂ) =
      (fun z : ℂ => (circI : ℂ) * z + (⟨x + b, y⟩ : ℂ)) := by
    funext z
    simp [T20B.mot]
  rw [hm, laneC_rotate_set, laneC_rotate_side₁, laneC_rotate_side₂]

def laneCTwelveMotionU (j : Fin 12) : Circle :=
  if (laneCDoublePrimeTwelveRect j).horiz then 1 else circI

def laneCTwelveMotionC (j : Fin 12) : ℂ :=
  let R := laneCDoublePrimeTwelveRect j
  if R.horiz then ⟨R.x0, R.y0⟩ else ⟨R.x0 + R.w, R.y0⟩

theorem laneC_twelve_rect_mrect (ξ : ℝ) (f : ℂ → ℝ) (j : Fin 12) :
    (rectLen ξ f (laneCDoublePrimeTwelveRect j)).toReal =
      T20B.mrectLen ξ f 0 (laneCTwelveMotionU j)
        (laneCTwelveMotionC j) 3 1 := by
  fin_cases j <;>
    simp [laneCDoublePrimeTwelveRect, laneCDoublePrimeLongRect,
      laneCTopConnector, laneCBottomConnector, laneCLeftConnector,
      laneCRightConnector, laneCTwelveMotionU, laneCTwelveMotionC,
      laneC_rectLen_mrect_horizontal, laneC_rectLen_mrect_vertical]

end SupercriticalLQGUniqueness.B2.DG20Conc
