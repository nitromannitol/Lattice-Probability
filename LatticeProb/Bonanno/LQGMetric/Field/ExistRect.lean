/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistRect at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernelL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Signed rectangle indicators and the increments of the antiderivative kernels (P2-EXIST, part 4)

`rectInd x u = s(x.re, u.re) s(x.im, u.im)`, `s(a, b) = 1_{0 < b ≤ a} − 1_{a < b ≤ 0}`, is the signed
indicator of the rectangle `[0, x]` (so `∫ rectInd x · f = ∫_0^{x.re} ∫_0^{x.im} f`). The field
`F(x) = W(kerFun (rectInd x))` is the antiderivative `∂₁⁻¹∂₂⁻¹ h` of the GFF.

Main result: `sq_norm_kerFun_rect_sub_le`, the increment bound
`‖kerFun (rectInd x) − kerFun (rectInd x')‖² ≤ C_A ‖x − x'‖` for `x, x'` with coordinates in
`[−A, A]` (the Kolmogorov input). Own elementary proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric

namespace LQGMetric
namespace GFFExist

open WhiteNoise

/-- `s(a, b) = 1_{0 < b ≤ a} − 1_{a < b ≤ 0}` -/
def sgnInd (a b : ℝ) : ℝ := if 0 < b ∧ b ≤ a then 1 else if a < b ∧ b ≤ 0 then -1 else 0

/-- the signed indicator of the rectangle `[0, x]` -/
def rectInd (x u : ℂ) : ℝ := sgnInd x.re u.re * sgnInd x.im u.im

lemma measurable_sgnInd (a : ℝ) : Measurable (sgnInd a) := by
  unfold sgnInd
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)

lemma measurable_rectInd (x : ℂ) : Measurable (rectInd x) :=
  ((measurable_sgnInd _).comp Complex.measurable_re).mul
    ((measurable_sgnInd _).comp Complex.measurable_im)

lemma sgnInd_of_pos {a b : ℝ} (hb : 0 < b) : sgnInd a b = if b ≤ a then 1 else 0 := by
  unfold sgnInd
  by_cases h : b ≤ a
  · simp [hb, h]
  · have : ¬ (a < b ∧ b ≤ 0) := fun h' => by linarith [h'.2]
    simp [h, this]

lemma sgnInd_of_nonpos {a b : ℝ} (hb : b ≤ 0) : sgnInd a b = if a < b then -1 else 0 := by
  unfold sgnInd
  have : ¬ (0 < b ∧ b ≤ a) := fun h' => by linarith [h'.1]
  by_cases h : a < b
  · simp [this, h, hb]
  · simp [this, h]

lemma abs_sgnInd_le_indicator {a A : ℝ} (ha : |a| ≤ A) (b : ℝ) :
    |sgnInd a b| ≤ (Icc (-A) A).indicator (fun _ => (1 : ℝ)) b := by
  obtain ⟨h1, h2⟩ := abs_le.mp ha
  rcases lt_or_ge 0 b with hb | hb
  · rw [sgnInd_of_pos hb]
    split_ifs with c
    · rw [indicator_of_mem (show b ∈ Icc (-A) A from ⟨by linarith, by linarith⟩)]; norm_num
    · simpa using indicator_nonneg (fun _ _ => zero_le_one) b
  · rw [sgnInd_of_nonpos hb]
    split_ifs with c
    · rw [indicator_of_mem (show b ∈ Icc (-A) A from ⟨by linarith, by linarith⟩)]; norm_num
    · simpa using indicator_nonneg (fun _ _ => zero_le_one) b

lemma abs_sgnInd_le_one (a b : ℝ) : |sgnInd a b| ≤ 1 := by
  unfold sgnInd; split_ifs <;> norm_num

lemma abs_sgnInd_sub_le (a a' b : ℝ) :
    |sgnInd a b - sgnInd a' b| ≤ (uIoc a a').indicator (fun _ => (1 : ℝ)) b := by
  have h0 : (0 : ℝ) ≤ (uIoc a a').indicator (fun _ => (1 : ℝ)) b :=
    indicator_nonneg (fun _ _ => zero_le_one) b
  rcases lt_or_ge 0 b with hb | hb
  · rw [sgnInd_of_pos hb, sgnInd_of_pos hb]
    split_ifs with c1 c2 c2
    · simpa using h0
    · rw [indicator_of_mem (mem_uIoc.2 (Or.inr ⟨by linarith, c1⟩))]; norm_num
    · rw [indicator_of_mem (mem_uIoc.2 (Or.inl ⟨by linarith, c2⟩))]; norm_num
    · simpa using h0
  · rw [sgnInd_of_nonpos hb, sgnInd_of_nonpos hb]
    split_ifs with c1 c2 c2
    · simpa using h0
    · rw [indicator_of_mem (mem_uIoc.2 (Or.inl ⟨c1, by linarith⟩))]; norm_num
    · rw [indicator_of_mem (mem_uIoc.2 (Or.inr ⟨c2, by linarith⟩))]; norm_num
    · simpa using h0

lemma sgnInd_eq_zero {a b : ℝ} (hb : |a| < |b|) : sgnInd a b = 0 := by
  have h1 := le_abs_self a
  have h2 := neg_abs_le a
  rcases lt_or_ge 0 b with hb0 | hb0
  · rw [sgnInd_of_pos hb0, abs_of_pos hb0] at *
    rw [if_neg (by linarith)]
  · rw [sgnInd_of_nonpos hb0]
    rw [abs_of_nonpos hb0] at hb
    rw [if_neg (by linarith)]

lemma rectInd_bddSupp (x : ℂ) : BddSupp (rectInd x) 1 (|x.re| + |x.im|) where
  meas := measurable_rectInd x
  bdd u := by
    rw [rectInd, abs_mul]
    exact mul_le_one₀ (abs_sgnInd_le_one _ _) (abs_nonneg _) (abs_sgnInd_le_one _ _)
  supp u hu := by
    have hu' : |x.re| + |x.im| < |u.re| + |u.im| :=
      hu.trans_le (Complex.norm_le_abs_re_add_abs_im u)
    rcases lt_or_ge |x.re| |u.re| with h | h
    · rw [rectInd, sgnInd_eq_zero h, zero_mul]
    · rw [rectInd, sgnInd_eq_zero (a := x.im) (b := u.im) (by linarith), mul_zero]

/-- `|rectInd x − rectInd x'|` is dominated by two thin rectangles. -/
lemma abs_rectInd_sub_le {x x' : ℂ} {A : ℝ} (h2 : |x.im| ≤ A) (h3 : |x'.re| ≤ A) (u : ℂ) :
    |rectInd x u - rectInd x' u| ≤
      (uIoc x.re x'.re).indicator (fun _ => (1 : ℝ)) u.re *
          (Icc (-A) A).indicator (fun _ => (1 : ℝ)) u.im +
        (Icc (-A) A).indicator (fun _ => (1 : ℝ)) u.re *
          (uIoc x.im x'.im).indicator (fun _ => (1 : ℝ)) u.im := by
  have e : rectInd x u - rectInd x' u =
      (sgnInd x.re u.re - sgnInd x'.re u.re) * sgnInd x.im u.im +
        sgnInd x'.re u.re * (sgnInd x.im u.im - sgnInd x'.im u.im) := by
    unfold rectInd; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul (abs_sgnInd_sub_le _ _ _) (abs_sgnInd_le_indicator h2 _) (abs_nonneg _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact mul_le_mul (abs_sgnInd_le_indicator h3 _) (abs_sgnInd_sub_le _ _ _) (abs_nonneg _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)

/-- integrals over `ℂ` as integrals over `ℝ × ℝ` -/
lemma integral_complex_eq (F : ℂ → ℝ) : ∫ u, F u = ∫ p : ℝ × ℝ, F ⟨p.1, p.2⟩ := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' (g := F)
  rw [← h]
  congr 1

lemma integrable_complex_iff {F : ℂ → ℝ} :
    Integrable F ↔ Integrable (fun p : ℝ × ℝ => F ⟨p.1, p.2⟩) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := F)
  rw [← h]
  have : (F ∘ Complex.measurableEquivRealProd.symm) = fun p : ℝ × ℝ => F ⟨p.1, p.2⟩ := by
    funext p; simp only [Function.comp_apply]
    congr 1
  rw [this]

lemma integral_indicator_mul_indicator (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hs' : volume s ≠ ⊤) (ht' : volume t ≠ ⊤) :
    Integrable (fun u : ℂ => s.indicator (fun _ => (1 : ℝ)) u.re *
      t.indicator (fun _ => (1 : ℝ)) u.im) ∧
    ∫ u : ℂ, s.indicator (fun _ => (1 : ℝ)) u.re * t.indicator (fun _ => (1 : ℝ)) u.im =
      volume.real s * volume.real t := by
  have hi1 : Integrable (s.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hs).2 (integrableOn_const hs')
  have hi2 : Integrable (t.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff ht).2 (integrableOn_const ht')
  refine ⟨integrable_complex_iff.2 (hi1.mul_prod hi2), ?_⟩
  rw [integral_complex_eq]
  simp only
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, integral_prod_mul,
    integral_indicator hs, integral_indicator ht, setIntegral_const, setIntegral_const]
  simp

/-- `∫ |rectInd x − rectInd x'| ≤ 2A (|Δre| + |Δim|) ≤ 4A ‖x − x'‖` -/
lemma integral_abs_rectInd_sub_le {x x' : ℂ} {A : ℝ} (h2 : |x.im| ≤ A) (h3 : |x'.re| ≤ A) :
    ∫ u, |rectInd x u - rectInd x' u| ≤ 4 * A * ‖x - x'‖ := by
  have hA : 0 ≤ A := (abs_nonneg _).trans h2
  obtain ⟨i1, e1⟩ := integral_indicator_mul_indicator (uIoc x.re x'.re) (Icc (-A) A)
    measurableSet_uIoc measurableSet_Icc (by simp) (by simp)
  obtain ⟨i2, e2⟩ := integral_indicator_mul_indicator (Icc (-A) A) (uIoc x.im x'.im)
    measurableSet_Icc measurableSet_uIoc (by simp) (by simp)
  have hint : Integrable fun u => |rectInd x u - rectInd x' u| :=
    (((rectInd_bddSupp x).integrable.sub (rectInd_bddSupp x').integrable)).abs
  refine (integral_mono hint (i1.add i2) (abs_rectInd_sub_le h2 h3)).trans ?_
  rw [integral_add' i1 i2, e1, e2]
  simp only [measureReal_def, Real.volume_uIoc, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (abs_nonneg _)]
  have hre : |x'.re - x.re| ≤ ‖x - x'‖ := by
    rw [abs_sub_comm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have him : |x'.im - x.im| ≤ ‖x - x'‖ := by
    rw [abs_sub_comm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
  nlinarith

end GFFExist
end LQGMetric
