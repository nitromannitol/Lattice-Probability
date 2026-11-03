/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistKernel at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel

/-!
# The white-noise kernels of the antiderivative field (task P2-EXIST, part 1)

Construction of the whole-plane GFF (route recorded in the P2-EXIST report): with `W` the
space-time white noise of `Field/WhiteNoise` and `p_s` the heat kernel, the GFF is
`h = √π ∫∫ p_{t/2}(·, y) W(dy, dt)` (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021,
`tightness.tex` l. 143–145, (2.2)), renormalised for large `t`. To obtain a random *distribution*
(a continuous linear functional on all of `𝓓(ℂ)` at once) we pair `W` with the kernels
`kerFun g (t, y) = √π 1_{t>0} ∫ g(u) (p_{t/2}(u, y) − 1_{t>1} p_{t/2}(0, y)) du`
for `g = 1_{[0,x]}` (signed rectangle indicators), obtaining a continuous field `F(x)` with
`⟨h, φ⟩ = ∫ F ∂₁∂₂φ`.

This file: the weighted Cauchy–Schwarz inequality and the two pointwise bounds on
`kerInner g t y = ∫ g(u) (p_{t/2}(u, y) − 1_{t>1} p_{t/2}(0, y)) du` used for the `L²` bound
(own elementary proofs of standard facts).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric

namespace LQGMetric
namespace GFFExist

open WhiteNoise

/-- **Weighted Cauchy–Schwarz**: `(∫ a b)² ≤ (∫ |a|) (∫ |a| b²)`. -/
lemma sq_integral_mul_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {a b : X → ℝ}
    (ha : Integrable a μ) (hab : Integrable (fun x => a x * b x) μ)
    (hab2 : Integrable (fun x => |a x| * b x ^ 2) μ) :
    (∫ x, a x * b x ∂μ) ^ 2 ≤ (∫ x, |a x| ∂μ) * ∫ x, |a x| * b x ^ 2 ∂μ := by
  set m := ∫ x, |a x| ∂μ with hm
  set c := ∫ x, |a x| * |b x| ∂μ with hc
  set S := ∫ x, |a x| * b x ^ 2 ∂μ with hS
  have hm0 : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  have hc0 : 0 ≤ c := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS0 : 0 ≤ S := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have habs : Integrable (fun x => |a x| * |b x|) μ := by
    simpa [abs_mul] using hab.abs
  have h1 : (∫ x, a x * b x ∂μ) ^ 2 ≤ c ^ 2 := by
    have := abs_integral_le_integral_abs (f := fun x => a x * b x) (μ := μ)
    simp only [abs_mul] at this
    exact sq_le_sq' (by linarith [neg_abs_le (∫ x, a x * b x ∂μ)])
      ((le_abs_self _).trans this)
  refine h1.trans ?_
  have hexp : ∫ x, |a x| * (m * |b x| - c) ^ 2 ∂μ = m * (m * S - c ^ 2) := by
    have e : ∀ x, |a x| * (m * |b x| - c) ^ 2 =
        m ^ 2 * (|a x| * b x ^ 2) - 2 * m * c * (|a x| * |b x|) + c ^ 2 * |a x| := fun x => by
      rw [show b x ^ 2 = |b x| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [e]
    have i1 : Integrable (fun x => m ^ 2 * (|a x| * b x ^ 2)) μ := hab2.const_mul _
    have i2 : Integrable (fun x => 2 * m * c * (|a x| * |b x|)) μ := habs.const_mul _
    have i3 : Integrable (fun x => c ^ 2 * |a x|) μ := ha.abs.const_mul _
    have i12 : Integrable (fun x => m ^ 2 * (|a x| * b x ^ 2) - 2 * m * c * (|a x| * |b x|)) μ :=
      i1.sub i2
    rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul]
    rw [← hm, ← hc, ← hS]; ring
  have h0 : 0 ≤ m * (m * S - c ^ 2) := by
    rw [← hexp]; exact integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  rcases hm0.lt_or_eq with hpos | hzero
  · have := (mul_nonneg_iff_of_pos_left hpos).mp h0
    linarith
  · -- `m = 0`: `a = 0` a.e., so `c = 0`
    have hae : (fun x => |a x|) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) ha.abs).mp hzero.symm
    have hc' : c = 0 := by
      rw [hc]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, zero_mul]
    rw [hc', ← hzero]; simp

lemma heatKernel_le (s : ℝ) (hs : 0 < s) (z w : ℂ) : heatKernel s z w ≤ (2 * Real.pi * s)⁻¹ := by
  unfold heatKernel
  have : Real.exp (-‖z - w‖ ^ 2 / (2 * s)) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖z - w‖]) (by positivity))
  have h0 : 0 ≤ (2 * Real.pi * s)⁻¹ := by positivity
  calc (2 * Real.pi * s)⁻¹ * Real.exp (-‖z - w‖ ^ 2 / (2 * s)) ≤ (2 * Real.pi * s)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left this h0
    _ = _ := mul_one _

/-- `∫ (p_s(u, y) − p_s(0, y))² dy = 2 (p_{2s}(0,0) − p_{2s}(u,0))`. -/
lemma integral_sq_heatKernel_sub (s : ℝ) (hs : 0 < s) (u : ℂ) :
    ∫ y, (heatKernel s u y - heatKernel s 0 y) ^ 2 =
      2 * (heatKernel (2 * s) 0 0 - heatKernel (2 * s) u 0) := by
  have e : ∀ y, (heatKernel s u y - heatKernel s 0 y) ^ 2 =
      heatKernel s u y * heatKernel s u y - 2 * (heatKernel s u y * heatKernel s 0 y) +
        heatKernel s 0 y * heatKernel s 0 y := fun y => by ring
  simp_rw [e]
  have i1 := integrable_heatKernel_mul_heatKernel s hs u u
  have i2 : Integrable (fun y => 2 * (heatKernel s u y * heatKernel s 0 y)) :=
    (integrable_heatKernel_mul_heatKernel s hs u 0).const_mul _
  have i12 : Integrable (fun y => heatKernel s u y * heatKernel s u y -
      2 * (heatKernel s u y * heatKernel s 0 y)) := i1.sub i2
  rw [integral_add i12 (integrable_heatKernel_mul_heatKernel s hs 0 0), integral_sub i1 i2,
    integral_const_mul,
    integral_heatKernel_mul_heatKernel s hs, integral_heatKernel_mul_heatKernel s hs,
    integral_heatKernel_mul_heatKernel s hs]
  have : heatKernel (2 * s) u u = heatKernel (2 * s) 0 0 := by simp [heatKernel]
  rw [this]; ring

/-- `∫ (p_s(u, y) − p_s(0, y))² dy ≤ ‖u‖² / (8π s²)`. -/
lemma integral_sq_heatKernel_sub_le (s : ℝ) (hs : 0 < s) (u : ℂ) :
    ∫ y, (heatKernel s u y - heatKernel s 0 y) ^ 2 ≤ ‖u‖ ^ 2 / (8 * Real.pi * s ^ 2) := by
  rw [integral_sq_heatKernel_sub s hs]
  have hx : 1 - Real.exp (-(‖u‖ ^ 2 / (4 * s))) ≤ ‖u‖ ^ 2 / (4 * s) := by
    linarith [Real.add_one_le_exp (-(‖u‖ ^ 2 / (4 * s)))]
  unfold heatKernel
  simp only [sub_zero, norm_zero]
  have h1 : -‖u‖ ^ 2 / (2 * (2 * s)) = -(‖u‖ ^ 2 / (4 * s)) := by ring
  rw [h1, show ((0 : ℝ) ^ 2) = 0 by norm_num, neg_zero, zero_div, Real.exp_zero, mul_one]
  have hpi := Real.pi_pos
  have h2 : 2 * ((2 * Real.pi * (2 * s))⁻¹ - (2 * Real.pi * (2 * s))⁻¹ *
      Real.exp (-(‖u‖ ^ 2 / (4 * s)))) =
      (2 * Real.pi * s)⁻¹ * (1 - Real.exp (-(‖u‖ ^ 2 / (4 * s)))) := by
    field_simp
  rw [h2]
  calc (2 * Real.pi * s)⁻¹ * (1 - Real.exp (-(‖u‖ ^ 2 / (4 * s))))
      ≤ (2 * Real.pi * s)⁻¹ * (‖u‖ ^ 2 / (4 * s)) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖u‖ ^ 2 / (8 * Real.pi * s ^ 2) := by field_simp; ring

/-! ### The kernels -/

/-- `∫ g(u) (p_{t/2}(u, y) − 1_{t>1} p_{t/2}(0, y)) du` -/
def kerInner (g : ℂ → ℝ) (t : ℝ) (y : ℂ) : ℝ :=
  ∫ u, g u * (heatKernel (t / 2) u y - (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 y) t)

/-- `kerFun g (t, y) = √π 1_{t>0} kerInner g t y` -/
def kerFun (g : ℂ → ℝ) (q : ℝ × ℂ) : ℝ :=
  Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator (fun t => kerInner g t q.2) q.1

variable {g : ℂ → ℝ} {M : ℝ}

lemma integrable_mul_heat (hgi : Integrable g) {s : ℝ} (hs : 0 < s) (c : ℝ) (y : ℂ) :
    Integrable fun u => g u * (heatKernel s u y - c * heatKernel s 0 y) := by
  refine hgi.mul_of_top_left (memLp_top_of_bound (by unfold heatKernel; fun_prop)
    ((2 * Real.pi * s)⁻¹ + |c| * (2 * Real.pi * s)⁻¹) (Eventually.of_forall fun u => ?_))
  rw [Real.norm_eq_abs]
  have h1 := heatKernel_le s hs u y
  have h2 := heatKernel_le s hs 0 y
  have h3 := heatKernel_nonneg s hs.le u y
  have h4 := heatKernel_nonneg s hs.le 0 y
  calc |heatKernel s u y - c * heatKernel s 0 y| ≤ |heatKernel s u y| + |c * heatKernel s 0 y| :=
        abs_sub _ _
    _ ≤ _ := by
        rw [abs_of_nonneg h3, abs_mul, abs_of_nonneg h4]
        gcongr

/-- `0 < t ≤ 1`: `kerInner g t y ² ≤ ∫ g(u)² p_{t/2}(u, y) du`. -/
lemma sq_kerInner_le_small (hgi : Integrable g) (hgb : ∀ u, |g u| ≤ M) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) (y : ℂ) :
    kerInner g t y ^ 2 ≤ ∫ u, g u ^ 2 * heatKernel (t / 2) u y := by
  have hs : 0 < t / 2 := by linarith
  have hind : (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 y) t = 0 :=
    indicator_of_notMem (by simpa using ht1) _
  unfold kerInner
  simp_rw [hind, sub_zero]
  have hpi : Integrable fun u => heatKernel (t / 2) u y := by
    simpa [heatKernel_symm _ _ y] using integrable_heatKernel (t / 2) hs y
  have hp1 : ∫ u, heatKernel (t / 2) u y = 1 := by
    simpa [heatKernel_symm _ _ y] using integral_heatKernel (t / 2) hs y
  have hgb' : ∀ u, ‖g u‖ ≤ M := fun u => by rw [Real.norm_eq_abs]; exact hgb u
  have hgm : AEStronglyMeasurable g volume := hgi.aestronglyMeasurable
  have hab : Integrable fun u => heatKernel (t / 2) u y * g u :=
    hpi.mul_of_top_left (memLp_top_of_bound hgm M (Eventually.of_forall hgb'))
  have hab2 : Integrable fun u => |heatKernel (t / 2) u y| * g u ^ 2 := by
    refine hpi.abs.mul_of_top_left (memLp_top_of_bound (hgm.pow 2) (M ^ 2)
      (Eventually.of_forall fun u => ?_))
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgb u) 2
  have := sq_integral_mul_le hpi hab hab2
  have habs : ∀ u, |heatKernel (t / 2) u y| = heatKernel (t / 2) u y := fun u =>
    abs_of_nonneg (heatKernel_nonneg _ hs.le _ _)
  simp_rw [habs, hp1, one_mul] at this
  calc (∫ u, g u * heatKernel (t / 2) u y) ^ 2 = (∫ u, heatKernel (t / 2) u y * g u) ^ 2 := by
        simp_rw [mul_comm (g _)]
    _ ≤ _ := this
    _ = _ := by simp_rw [mul_comm (heatKernel _ _ _)]

/-- `t > 1`: `kerInner g t y ² ≤ (∫ |g|) ∫ |g(u)| (p_{t/2}(u, y) − p_{t/2}(0, y))² du`. -/
lemma sq_kerInner_le_large (hgi : Integrable g) {t : ℝ} (ht1 : 1 < t) (y : ℂ) :
    kerInner g t y ^ 2 ≤ (∫ u, |g u|) *
      ∫ u, |g u| * (heatKernel (t / 2) u y - heatKernel (t / 2) 0 y) ^ 2 := by
  have hs : 0 < t / 2 := by linarith
  have hind : (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 y) t = heatKernel (t / 2) 0 y :=
    indicator_of_mem (by simpa using ht1) _
  unfold kerInner
  simp_rw [hind]
  have hab := integrable_mul_heat hgi hs 1 y
  simp only [one_mul] at hab
  have hb : ∀ u, |heatKernel (t / 2) u y - heatKernel (t / 2) 0 y| ≤ (2 * Real.pi * (t / 2))⁻¹ :=
    fun u => abs_sub_le_iff.mpr ⟨by linarith [heatKernel_le _ hs u y, heatKernel_nonneg _ hs.le 0 y],
      by linarith [heatKernel_le _ hs 0 y, heatKernel_nonneg _ hs.le u y]⟩
  have hab2 : Integrable fun u => |g u| * (heatKernel (t / 2) u y - heatKernel (t / 2) 0 y) ^ 2 := by
    refine hgi.abs.mul_of_top_left (memLp_top_of_bound (by unfold heatKernel; fun_prop)
      ((2 * Real.pi * (t / 2))⁻¹ ^ 2) (Eventually.of_forall fun u => ?_))
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb u) 2
  exact sq_integral_mul_le hgi hab hab2

end GFFExist
end LQGMetric
