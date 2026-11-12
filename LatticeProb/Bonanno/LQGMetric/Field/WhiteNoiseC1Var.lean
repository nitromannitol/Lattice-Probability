/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseC1Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1L2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scale-correct `L²` bounds for the gradient kernel of `φ_{a,b}` (task P2-DDDFFIELD)

For the gradient kernel `∂_e k_x(t, y) = 1_{[a²,b²]}(t) ∂_e p_{t/2}(x − y)` (`dqKernel a b e x 0`):

* `sq_norm_gradKernel_le`: `‖∂_e k_x‖² ≤ 4/(π a²)` (so `Var(a ∂_e φ_{a,b}(x)) ≤ 4`);
* `sq_norm_gradKernel_sub_le`: for `b ≤ 1`,
  `‖∂_e k_u − ∂_e k_v‖² ≤ 392/(π a⁴) e^{|u−v|²/a²} |u − v|²`.

These are the bounds behind the Fernique step of DDDF Prop. 3 (`tightness.tex` l. 329–345; DF
arXiv:1809.02607 l. 1828–1840, where `Var` and the increments of `∇φ_{0,n}` are controlled by
scaling). Own elementary proof: pointwise Gaussian bounds, the Gaussian integral over `ℂ`
(mathlib `GaussianFourier.integral_rexp_neg_mul_sq_norm`) and Fubini.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- `(∂_e g_s(v))² ≤ (2π²s³)⁻¹ e^{−|v|²/(2s)}`. -/
lemma sq_gkD_le {s : ℝ} (hs : 0 < s) {e : ℂ} (he : ‖e‖ ≤ 1) (v : ℂ) :
    gkD s e v ^ 2 ≤ (2 * Real.pi ^ 2 * s ^ 3)⁻¹ * Real.exp (-‖v‖ ^ 2 / (2 * s)) := by
  have hin : ⟪e, v⟫ ^ 2 ≤ ‖v‖ ^ 2 := by
    have := abs_real_inner_le_norm e v
    have h2 : |⟪e, v⟫| ≤ ‖v‖ := this.trans (by nlinarith [norm_nonneg v])
    nlinarith [abs_nonneg ⟪e, v⟫, sq_abs ⟪e, v⟫]
  have hk := mul_exp_neg_div_le (sq_nonneg ‖v‖) hs
  have hE : Real.exp (-‖v‖ ^ 2 / (2 * s)) ^ 2 = Real.exp (-‖v‖ ^ 2 / s) := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp; push_cast; ring
  have hpi := Real.pi_pos
  calc gkD s e v ^ 2 = ⟪e, v⟫ ^ 2 / s ^ 2 * (2 * Real.pi * s)⁻¹ ^ 2 *
        Real.exp (-‖v‖ ^ 2 / (2 * s)) ^ 2 := by unfold gkD gk; ring
    _ ≤ ‖v‖ ^ 2 / s ^ 2 * (2 * Real.pi * s)⁻¹ ^ 2 * Real.exp (-‖v‖ ^ 2 / s) := by
        rw [hE]; gcongr
    _ = (s ^ 2)⁻¹ * (2 * Real.pi * s)⁻¹ ^ 2 * (‖v‖ ^ 2 * Real.exp (-‖v‖ ^ 2 / s)) := by ring
    _ ≤ (s ^ 2)⁻¹ * (2 * Real.pi * s)⁻¹ ^ 2 * (2 * s * Real.exp (-‖v‖ ^ 2 / (2 * s))) := by
        gcongr
    _ = (2 * Real.pi ^ 2 * s ^ 3)⁻¹ * Real.exp (-‖v‖ ^ 2 / (2 * s)) := by field_simp

/-- Lipschitz bound of `∂_e g_s` around `v`: `|∂_e g_s(u − y) − ∂_e g_s(v − y)| ≤
B_s e^{δ²/(4s)} e^{−|v−y|²/(8s)} δ` with `δ = ‖u − v‖`. -/
lemma abs_gkD_sub_le {s : ℝ} (hs : 0 < s) {e : ℂ} (he : ‖e‖ ≤ 1) (u v y : ℂ) :
    |gkD s e (u - y) - gkD s e (v - y)| ≤ gkB s * Real.exp (‖u - v‖ ^ 2 / (4 * s)) *
      Real.exp (-‖v - y‖ ^ 2 / (8 * s)) * ‖u - v‖ := by
  set K := gkB s * Real.exp (‖u - v‖ ^ 2 / (4 * s)) * Real.exp (-‖v - y‖ ^ 2 / (8 * s)) with hK
  have hmv := (convex_closedBall (v - y) ‖u - v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := gkD s e) (f' := gkDD s e) (C := K)
    (fun w _ => (hasFDerivAt_gkD hs.ne' e w).hasFDerivWithinAt)
    (fun w hw => by
      refine (norm_gkDD_le hs he _).trans ?_
      rw [hK, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by unfold gkB; have := Real.pi_pos; positivity)
      have h := exp_shift_le (ρ := ‖u - v‖) (v := w) (y := -(v - y)) hs (by
        rw [← sub_eq_add_neg, ← dist_eq_norm]; exact Metric.mem_closedBall.1 hw)
      rwa [norm_neg] at h)
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm, show u - y - (v - y) = u - v by abel])
  rw [← Real.norm_eq_abs]
  refine hmv.trans (le_of_eq ?_)
  rw [show u - y - (v - y) = u - v by abel]

/-- The `(t, y)`-function `1_{[A,B]}(t) φ(t) e^{−|v−y|²/(ct)}`. -/
def gaussTime (A B : ℝ) (φ : ℝ → ℝ) (c : ℝ) (v : ℂ) : ℝ × ℂ → ℝ :=
  (Icc A B ×ˢ univ).indicator fun p => φ p.1 * Real.exp (-‖v - p.2‖ ^ 2 / (c * p.1))

lemma integral_exp_neg_norm_sub_sq {β : ℝ} (hβ : 0 < β) (v : ℂ) :
    ∫ y : ℂ, Real.exp (-‖v - y‖ ^ 2 / β) = Real.pi * β := by
  have e : ∀ y : ℂ, Real.exp (-‖v - y‖ ^ 2 / β) = Real.exp (-β⁻¹ * ‖y - v‖ ^ 2) := fun y => by
    rw [norm_sub_rev]; congr 1; field_simp
  simp_rw [e]
  rw [integral_sub_right_eq_self (fun y : ℂ => Real.exp (-β⁻¹ * ‖y‖ ^ 2)) v,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.mpr hβ)]
  simp only [Complex.finrank_real_complex]
  norm_num

/-- **Fubini for `gaussTime`**: integrable, with `∫∫ = ∫_A^B φ(t) π c t dt`. -/
lemma integrable_integral_gaussTime {A B : ℝ} (hA : 0 < A) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : ContinuousOn φ (Icc A B)) {c : ℝ} (hc : 0 < c) (v : ℂ) :
    Integrable (gaussTime A B φ c v) ∧
      ∫ p, gaussTime A B φ c v p = ∫ t in Icc A B, φ t * (Real.pi * (c * t)) := by
  set F := gaussTime A B φ c v with hF
  have hpos : ∀ t ∈ Icc A B, 0 < t := fun t ht => lt_of_lt_of_le hA ht.1
  have hsec : ∀ t, (fun y => F (t, y)) =
      fun y => (Icc A B).indicator φ t * Real.exp (-‖v - y‖ ^ 2 / (c * t)) := by
    intro t; funext y
    by_cases ht : t ∈ Icc A B <;> simp [hF, gaussTime, ht]
  have hy : ∀ t ∈ Icc A B, Integrable fun y : ℂ => Real.exp (-‖v - y‖ ^ 2 / (c * t)) := by
    intro t ht
    have h := (integrable_rexp_neg_mul_sq_norm_complex
      (inv_pos.mpr (mul_pos hc (hpos t ht)))).comp_sub_left v
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only; congr 1; field_simp
  have hinner : ∀ t, ∫ y, F (t, y) = (Icc A B).indicator
      (fun t => φ t * (Real.pi * (c * t))) t := by
    intro t
    rw [hsec t, integral_const_mul]
    by_cases ht : t ∈ Icc A B
    · rw [indicator_of_mem ht, indicator_of_mem ht,
        integral_exp_neg_norm_sub_sq (mul_pos hc (hpos t ht))]
    · simp [ht]
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ (measurableSet_Icc.prod MeasurableSet.univ)
    exact (hφm.comp measurable_fst).mul (by fun_prop)
  have hcont : ContinuousOn (fun t => φ t * (Real.pi * (c * t))) (Icc A B) :=
    hφ.mul (continuousOn_const.mul (continuousOn_const.mul continuousOn_id))
  have hint : Integrable F := by
    rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
      integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · rw [hsec t]
      by_cases ht : t ∈ Icc A B
      · exact (hy t ht).const_mul _
      · simp [ht]
    · have : (fun t => ∫ y, ‖F (t, y)‖) = (Icc A B).indicator
          (fun t => |φ t| * (Real.pi * (c * t))) := by
        funext t
        have hs' : ∀ y, F (t, y) = (Icc A B).indicator φ t * Real.exp (-‖v - y‖ ^ 2 / (c * t)) :=
          fun y => congrFun (hsec t) y
        simp_rw [hs']
        by_cases ht : t ∈ Icc A B
        · rw [indicator_of_mem ht]
          simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), indicator_of_mem ht]
          rw [integral_const_mul, integral_exp_neg_norm_sub_sq (mul_pos hc (hpos t ht))]
        · simp [ht]
      rw [this, integrable_indicator_iff measurableSet_Icc]
      exact (hφ.abs.mul (continuousOn_const.mul (continuousOn_const.mul continuousOn_id))
        ).integrableOn_compact isCompact_Icc
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod F hint]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Icc]

/-- `∫_A^B t⁻² dt ≤ A⁻¹`. -/
lemma integral_inv_sq_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ t in Icc A B, (t ^ 2)⁻¹ ≤ A⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -t⁻¹)]
  · simp only [neg_sub_neg]
    have : 0 < B⁻¹ := inv_pos.mpr (lt_of_lt_of_le hA hAB)
    linarith
  · intro t ht
    rw [uIcc_of_le hAB] at ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le hA ht.1).ne'
    have h := (hasDerivAt_inv ht0).neg
    rw [neg_neg] at h
    exact h
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hAB]
    exact (continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero 2 (lt_of_lt_of_le hA ht.1).ne'

/-- `‖f‖² = ∫ f²` for an `L²` class with a representative. -/
lemma sq_norm_eq_integral {f : WNSpace} {F : ℝ × ℂ → ℝ} (hf : (f : ℝ × ℂ → ℝ) =ᵐ[volume] F) :
    ‖f‖ ^ 2 = ∫ p, F p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf] with p hp
  rw [hp, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [sq]

/-- **Variance bound for the gradient kernel**: `‖∂_e k_x‖² ≤ 4/(π a²)`. -/
theorem sq_norm_gradKernel_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1)
    (x : ℂ) : ‖dqKernelL2 a b e x 0‖ ^ 2 ≤ 4 / (Real.pi * a ^ 2) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hpi := Real.pi_pos
  set φ : ℝ → ℝ := fun t => 4 / (Real.pi ^ 2 * t ^ 3) with hφ
  have hφm : Measurable φ := by rw [hφ]; fun_prop
  have hφc : ContinuousOn φ (Icc (a ^ 2) (b ^ 2)) := by
    rw [hφ]
    exact continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 3))
      fun t ht => by have := lt_of_lt_of_le ha2 ht.1; positivity
  obtain ⟨hHi, hHe⟩ := integrable_integral_gaussTime ha2 hφm hφc one_pos x
  rw [sq_norm_eq_integral (coeFn_dqKernelL2 ha hab he x 0)]
  have hle : ∀ p, dqKernel a b e x 0 p ^ 2 ≤ gaussTime (a ^ 2) (b ^ 2) φ 1 x p := by
    intro p
    rw [dqKernel_zero]
    unfold gaussTime
    by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
    · rw [indicator_of_mem hp, indicator_of_mem hp]
      have ht := lt_of_lt_of_le ha2 hp.1.1
      refine (sq_gkD_le (by positivity) he _).trans (le_of_eq ?_)
      rw [hφ]; simp only
      rw [show 2 * (p.1 / 2) = 1 * p.1 by ring]
      congr 1
      field_simp; ring
    · simp [indicator_of_notMem hp]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun p => sq_nonneg _) hHi
    (Eventually.of_forall hle)).trans ?_
  rw [hHe]
  calc ∫ t in Icc (a ^ 2) (b ^ 2), φ t * (Real.pi * (1 * t))
      = ∫ t in Icc (a ^ 2) (b ^ 2), 4 / Real.pi * (t ^ 2)⁻¹ := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        have := lt_of_lt_of_le ha2 ht.1
        rw [hφ]; simp only; field_simp
    _ = 4 / Real.pi * ∫ t in Icc (a ^ 2) (b ^ 2), (t ^ 2)⁻¹ := integral_const_mul _ _
    _ ≤ 4 / Real.pi * (a ^ 2)⁻¹ := by
        gcongr; exact integral_inv_sq_le ha2 hab2
    _ = 4 / (Real.pi * a ^ 2) := by field_simp

/-- **Increment bound for the gradient kernel** (`b ≤ 1`):
`‖∂_e k_u − ∂_e k_v‖² ≤ 392/(π a⁴) e^{|u−v|²/a²} |u − v|²`. -/
theorem sq_norm_gradKernel_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) {e : ℂ}
    (he : ‖e‖ ≤ 1) (u v : ℂ) :
    ‖dqKernelL2 a b e u 0 - dqKernelL2 a b e v 0‖ ^ 2 ≤
      392 / (Real.pi * a ^ 4) * Real.exp (‖u - v‖ ^ 2 / a ^ 2) * ‖u - v‖ ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [lt_of_lt_of_le ha hab]
  have hpi := Real.pi_pos
  set δ := ‖u - v‖ with hδ
  set φ : ℝ → ℝ := fun t => δ ^ 2 * gkB (t / 2) ^ 2 * Real.exp (δ ^ 2 / t) with hφ
  have hφm : Measurable φ := by rw [hφ]; unfold gkB; fun_prop
  have hφc : ContinuousOn φ (Icc (a ^ 2) (b ^ 2)) := by
    have hne : ∀ t ∈ Icc (a ^ 2) (b ^ 2), t ≠ 0 := fun t ht => (lt_of_lt_of_le ha2 ht.1).ne'
    rw [hφ]; unfold gkB
    refine (continuousOn_const.mul (ContinuousOn.pow ?_ 2)).mul
      ((continuousOn_const.div continuousOn_id hne).rexp)
    refine (continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.div_const 2))).div (continuousOn_const.mul
      ((continuousOn_id.div_const 2).pow 2)) fun t ht => ?_
    have := hne t ht; positivity
  obtain ⟨hHi, hHe⟩ := integrable_integral_gaussTime ha2 hφm hφc two_pos v
  have hsub : (⇑(dqKernelL2 a b e u 0 - dqKernelL2 a b e v 0) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun p => dqKernel a b e u 0 p - dqKernel a b e v 0 p := by
    filter_upwards [Lp.coeFn_sub (dqKernelL2 a b e u 0) (dqKernelL2 a b e v 0),
      coeFn_dqKernelL2 ha hab he u 0, coeFn_dqKernelL2 ha hab he v 0] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [sq_norm_eq_integral hsub]
  have hle : ∀ p, (dqKernel a b e u 0 p - dqKernel a b e v 0 p) ^ 2 ≤
      gaussTime (a ^ 2) (b ^ 2) φ 2 v p := by
    intro p
    rw [dqKernel_zero, dqKernel_zero]
    unfold gaussTime
    by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
    · rw [indicator_of_mem hp, indicator_of_mem hp, indicator_of_mem hp]
      have ht := lt_of_lt_of_le ha2 hp.1.1
      have hs : 0 < p.1 / 2 := by positivity
      have h := abs_gkD_sub_le hs he u v p.2
      have h0 : 0 ≤ |gkD (p.1 / 2) e (u - p.2) - gkD (p.1 / 2) e (v - p.2)| := abs_nonneg _
      rw [← sq_abs]
      refine (pow_le_pow_left₀ h0 h 2).trans (le_of_eq ?_)
      rw [hφ]; simp only
      rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      have e1 : ((2 : ℕ) : ℝ) * (δ ^ 2 / (4 * (p.1 / 2))) = δ ^ 2 / p.1 := by
        field_simp; ring
      have e2 : ((2 : ℕ) : ℝ) * (-‖v - p.2‖ ^ 2 / (8 * (p.1 / 2))) = -‖v - p.2‖ ^ 2 / (2 * p.1) := by
        field_simp; ring
      rw [e1, e2]
      ring
    · simp [indicator_of_notMem hp]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun p => sq_nonneg _) hHi
    (Eventually.of_forall hle)).trans ?_
  rw [hHe]
  have hpt : ∀ t ∈ Icc (a ^ 2) (b ^ 2), φ t * (Real.pi * (2 * t)) ≤
      392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 * (t ^ 2)⁻¹ := by
    intro t ht
    have ht0 := lt_of_lt_of_le ha2 ht.1
    have ht1 : t ≤ 1 := ht.2.trans hb2
    have hB : gkB (t / 2) ≤ 14 / (Real.pi * t ^ 2) := by
      unfold gkB
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg t, mul_pos hpi (pow_pos ht0 2)]
    have hB0 : 0 ≤ gkB (t / 2) := by unfold gkB; positivity
    have hE : Real.exp (δ ^ 2 / t) ≤ Real.exp (δ ^ 2 / a ^ 2) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) ha2 ht.1)
    rw [hφ]; simp only
    calc δ ^ 2 * gkB (t / 2) ^ 2 * Real.exp (δ ^ 2 / t) * (Real.pi * (2 * t))
        ≤ δ ^ 2 * (14 / (Real.pi * t ^ 2)) ^ 2 * Real.exp (δ ^ 2 / a ^ 2) *
            (Real.pi * (2 * t)) := by gcongr
      _ = 392 / (Real.pi * t) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 * (t ^ 2)⁻¹ := by
          field_simp; ring
      _ ≤ 392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 * (t ^ 2)⁻¹ := by
          gcongr; exact ht.1
  have hint2 : IntegrableOn (fun t => 392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) *
      δ ^ 2 * (t ^ 2)⁻¹) (Icc (a ^ 2) (b ^ 2)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ fun t ht =>
      pow_ne_zero 2 (lt_of_lt_of_le ha2 ht.1).ne')
  have hint1 : IntegrableOn (fun t => φ t * (Real.pi * (2 * t))) (Icc (a ^ 2) (b ^ 2)) :=
    (hφc.mul (continuousOn_const.mul (continuousOn_const.mul continuousOn_id))).integrableOn_compact
      isCompact_Icc
  refine (setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt).trans ?_
  rw [integral_const_mul]
  have hI := integral_inv_sq_le ha2 hab2
  have hc0 : 0 ≤ 392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 := by positivity
  calc 392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 *
        ∫ t in Icc (a ^ 2) (b ^ 2), (t ^ 2)⁻¹
      ≤ 392 / (Real.pi * a ^ 2) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 * (a ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hI hc0
    _ = 392 / (Real.pi * a ^ 4) * Real.exp (δ ^ 2 / a ^ 2) * δ ^ 2 := by field_simp

end WhiteNoise
end LQGMetric
