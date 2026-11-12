/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseC1L2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1Kernel

/-!
# The difference-quotient kernels of `φ_{a,b}` in `L²` (task P2-DDDFFIELD)

For `0 < a`, `‖e‖ ≤ 1`, `x ∈ ℂ`, `h ∈ ℝ`, the kernel
`q_{x,h}(t, y) = 1_{[a²,b²]}(t) ∫₀¹ ∂_e p_{t/2}(x − y + r h e) dr` (`dqKernel`) is in
`L²(ℝ × ℂ)` (`dqKernelL2`), and

* `phiKernelL2_add_smul_sub`: `k_{x + h e} − k_x = h q_{x,h}` (DDDF's kernel
  `k_x(t, y) = 1_{[a²,b²]}(t) p_{t/2}(x − y)`, `tightness.tex` l. 289);
* `dqKernel_zero`: `q_{x,0}(t, y) = 1_{[a²,b²]}(t) ∂_e p_{t/2}(x − y)` (the kernel of `∂_e φ`);
* `norm_dqKernelL2_sub_le`: `‖q_{x,h} − q_{x',h'}‖ ≤ (‖x − x'‖ + |h − h'|) ‖M_ρ‖` on
  `‖x‖ + |h|, ‖x'‖ + |h'| ≤ ρ`, with an explicit Gaussian dominating function `M_ρ ∈ L²`.

Own elementary proof (dominated bounds from `WhiteNoiseC1Kernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace WhiteNoise

/-- The difference-quotient kernel `q_{x,h}(t, y) = 1_{[a²,b²]}(t) dq t e x h y`. -/
def dqKernel (a b : ℝ) (e x : ℂ) (h : ℝ) : ℝ × ℂ → ℝ :=
  (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator fun p => dq p.1 e x h p.2

lemma dqKernel_zero (a b : ℝ) (e x : ℂ) :
    dqKernel a b e x 0 = (Icc (a ^ 2) (b ^ 2) ×ˢ univ).indicator
      fun p => gkD (p.1 / 2) e (x - p.2) := by
  unfold dqKernel; simp_rw [dq_zero]

lemma measurable_dqKernel (a b : ℝ) (e x : ℂ) (h : ℝ) : Measurable (dqKernel a b e x h) := by
  refine Measurable.indicator ?_ (measurableSet_Icc.prod MeasurableSet.univ)
  have hF : Measurable fun q : (ℝ × ℂ) × ℝ => gkD (q.1.1 / 2) e (x - q.1.2 + (q.2 * h) • e) := by
    unfold gkD gk; fun_prop
  have := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  convert this.measurable using 1
  funext p
  simp only [dq, intervalIntegral.integral_of_le zero_le_one]

/-- The constant of the dominating function. -/
def domC (a b ρ : ℝ) : ℝ := 2 * (5 + 2 * b ^ 2) / (Real.pi * a ^ 4) * Real.exp (ρ ^ 2 / (2 * a ^ 2))

lemma domC_nonneg (a b ρ : ℝ) : 0 ≤ domC a b ρ := by
  unfold domC; have := Real.pi_pos; positivity

/-- The dominating function `M_ρ(t, y) = 1_{[a²,b²]}(t) C e^{−|y|²/(4b²)}`. -/
def domFun (a b ρ : ℝ) (p : ℝ × ℂ) : ℝ :=
  (Icc (a ^ 2) (b ^ 2)).indicator (fun _ => domC a b ρ) p.1 * Real.exp (-‖p.2‖ ^ 2 / (4 * b ^ 2))

lemma domFun_nonneg (a b ρ : ℝ) (p : ℝ × ℂ) : 0 ≤ domFun a b ρ p := by
  unfold domFun
  refine mul_nonneg (indicator_nonneg (fun _ _ => domC_nonneg a b ρ) _) (Real.exp_pos _).le

lemma memLp_domFun {a b : ℝ} (hb : 0 < b) (ρ : ℝ) :
    MemLp (domFun a b ρ) 2 (volume : Measure (ℝ × ℂ)) := by
  have hm : Measurable (domFun a b ρ) := by
    unfold domFun
    exact ((measurable_const.indicator measurableSet_Icc).comp measurable_fst).mul
      (by fun_prop)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h1 : Integrable ((Icc (a ^ 2) (b ^ 2)).indicator fun _ : ℝ => domC a b ρ ^ 2) :=
    (integrableOn_const (by simp [Real.volume_Icc]) ).integrable_indicator measurableSet_Icc
  have h2 : Integrable fun y : ℂ => Real.exp (-(2 * b ^ 2)⁻¹ * ‖y‖ ^ 2) :=
    integrable_rexp_neg_mul_sq_norm_complex (by positivity)
  have := h1.mul_prod h2
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [domFun]
  rw [mul_pow, ← Real.exp_nat_mul]
  by_cases hp : p.1 ∈ Icc (a ^ 2) (b ^ 2)
  · simp only [indicator_of_mem hp]
    congr 2
    field_simp
    ring
  · simp [indicator_of_notMem hp]

/-- On `[a², b²]`, the time-dependent constant of `abs_dq_le` is below `M_ρ`. -/
lemma dq_const_le {a b : ℝ} (ha : 0 < a) {t : ℝ} (ht : t ∈ Icc (a ^ 2) (b ^ 2)) (ρ : ℝ) (y : ℂ) :
    gkB (t / 2) * Real.exp (ρ ^ 2 / (4 * (t / 2))) * Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))) ≤
      domC a b ρ * Real.exp (-‖y‖ ^ 2 / (4 * b ^ 2)) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le ha2 ht.1
  have hb2 : 0 < b ^ 2 := lt_of_lt_of_le ht0 ht.2
  have hpi := Real.pi_pos
  have h1 : gkB (t / 2) ≤ 2 * (5 + 2 * b ^ 2) / (Real.pi * a ^ 4) := by
    unfold gkB
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : a ^ 4 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ ha2.le ht.1 2
      calc a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ ≤ t ^ 2 := this
    calc (5 + 4 * (t / 2)) * (Real.pi * a ^ 4) ≤ (5 + 2 * b ^ 2) * (Real.pi * t ^ 2) :=
          mul_le_mul (by linarith [ht.2]) (mul_le_mul_of_nonneg_left this hpi.le)
            (by positivity) (by positivity)
      _ = 2 * (5 + 2 * b ^ 2) * (2 * Real.pi * (t / 2) ^ 2) := by ring
  have h2 : Real.exp (ρ ^ 2 / (4 * (t / 2))) ≤ Real.exp (ρ ^ 2 / (2 * a ^ 2)) := by
    rw [Real.exp_le_exp, show 4 * (t / 2) = 2 * t by ring]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [ht.1])
  have h3 : Real.exp (-‖y‖ ^ 2 / (8 * (t / 2))) ≤ Real.exp (-‖y‖ ^ 2 / (4 * b ^ 2)) := by
    rw [Real.exp_le_exp, show 8 * (t / 2) = 4 * t by ring, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [ht.2])
  unfold domC
  have := Real.exp_pos (ρ ^ 2 / (4 * (t / 2)))
  have := Real.exp_pos (-‖y‖ ^ 2 / (8 * (t / 2)))
  calc gkB (t / 2) * Real.exp (ρ ^ 2 / (4 * (t / 2))) * Real.exp (-‖y‖ ^ 2 / (8 * (t / 2)))
      ≤ (2 * (5 + 2 * b ^ 2) / (Real.pi * a ^ 4)) * Real.exp (ρ ^ 2 / (2 * a ^ 2)) *
          Real.exp (-‖y‖ ^ 2 / (4 * b ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma abs_dqKernel_le {a b : ℝ} (ha : 0 < a) {e : ℂ} (he : ‖e‖ ≤ 1) {ρ : ℝ} {x : ℂ} {h : ℝ}
    (hxh : ‖x‖ + |h| ≤ ρ) (p : ℝ × ℂ) : |dqKernel a b e x h p| ≤ domFun a b ρ p := by
  unfold dqKernel domFun
  by_cases hp : p.1 ∈ Icc (a ^ 2) (b ^ 2)
  · have hp' : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := ⟨hp, trivial⟩
    rw [indicator_of_mem hp', indicator_of_mem hp]
    exact (abs_dq_le (lt_of_lt_of_le (by positivity) hp.1) he hxh p.2).trans
      (dq_const_le ha hp ρ p.2)
  · have hp' : p ∉ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := fun h => hp h.1
    simp [indicator_of_notMem hp', indicator_of_notMem hp]

lemma abs_dqKernel_sub_le {a b : ℝ} (ha : 0 < a) {e : ℂ} (he : ‖e‖ ≤ 1) {ρ : ℝ} {x x' : ℂ}
    {h h' : ℝ} (hxh : ‖x‖ + |h| ≤ ρ) (hxh' : ‖x'‖ + |h'| ≤ ρ) (p : ℝ × ℂ) :
    |dqKernel a b e x h p - dqKernel a b e x' h' p| ≤
      (‖x - x'‖ + |h - h'|) * domFun a b ρ p := by
  unfold dqKernel domFun
  by_cases hp : p.1 ∈ Icc (a ^ 2) (b ^ 2)
  · have hp' : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := ⟨hp, trivial⟩
    rw [indicator_of_mem hp', indicator_of_mem hp', indicator_of_mem hp]
    refine (abs_dq_sub_le (lt_of_lt_of_le (by positivity) hp.1) he hxh hxh' p.2).trans ?_
    rw [mul_comm (‖x - x'‖ + |h - h'|)]
    exact mul_le_mul_of_nonneg_right (dq_const_le ha hp ρ p.2) (by positivity)
  · have hp' : p ∉ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := fun h => hp h.1
    simp [indicator_of_notMem hp', indicator_of_notMem hp]

lemma memLp_dqKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1) (x : ℂ)
    (h : ℝ) : MemLp (dqKernel a b e x h) 2 (volume : Measure (ℝ × ℂ)) :=
  (memLp_domFun (lt_of_lt_of_le ha hab) (‖x‖ + |h|)).of_le
    (measurable_dqKernel a b e x h).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (domFun_nonneg _ _ _ p)]
      exact abs_dqKernel_le ha he le_rfl p)

/-- The `L²` class of `q_{x,h}` (junk `0` outside `0 < a ≤ b`, `‖e‖ ≤ 1`). -/
def dqKernelL2 (a b : ℝ) (e x : ℂ) (h : ℝ) : WNSpace :=
  if hc : 0 < a ∧ a ≤ b ∧ ‖e‖ ≤ 1 then (memLp_dqKernel hc.1 hc.2.1 hc.2.2 x h).toLp _ else 0

lemma coeFn_dqKernelL2 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1) (x : ℂ)
    (h : ℝ) : (dqKernelL2 a b e x h : ℝ × ℂ → ℝ) =ᵐ[volume] dqKernel a b e x h := by
  rw [dqKernelL2, dite_eq_left_of_eq_true (eq_true ⟨ha, hab, he⟩)]
  exact MemLp.coeFn_toLp _

/-- The `L²` class of the dominating function. -/
def domL2 (a b ρ : ℝ) : WNSpace :=
  if hb : 0 < b then (memLp_domFun (a := a) hb ρ).toLp _ else 0

/-- **`L²` Lipschitz bound** for the difference-quotient kernels. -/
theorem norm_dqKernelL2_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1)
    {ρ : ℝ} {x x' : ℂ} {h h' : ℝ} (hxh : ‖x‖ + |h| ≤ ρ) (hxh' : ‖x'‖ + |h'| ≤ ρ) :
    ‖dqKernelL2 a b e x h - dqKernelL2 a b e x' h'‖ ≤
      (‖x - x'‖ + |h - h'|) * ‖domL2 a b ρ‖ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hd : (domL2 a b ρ : ℝ × ℂ → ℝ) =ᵐ[volume] domFun a b ρ := by
    rw [domL2, dite_eq_left_of_eq_true (eq_true hb)]; exact MemLp.coeFn_toLp _
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (dqKernelL2 a b e x h) (dqKernelL2 a b e x' h'),
    coeFn_dqKernelL2 ha hab he x h, coeFn_dqKernelL2 ha hab he x' h', hd] with p h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, Real.norm_eq_abs, Real.norm_of_nonneg (domFun_nonneg _ _ _ p)]
  exact abs_dqKernel_sub_le ha he hxh hxh' p

/-- **Kernel identity** `k_{x + h e} − k_x = h q_{x,h}` in `L²`. -/
theorem phiKernelL2_add_smul_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {e : ℂ} (he : ‖e‖ ≤ 1)
    (x : ℂ) (h : ℝ) :
    phiKernelL2 a b (x + h • e) - phiKernelL2 a b x = h • dqKernelL2 a b e x h := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (phiKernelL2 a b (x + h • e)) (phiKernelL2 a b x),
    Lp.coeFn_smul h (dqKernelL2 a b e x h), coeFn_phiKernelL2 a b ha (x + h • e),
    coeFn_phiKernelL2 a b ha x, coeFn_dqKernelL2 ha hab he x h] with p h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.smul_apply, h3, h4, h5, smul_eq_mul]
  unfold phiKernel dqKernel
  by_cases hp : p ∈ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ)
  · have hs : p.1 / 2 ≠ 0 := by
      have := lt_of_lt_of_le (by positivity : (0 : ℝ) < a ^ 2) hp.1.1
      positivity
    rw [indicator_of_mem hp, indicator_of_mem hp, indicator_of_mem hp, heatKernel_eq_gk,
      heatKernel_eq_gk, show x + h • e - p.2 = (x - p.2) + h • e by abel,
      gk_add_smul_sub hs e (x - p.2) h]
    rfl
  · rw [indicator_of_notMem hp, indicator_of_notMem hp, indicator_of_notMem hp]; ring

end WhiteNoise
end LQGMetric
