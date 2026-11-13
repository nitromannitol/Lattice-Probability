/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.Semigroup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.Generator

/-!
# The semigroup argument for Theorem 1.2

Task SEMIGROUP (`PLAN.md` §5 M2, steps 2 and 4).

* `pushR f a`: the pushforward density of `a` along an injective holomorphic `f` on `H`, with
  the change of variables `integral_pushR_mul`.
* Flow splitting of `hTrev`, `Xfun`, `Efun` at an intermediate time.
* `norm_Phi_add_sub_le`: `‖Φ_{t+s} − Φ_t‖ ≤ C s^{3/2}` uniformly for `t ∈ [0, T]`.
* `Phi_eq_Phi_zero`: `Φ_T = Φ_0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Semigroup

open CharFun Generator

/-! ## Pushforward densities -/

section Push

variable {f : ℂ → ℂ}

/-- The pushforward density of `a` along `f` (restricted to `H`):
`(pushR f a)(f z) = a z / ‖f' z‖²` on `f '' H`, and `0` off `f '' H`. -/
def pushR (f : ℂ → ℂ) (a : ℂ → ℝ) : ℂ → ℝ :=
  Function.extend (H.domRestrict f) (fun z : H => a z / ‖deriv f z‖ ^ 2) 0

theorem pushR_apply (hinj : InjOn f H) (a : ℂ → ℝ) {z : ℂ} (hz : z ∈ H) :
    pushR f a (f z) = a z / ‖deriv f z‖ ^ 2 :=
  (injOn_iff_injective.1 hinj).extend_apply _ _ ⟨z, hz⟩

theorem pushR_of_not_mem (a : ℂ → ℝ) {w : ℂ} (hw : w ∉ f '' H) : pushR f a w = 0 := by
  unfold pushR
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨z, hz⟩; exact hw ⟨z, z.2, hz⟩

theorem abs_pushR (hinj : InjOn f H) (a : ℂ → ℝ) (w : ℂ) :
    |pushR f a w| = pushR f (fun z => |a z|) w := by
  by_cases hw : w ∈ f '' H
  · obtain ⟨z, hz, rfl⟩ := hw
    rw [pushR_apply hinj _ hz, pushR_apply hinj _ hz, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖deriv f z‖ ^ 2)]
  · rw [pushR_of_not_mem _ hw, pushR_of_not_mem _ hw, abs_zero]

theorem hasFDerivWithinAt_H (hf : DifferentiableOn ℂ f H) :
    ∀ z ∈ H, HasFDerivWithinAt f (fderiv ℝ f z) H z := fun z hz =>
  (hf.differentiableAt (isOpen_H.mem_nhds hz)).real_of_complex.hasFDerivAt.hasFDerivWithinAt

theorem measurable_pushR (hf : DifferentiableOn ℂ f H) (hinj : InjOn f H) {a : ℂ → ℝ}
    (ha : Measurable a) : Measurable (pushR f a) :=
  (measurableEmbedding_of_fderivWithin isOpen_H.measurableSet (hasFDerivWithinAt_H hf)
    hinj).measurable_extend
    ((ha.comp measurable_subtype_coe).div
      (((measurable_deriv f).norm.pow_const 2).comp measurable_subtype_coe))
    measurable_const

/-- Change of variables along `f`. -/
theorem integral_pushR_mul (hf : DifferentiableOn ℂ f H) (hinj : InjOn f H)
    (hd : ∀ z ∈ H, deriv f z ≠ 0) {a : ℂ → ℝ} (ha : ∀ z ∉ H, a z = 0) (φ : ℂ → ℝ) :
    ∫ w, pushR f a w * φ w = ∫ z, a z * φ (f z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := f '' H) (fun w hw => by
      rw [pushR_of_not_mem a hw, zero_mul]),
    integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) isOpen_H.measurableSet
      (hasFDerivWithinAt_H hf) hinj]
  conv_rhs => rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := H) (fun z hz => by
      rw [ha z hz, zero_mul])]
  refine setIntegral_congr_fun isOpen_H.measurableSet fun z hz => ?_
  have hdz : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.2 (hd z hz)
  rw [smul_eq_mul, abs_det_fderiv_eq_normSq (hf.differentiableAt (isOpen_H.mem_nhds hz)),
    pushR_apply hinj a hz]
  field_simp

theorem N1_pushR (hf : DifferentiableOn ℂ f H) (hinj : InjOn f H)
    (hd : ∀ z ∈ H, deriv f z ≠ 0) {a : ℂ → ℝ} (ha : ∀ z ∉ H, a z = 0) :
    N1 (pushR f a) = N1 a := by
  unfold N1
  have := integral_pushR_mul hf hinj hd (a := fun z => |a z|) (fun z hz => by simp [ha z hz])
    (fun _ => 1)
  simp only [mul_one] at this
  rw [← this]
  exact integral_congr_ae (ae_of_all _ fun w => abs_pushR hinj a w)

end Push

/-! ## Pushing a test function along the reverse flow -/

section RevPush

theorem norm_deriv_revMap_ge {W : ℝ → ℝ} (hW : Continuous W) {t δ : ℝ} (ht : 0 ≤ t)
    (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ z.im) :
    Real.exp (-(2 / δ ^ 2 * t)) ≤ ‖deriv (revMap W t) z‖ := by
  have hzH : z ∈ H := show 0 < z.im from hδ.trans_le hz
  rw [deriv_revMap W hW ht hzH, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hb : ‖∫ s in (0 : ℝ)..t, 2 / revMap W s z ^ 2‖ ≤ 2 / δ ^ 2 * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
    rw [uIoc_of_le ht] at hr
    have h1 : δ ≤ ‖revMap W r z‖ :=
      hz.trans ((im_le_im_revMap W hW z hzH hr.1.le).trans (Complex.im_le_norm _))
    rw [norm_div, norm_pow, Complex.norm_two]
    gcongr
  rw [sub_zero, abs_of_nonneg ht] at hb
  have h2 := Complex.abs_re_le_norm (∫ s in (0 : ℝ)..t, 2 / revMap W s z ^ 2)
  have h3 := neg_abs_le (∫ s in (0 : ℝ)..t, 2 / revMap W s z ^ 2).re
  linarith

/-- The push of a density with support in `{δ < Im} ∩ closedBall 0 R` along `f_t` is a
generator test function. -/
theorem isGenTest_pushR {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {a : ℂ → ℝ}
    {K : Set ℂ} {M δ R : ℝ} (hd : Dens a K M δ) (hKR : K ⊆ Metric.closedBall 0 R) :
    IsGenTest (pushR (revMap W t) a) δ (R + |W t| + 2 * t / δ)
      (M * Real.exp (2 * (2 / δ ^ 2 * t))) := by
  have hdiff := differentiableOn_revMap W hW ht
  have hinj := injOn_revMap W hW ht
  have hM : 0 ≤ M := (abs_nonneg _).trans (hd.bound 0)
  refine ⟨hd.delta, measurable_pushR hdiff hinj hd.meas, fun w => ?_, fun w hw => ?_⟩
  · by_cases hw : w ∈ revMap W t '' H
    · obtain ⟨z, hz, rfl⟩ := hw
      rw [pushR_apply hinj a hz]
      by_cases hzK : z ∈ K
      · have hzd : δ ≤ z.im := (hd.sub hzK).le
        have h1 := norm_deriv_revMap_ge hW ht hd.delta hzd
        have h2 : Real.exp (-(2 / δ ^ 2 * t)) ^ 2 ≤ ‖deriv (revMap W t) z‖ ^ 2 :=
          pow_le_pow_left₀ (Real.exp_pos _).le h1 2
        have h3 : Real.exp (-(2 / δ ^ 2 * t)) ^ 2 * Real.exp (2 * (2 / δ ^ 2 * t)) = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
        have hpos : 0 < Real.exp (-(2 / δ ^ 2 * t)) ^ 2 := by positivity
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖deriv (revMap W t) z‖ ^ 2),
          div_le_iff₀ (hpos.trans_le h2)]
        calc |a z| ≤ M := hd.bound z
          _ = M * Real.exp (2 * (2 / δ ^ 2 * t)) * Real.exp (-(2 / δ ^ 2 * t)) ^ 2 := by
            rw [mul_assoc, mul_comm (Real.exp _), h3, mul_one]
          _ ≤ _ := by gcongr
      · rw [hd.supp z hzK, zero_div, abs_zero]; positivity
    · rw [pushR_of_not_mem a hw, abs_zero]; positivity
  · by_cases hw' : w ∈ revMap W t '' H
    · obtain ⟨z, hz, rfl⟩ := hw'
      rw [pushR_apply hinj a hz] at hw
      have hzK : z ∈ K := by
        by_contra hzK; rw [hd.supp z hzK, zero_div] at hw; exact hw rfl
      have hzd : δ < z.im := hd.sub hzK
      refine ⟨hzd.le.trans (im_le_im_revMap W hW z hz ht), ?_⟩
      have h1 := norm_revMap_sub_le W hW z hz ht
      have h2 : ‖z‖ ≤ R := by simpa using hKR hzK
      have h3 : 2 * t / z.im ≤ 2 * t / δ :=
        div_le_div_of_nonneg_left (by positivity) hd.delta hzd.le
      have h4 : ‖z - (W t : ℂ)‖ ≤ ‖z‖ + |W t| := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
      calc ‖revMap W t z‖ ≤ ‖revMap W t z - (z - (W t : ℂ))‖ + ‖z - (W t : ℂ)‖ :=
            norm_le_norm_sub_add _ _
        _ ≤ _ := by linarith
    · exact absurd (pushR_of_not_mem a hw') hw

end RevPush

/-! ## Splitting the flow at an intermediate time -/

section Split

variable {W W1 W2 : ℝ → ℝ} {t s : ℝ}

theorem mem_H_revMap {V : ℝ → ℝ} (hV : Continuous V) {τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ}
    (hz : z ∈ H) : revMap V τ z ∈ H :=
  show 0 < (revMap V τ z).im from lt_of_lt_of_le hz (im_le_im_revMap V hV z hz hτ)

theorem pushR_mem_of_ne_zero {f : ℂ → ℂ} {a : ℂ → ℝ} {w : ℂ} (hw : pushR f a w ≠ 0) :
    w ∈ f '' H := by
  by_contra h; exact hw (pushR_of_not_mem a h)

theorem intervalIntegrable_inv_sq {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H)
    {τ : ℝ} (hτ : 0 ≤ τ) : IntervalIntegrable (fun r => 2 / revMap V r z ^ 2) volume 0 τ := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hτ]
  exact continuousOn_const.div ((continuousOn_revMap_time V hV hz hτ).pow 2)
    fun r hr => pow_ne_zero 2 (revMap_ne_zero_of_im hV hz hr.1)

theorem revMap_split (hW : Continuous W) (ht : 0 ≤ t)
    (h1 : EqOn W W1 (Icc 0 t)) (h2 : ∀ r ∈ Icc (0 : ℝ) s, W (t + r) - W t = W2 r)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) s) {z : ℂ} (hz : z ∈ H) :
    revMap W (t + r) z = revMap W2 r (revMap W1 t z) := by
  rw [ReverseFlow.revMap_add W hW z hz ht hr.1, ReverseFlow.revMap_congr_drive z h1]
  exact ReverseFlow.revMap_congr_drive _ fun u hu => h2 u ⟨hu.1, hu.2.trans hr.2⟩

theorem hTrev_split (κ : ℝ) (hW : Continuous W) (hW1 : Continuous W1) (hW2 : Continuous W2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (h1 : EqOn W W1 (Icc 0 t))
    (h2 : ∀ r ∈ Icc (0 : ℝ) s, W (t + r) - W t = W2 r) {z : ℂ} (hz : z ∈ H) :
    hTrev κ W (t + s) z = hTrev κ W2 s (revMap W1 t z) +
      Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W1 t) z‖ := by
  have hw := mem_H_revMap hW1 ht hz
  have hts : 0 ≤ t + s := by linarith
  have hsub : uIcc t (t + s) ⊆ uIcc 0 (t + s) := by
    rw [uIcc_of_le (by linarith), uIcc_of_le hts]; exact Icc_subset_Icc ht le_rfl
  have hA : ∫ r in (0 : ℝ)..t, 2 / revMap W r z ^ 2 = ∫ r in (0 : ℝ)..t, 2 / revMap W1 r z ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht] at hr
    show 2 / revMap W r z ^ 2 = 2 / revMap W1 r z ^ 2
    rw [ReverseFlow.revMap_congr_drive z (Set.EqOn.mono (Icc_subset_Icc le_rfl hr.2) h1)]
  have hB : ∫ r in t..(t + s), 2 / revMap W r z ^ 2 =
      ∫ r in (0 : ℝ)..s, 2 / revMap W2 r (revMap W1 t z) ^ 2 := by
    have e := intervalIntegral.integral_comp_add_left (a := 0) (b := s)
      (fun r => 2 / revMap W r z ^ 2) t
    simp only [add_zero] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    show 2 / revMap W (t + r) z ^ 2 = 2 / revMap W2 r (revMap W1 t z) ^ 2
    rw [revMap_split hW ht h1 h2 hr hz]
  have hsplit : ∫ r in (0 : ℝ)..(t + s), 2 / revMap W r z ^ 2 =
      (∫ r in (0 : ℝ)..t, 2 / revMap W1 r z ^ 2) +
        ∫ r in (0 : ℝ)..s, 2 / revMap W2 r (revMap W1 t z) ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (intervalIntegrable_inv_sq hW hz ht) ((intervalIntegrable_inv_sq hW hz hts).mono_set hsub),
      hA, hB]
  unfold hTrev
  rw [log_norm_deriv_revMap W hW hts hz, log_norm_deriv_revMap W2 hW2 hs hw,
    log_norm_deriv_revMap W1 hW1 ht hz, hsplit, revMap_split hW ht h1 h2 ⟨hs, le_rfl⟩ hz,
    Complex.add_re]
  ring

/-- The part of `(𝔥_t, ρ)` coming from `Q log|f_t'|`. -/
def Gpart (κ : ℝ) (W1 : ℝ → ℝ) (t : ℝ) (ρ : ℂ → ℝ) : ℝ :=
  ∫ z, ρ z * (Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W1 t) z‖)

theorem continuousOn_logDeriv (κ : ℝ) (hW1 : Continuous W1) (ht : 0 ≤ t) :
    ContinuousOn (fun z => Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W1 t) z‖) H := by
  refine ((continuousOn_hTrev κ hW1 ht).sub ((continuousOn_h0rev κ).comp
    (differentiableOn_revMap W1 hW1 ht).continuousOn
      fun z hz => mem_H_revMap hW1 ht hz)).congr ?_
  intro z _
  show _ = hTrev κ W1 t z - h0rev κ (revMap W1 t z)
  unfold hTrev
  ring

theorem integrable_tf_mul (ρ : TestFun H) {g : ℂ → ℝ} (hg : ContinuousOn g H) :
    Integrable (fun z => ρ.1 z * g z) :=
  (continuous_mul_of_tsupport (tf_continuous ρ) ρ.2.2.2 hg).integrable_of_hasCompactSupport
    ρ.2.2.1.mul_right

theorem Xfun_split (κ : ℝ) (hW : Continuous W) (hW1 : Continuous W1) (hW2 : Continuous W2)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (h1 : EqOn W W1 (Icc 0 t))
    (h2 : ∀ r ∈ Icc (0 : ℝ) s, W (t + r) - W t = W2 r) (ρ : TestFun H) :
    Xfun κ W (t + s) ρ.1 = Xs κ (pushR (revMap W1 t) ρ.1) W2 s + Gpart κ W1 t ρ.1 := by
  have hdiff := differentiableOn_revMap W1 hW1 ht
  have hinj := injOn_revMap W1 hW1 ht
  have hder : ∀ z ∈ H, deriv (revMap W1 t) z ≠ 0 := fun z hz =>
    deriv_revMap_ne_zero W1 hW1 ht hz
  have hρ0 : ∀ z ∉ H, ρ.1 z = 0 := fun z hz => tf_eq_zero_of_not_mem ρ hz
  have hA : ContinuousOn (fun z => hTrev κ W2 s (revMap W1 t z)) H :=
    (continuousOn_hTrev κ hW2 hs).comp hdiff.continuousOn fun z hz => mem_H_revMap hW1 ht hz
  have e1 : Xfun κ W (t + s) ρ.1 = ∫ z, (ρ.1 z * hTrev κ W2 s (revMap W1 t z) +
      ρ.1 z * (Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W1 t) z‖)) := by
    unfold Xfun
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ H
    · simp only; rw [hTrev_split κ hW hW1 hW2 ht hs h1 h2 hz]; ring
    · simp [hρ0 z hz]
  rw [e1, integral_add (integrable_tf_mul ρ hA) (integrable_tf_mul ρ (continuousOn_logDeriv κ hW1 ht)),
    ← integral_pushR_mul hdiff hinj hder hρ0 (hTrev κ W2 s)]
  unfold Gpart
  congr 1
  unfold Xs
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  by_cases hw : pushR (revMap W1 t) ρ.1 w = 0
  · simp [hw]
  · have hwH : w ∈ H := by
      obtain ⟨z, hz, rfl⟩ := pushR_mem_of_ne_zero hw
      exact mem_H_revMap hW1 ht hz
    simp only [hTrev, h0rev]
    rw [log_norm_deriv_revMap W2 hW2 hs hwH]

theorem Xfun_eq_X0 (κ : ℝ) (hW1 : Continuous W1) (ht : 0 ≤ t) (ρ : TestFun H) :
    Xfun κ W1 t ρ.1 = X0 κ (pushR (revMap W1 t) ρ.1) + Gpart κ W1 t ρ.1 := by
  have hdiff := differentiableOn_revMap W1 hW1 ht
  have hinj := injOn_revMap W1 hW1 ht
  have hder : ∀ z ∈ H, deriv (revMap W1 t) z ≠ 0 := fun z hz =>
    deriv_revMap_ne_zero W1 hW1 ht hz
  have hρ0 : ∀ z ∉ H, ρ.1 z = 0 := fun z hz => tf_eq_zero_of_not_mem ρ hz
  have hA : ContinuousOn (fun z => h0rev κ (revMap W1 t z)) H :=
    (continuousOn_h0rev κ).comp hdiff.continuousOn fun z hz => mem_H_revMap hW1 ht hz
  have e1 : Xfun κ W1 t ρ.1 = ∫ z, (ρ.1 z * h0rev κ (revMap W1 t z) +
      ρ.1 z * (Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W1 t) z‖)) := by
    unfold Xfun hTrev
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    ring
  rw [e1, integral_add (integrable_tf_mul ρ hA) (integrable_tf_mul ρ (continuousOn_logDeriv κ hW1 ht)),
    ← integral_pushR_mul hdiff hinj hder hρ0 (h0rev κ)]
  rfl

theorem double_push {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H) (hinj : InjOn f H)
    (hd : ∀ z ∈ H, deriv f z ≠ 0) {a : ℂ → ℝ} (ha : ∀ z ∉ H, a z = 0) (K : ℂ → ℂ → ℝ) :
    ∫ x, ∫ y, pushR f a x * pushR f a y * K x y = ∫ x, ∫ y, a x * a y * K (f x) (f y) := by
  have e1 : ∀ x, ∫ y, pushR f a x * pushR f a y * K x y =
      pushR f a x * ∫ y, pushR f a y * K x y := fun x => by
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e2 : ∀ x, ∫ y, a x * a y * K (f x) (f y) = a x * ∫ y, a y * K (f x) (f y) := fun x => by
    rw [← integral_const_mul]; congr 1; funext y; ring
  simp_rw [e1, e2]
  rw [integral_pushR_mul hf hinj hd ha (fun x => ∫ y, pushR f a y * K x y)]
  congr 1; funext x; congr 1
  exact integral_pushR_mul hf hinj hd ha (fun y => K (f x) y)

theorem Efun_split (hW : Continuous W) (hW1 : Continuous W1) (ht : 0 ≤ t)
    (h1 : EqOn W W1 (Icc 0 t)) (h2 : ∀ r ∈ Icc (0 : ℝ) s, W (t + r) - W t = W2 r)
    (hs : 0 ≤ s) (ρ : TestFun H) :
    Efun W (t + s) ρ.1 = Es (pushR (revMap W1 t) ρ.1) W2 s := by
  have hρ0 : ∀ z ∉ H, ρ.1 z = 0 := fun z hz => tf_eq_zero_of_not_mem ρ hz
  unfold Es
  rw [double_push (differentiableOn_revMap W1 hW1 ht) (injOn_revMap W1 hW1 ht)
    (fun z hz => deriv_revMap_ne_zero W1 hW1 ht hz) hρ0
    (fun x y => neumannH (revMap W2 s x) (revMap W2 s y))]
  unfold Efun
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => ?_))
  by_cases hx : x ∈ H
  · by_cases hy : y ∈ H
    · simp only
      rw [revMap_split hW ht h1 h2 ⟨hs, le_rfl⟩ hx, revMap_split hW ht h1 h2 ⟨hs, le_rfl⟩ hy]
    · simp [hρ0 y hy]
  · simp [hρ0 x hx]

theorem Efun_eq_E0 (hW1 : Continuous W1) (ht : 0 ≤ t) (ρ : TestFun H) :
    Efun W1 t ρ.1 = E0 (pushR (revMap W1 t) ρ.1) := by
  unfold E0
  rw [double_push (differentiableOn_revMap W1 hW1 ht) (injOn_revMap W1 hW1 ht)
    (fun z hz => deriv_revMap_ne_zero W1 hW1 ht hz) (fun z hz => tf_eq_zero_of_not_mem ρ hz)
    neumannH]
  rfl

end Split

/-! ## The integrand as a function of the driver path -/

section PathFun

/-- The integrand of `Φ_T` as a function of the driver path on `[0, T]`. -/
def Hf (κ T : ℝ) (hT : 0 ≤ T) (ρ : ℂ → ℝ) (f : C(Icc (0 : ℝ) T, ℝ)) : ℂ :=
  cexp (I * (Xfun κ (Wof κ T hT f) T ρ : ℂ) - (Efun (Wof κ T hT f) T ρ : ℂ) / 2)

theorem measurable_Xfun_Wof (κ T : ℝ) (hT : 0 ≤ T) (ρ : TestFun H) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) => Xfun κ (Wof κ T hT f) T ρ.1 := by
  have heq : (fun f : C(Icc (0 : ℝ) T, ℝ) => Xfun κ (Wof κ T hT f) T ρ.1) =
      fun f => ∫ z, ρ.1 z * hTm κ T hT (f, z) := by
    funext f
    unfold Xfun
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ H
    · simp only; rw [hTm_eq κ T hT f hz]
    · simp [tf_eq_zero_of_not_mem ρ hz]
  rw [heq]
  exact (((tf_continuous ρ).measurable.comp measurable_snd).mul
    (measurable_hTm κ T hT)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_Efun_Wof (κ T : ℝ) (hT : 0 ≤ T) (ρ : TestFun H) :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) => Efun (Wof κ T hT f) T ρ.1 := by
  have hρ := (tf_continuous ρ).measurable
  have hF := measurable_Fm κ T hT
  have h3 : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × ℂ) × ℂ =>
      ρ.1 q.1.2 * ρ.1 q.2 * neumannH (Fm κ T hT (q.1.1, q.1.2)) (Fm κ T hT (q.1.1, q.2)) :=
    ((hρ.comp (measurable_snd.comp measurable_fst)).mul (hρ.comp measurable_snd)).mul
      (Generator.measurable_neumannH.comp ((hF.comp measurable_fst).prodMk
        (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
  exact h3.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem measurable_Hf (κ T : ℝ) (hT : 0 ≤ T) (ρ : TestFun H) :
    Measurable (Hf κ T hT ρ.1) :=
  Complex.measurable_exp.comp ((measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_Xfun_Wof κ T hT ρ))).sub
    ((Complex.measurable_ofReal.comp (measurable_Efun_Wof κ T hT ρ)).div_const 2))

theorem norm_cexp_I_sub (x E : ℝ) : ‖cexp (I * (x : ℂ) - (E : ℂ) / 2)‖ = Real.exp (-E / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.sub_re, Complex.mul_re]
  ring

theorem Efun_nonneg_of_gff {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (κ T : ℝ)
    (hT : 0 ≤ T) (ρ : TestFun0 H) (f : C(Icc (0 : ℝ) T, ℝ)) :
    0 ≤ Efun (Wof κ T hT f) T ρ.1.1 := by
  have h := cond_charFun_Y2f κ T hT hX ρ f
  have hle : ‖∫ ω, cexp (I * (pairRaw (Y2f κ T hT f (X ω)) ρ.1.1 : ℂ)) ∂P‖ ≤ 1 := by
    refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω => ?_)).trans
      (by simp)
    simp [Complex.norm_exp, Complex.mul_re]
  rw [h, norm_cexp_I_sub, Real.exp_le_one_iff] at hle
  linarith

theorem norm_Hf_le {κ T : ℝ} {hT : 0 ≤ T} {ρ : ℂ → ℝ} {f : C(Icc (0 : ℝ) T, ℝ)}
    (hE : 0 ≤ Efun (Wof κ T hT f) T ρ) : ‖Hf κ T hT ρ f‖ ≤ 1 := by
  rw [Hf, norm_cexp_I_sub, Real.exp_le_one_iff]
  linarith

end PathFun

/-! ## Concatenation of driver paths -/

section Concat

variable {t s : ℝ}

/-- Concatenation of a path on `[0, t]` with a path on `[0, s]` (the second one re-based at
the endpoint of the first). -/
def catP (ht : 0 ≤ t) (hs : 0 ≤ s) (u : C(Icc (0 : ℝ) t, ℝ)) (v : C(Icc (0 : ℝ) s, ℝ)) :
    C(Icc (0 : ℝ) (t + s), ℝ) :=
  ⟨fun x => u (projIcc 0 t ht x.1) + v (projIcc 0 s hs (x.1 - t)) - v (projIcc 0 s hs 0),
    ((u.continuous.comp (continuous_projIcc.comp continuous_subtype_val)).add
      (v.continuous.comp (continuous_projIcc.comp
        (continuous_subtype_val.sub continuous_const)))).sub continuous_const⟩

theorem measurable_catP (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Measurable fun p : C(Icc (0 : ℝ) t, ℝ) × C(Icc (0 : ℝ) s, ℝ) => catP ht hs p.1 p.2 :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    (((ContinuousMap.measurable_eval _).comp measurable_fst).add
      ((ContinuousMap.measurable_eval _).comp measurable_snd)).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd)

theorem Wof_cat_eqOn (κ : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (u : C(Icc (0 : ℝ) t, ℝ))
    (v : C(Icc (0 : ℝ) s, ℝ)) :
    EqOn (Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v)) (Wof κ t ht u) (Icc 0 t) := by
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) (t + s) := ⟨hr.1, by linarith [hr.2]⟩
  simp only [Wof, catP, ContinuousMap.coe_mk, projIcc_of_mem (add_nonneg ht hs) hr']
  rw [projIcc_of_le_left hs (by linarith [hr.2] : r - t ≤ 0), projIcc_left hs]
  ring

theorem Wof_cat_shift (κ : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (u : C(Icc (0 : ℝ) t, ℝ))
    (v : C(Icc (0 : ℝ) s, ℝ)) (hv0 : v (projIcc 0 s hs 0) = 0) :
    ∀ r ∈ Icc (0 : ℝ) s, Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v) (t + r) -
      Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v) t = Real.sqrt κ * v (projIcc 0 s hs r) := by
  intro r hr
  have h1 : t + r ∈ Icc (0 : ℝ) (t + s) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have h2 : t ∈ Icc (0 : ℝ) (t + s) := ⟨ht, by linarith⟩
  simp only [Wof, catP, ContinuousMap.coe_mk, projIcc_of_mem (add_nonneg ht hs) h1,
    projIcc_of_mem (add_nonneg ht hs) h2]
  rw [projIcc_of_right_le ht (by linarith [hr.1] : t ≤ t + r), projIcc_of_right_le ht le_rfl,
    show t + r - t = r by ring, sub_self, hv0]
  ring

/-- The shifted Brownian motion `B̃_u = B_{t+u} − B_t`. -/
def shiftB {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun u ω => B (t.toNNReal + u) ω - B t.toNNReal ω

theorem continuous_shiftB {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => B t ω)
    (t : ℝ) : ∀ ω, Continuous fun u => shiftB B t u ω := fun ω =>
  ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const

theorem pathC_cat {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => B t ω)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (ω : Ω) :
    pathC (t + s) B hc ω =
      catP ht hs (pathC t B hc ω) (pathC s (shiftB B t) (continuous_shiftB hc t) ω) := by
  ext ⟨x, hx0, hx1⟩
  simp only [pathC, catP, shiftB, ContinuousMap.coe_mk]
  rw [projIcc_left hs]
  rcases le_total x t with hxt | hxt
  · rw [projIcc_of_mem ht ⟨hx0, hxt⟩, projIcc_of_le_left hs (by linarith : x - t ≤ 0)]
    ring
  · rw [projIcc_of_right_le ht hxt, projIcc_of_mem hs ⟨by linarith, by linarith⟩]
    have : x.toNNReal = t.toNNReal + (x - t).toNNReal := by
      rw [← Real.toNNReal_add ht (by linarith)]; ring_nf
    simp only [Real.toNNReal_zero, add_zero]
    rw [this]
    ring

theorem indepFun_pathC_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous fun t => B t ω)
    (t s : ℝ) :
    IndepFun (pathC t B hc) (pathC s (shiftB B t) (continuous_shiftB hc t)) P := by
  have hind := hB.toIsPreBrownianReal.indepFun_shift t.toNNReal
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro A C hA hC
  have k1 : ∃ A', MeasurableSet A' ∧
      (fun ω (r : Set.Iic t.toNNReal) => B r ω) ⁻¹' A' = pathC t B hc ⁻¹' A := by
    let _ : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (r : Set.Iic t.toNNReal) => B r ω) MeasurableSpace.pi
    have hm : Measurable (pathC t B hc) := ContinuousMap.measurable_iff_eval.2 fun x =>
      show Measurable ((fun f : Set.Iic t.toNNReal → ℝ =>
          f ⟨x.1.toNNReal, Real.toNNReal_le_toNNReal x.2.2⟩) ∘
          (fun ω (r : Set.Iic t.toNNReal) => B r ω)) from
        (measurable_pi_apply _).comp (comap_measurable _)
    exact hm hA
  have k2 : ∃ C', MeasurableSet C' ∧
      (fun ω u => B (t.toNNReal + u) ω - B t.toNNReal ω) ⁻¹' C' =
        pathC s (shiftB B t) (continuous_shiftB hc t) ⁻¹' C := by
    let _ : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω u => B (t.toNNReal + u) ω - B t.toNNReal ω)
        MeasurableSpace.pi
    have hm : Measurable (pathC s (shiftB B t) (continuous_shiftB hc t)) :=
      ContinuousMap.measurable_iff_eval.2 fun x =>
        show Measurable ((fun f : ℝ≥0 → ℝ => f x.1.toNNReal) ∘
            (fun ω u => B (t.toNNReal + u) ω - B t.toNNReal ω)) from
          (measurable_pi_apply _).comp (comap_measurable _)
    exact hm hC
  obtain ⟨A', hA', e1⟩ := k1
  obtain ⟨C', hC', e2⟩ := k2
  rw [← e1, ← e2, inter_comm, hind C' A' hC' hA', mul_comm]

end Concat

/-! ## One step of the semigroup -/

section Step

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem Phi_eq_integral_Hf (κ τ : ℝ) (hτ : 0 ≤ τ) {B : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => B t ω) (ρ : ℂ → ℝ) :
    Phi κ τ B P ρ = ∫ ω, Hf κ τ hτ ρ (pathC τ B hc ω) ∂P := by
  unfold Phi Hf
  congr 1
  funext ω
  have h := revMap_drive_eq κ τ hτ B hc ω
  rw [Xfun_congr h, Efun_congr h]

theorem inner_eq (κ : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (ρ : TestFun H)
    {B : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t => B t ω) (u : C(Icc (0 : ℝ) t, ℝ)) :
    ∫ ω', Hf κ (t + s) (add_nonneg ht hs) ρ.1
        (catP ht hs u (pathC s (shiftB B t) (continuous_shiftB hc t) ω')) ∂P =
      cexp (I * (Gpart κ (Wof κ t ht u) t ρ.1 : ℂ)) *
        Psi κ (pushR (revMap (Wof κ t ht u) t) ρ.1) (shiftB B t) P s := by
  rw [Psi, ← integral_const_mul]
  congr 1
  funext ω'
  set v := pathC s (shiftB B t) (continuous_shiftB hc t) ω'
  have hv0 : v (projIcc 0 s hs 0) = 0 := by
    simp [v, pathC, shiftB]
  have hW := continuous_Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v)
  have hW1 := continuous_Wof κ t ht u
  have hW2 := Generator.continuous_drive κ (continuous_shiftB hc t) ω'
  have h1 := Wof_cat_eqOn κ ht hs u v
  have h2 : ∀ r ∈ Icc (0 : ℝ) s, Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v) (t + r) -
      Wof κ (t + s) (add_nonneg ht hs) (catP ht hs u v) t = drive κ (shiftB B t) ω' r := by
    intro r hr
    rw [Wof_cat_shift κ ht hs u v hv0 r hr]
    simp only [v, pathC, ContinuousMap.coe_mk, projIcc_of_mem hs hr, drive]
  unfold Hf
  rw [Xfun_split κ hW hW1 hW2 ht hs h1 h2 ρ, Efun_split hW hW1 ht h1 h2 hs ρ,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem Hf_eq (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (ρ : TestFun H) (u : C(Icc (0 : ℝ) t, ℝ)) :
    Hf κ t ht ρ.1 u = cexp (I * (Gpart κ (Wof κ t ht u) t ρ.1 : ℂ)) *
      cexp (I * (X0 κ (pushR (revMap (Wof κ t ht u) t) ρ.1) : ℂ) -
        (E0 (pushR (revMap (Wof κ t ht u) t) ρ.1) : ℂ) / 2) := by
  unfold Hf
  rw [Xfun_eq_X0 κ (continuous_Wof κ t ht u) ht ρ, Efun_eq_E0 (continuous_Wof κ t ht u) ht ρ,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Step

/-! ## Constants -/

section Const

/-- The part of `C₄` not depending on `R`. -/
def cC4a (κ δ : ℝ) : ℝ :=
  2 / Real.sqrt κ * OnePointExpansion.C₁ δ / δ + 4 / δ ^ 3 + 4 / (Real.sqrt κ * δ ^ 4) +
    Qc (Real.sqrt κ) * OnePointExpansion.C₂ δ

/-- The coefficient of `C₃` in `C₄`. -/
def cC4b (κ δ : ℝ) : ℝ :=
  8 / Real.sqrt κ * (Real.sqrt κ ^ 3 / δ ^ 3) + 8 / Real.sqrt κ * (8 / δ ^ 6)

theorem C₄_eq (κ δ R : ℝ) :
    OnePointExpansion.C₄ κ δ R = cC4a κ δ + cC4b κ δ * OnePointExpansion.C₃ δ R := by
  unfold OnePointExpansion.C₄ cC4a cC4b; ring

theorem max_C₄_le {κ δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    max (OnePointExpansion.C₄ κ δ R) 0 ≤ |cC4a κ δ| + cC4b κ δ * (9 + 8 * (R / δ)) := by
  have hb : 0 ≤ cC4b κ δ := by unfold cC4b; positivity
  have hRd : 0 < R / δ := div_pos hR hδ
  have hlog : Real.log (R / δ) ≤ R / δ := (Real.log_le_sub_one_of_pos hRd).trans (by linarith)
  have hC3 : OnePointExpansion.C₃ δ R ≤ 9 + 8 * (R / δ) := by
    unfold OnePointExpansion.C₃; linarith
  refine max_le ?_ (by positivity)
  rw [C₄_eq]
  have := le_abs_self (cC4a κ δ)
  nlinarith [mul_le_mul_of_nonneg_left hC3 hb]

theorem Kall_split (N δ γ C4 cs : ℝ) :
    Kall N δ γ C4 cs = Kall N δ γ 0 cs + C4 * (N * ((2 / δ + cs) * N + 2 * N / δ) + N) := by
  unfold Kall; ring

/-- Auxiliary constant. -/
def NxC (κ δ N : ℝ) : ℝ := N * ((2 / δ + cX κ δ) * N + 2 * N / δ) + N

/-- Constant term of the affine bound on `Cgen`. -/
def alphaC (κ T δ R0 N : ℝ) : ℝ :=
  CD κ * (Kall N δ (Real.sqrt κ) 0 (cX κ δ) +
    (|cC4a κ δ| + cC4b κ δ * (9 + 8 * ((R0 + 2 * T / δ) / δ))) * NxC κ δ N)

/-- Linear coefficient of the affine bound on `Cgen`. -/
def betaC (κ δ N : ℝ) : ℝ := CD κ * (cC4b κ δ * (8 * Real.sqrt κ / δ) * NxC κ δ N)

/-- The constant of the one-step estimate. -/
def Cst (κ T δ R0 N : ℝ) : ℝ := alphaC κ T δ R0 N + betaC κ δ N * (1 + T)

theorem CD_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ CD κ := by
  have h1 := gaussianAbsMoment_nonneg 1
  have h2 := gaussianAbsMoment_nonneg 2
  have h3 := gaussianAbsMoment_nonneg 3
  have h4 := gaussianAbsMoment_nonneg 4
  have h5 := mul_nonneg (Real.sqrt_nonneg κ) h1
  have h6 := mul_nonneg hκ h2
  unfold CD
  linarith

theorem cX_nonneg {κ δ : ℝ} (hκ : 0 < κ) : 0 ≤ cX κ δ := by
  have := Qc_pos hκ; unfold cX; positivity

theorem betaC_nonneg {κ δ N : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hN : 0 ≤ N) :
    0 ≤ betaC κ δ N := by
  have hcs := cX_nonneg (δ := δ) hκ
  have hCD := CD_nonneg hκ.le
  have hb : 0 ≤ cC4b κ δ := by unfold cC4b; positivity
  have hNx : 0 ≤ NxC κ δ N := by unfold NxC; positivity
  unfold betaC; positivity

theorem Cgen_nonneg {σ : ℂ → ℝ} {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    0 ≤ Cgen σ κ δ R :=
  mul_nonneg (Kall_nonneg (N1_nonneg σ) hδ (Real.sqrt_pos.2 hκ) (le_max_right _ _)
    (cX_nonneg hκ)) (CD_nonneg hκ.le)

theorem Cgen_le_affine {σ : ℂ → ℝ} {κ T δ R0 y : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR0 : 0 < R0)
    (hT : 0 ≤ T) (hy : 0 ≤ y) :
    Cgen σ κ δ (R0 + 2 * T / δ + Real.sqrt κ * y) ≤
      alphaC κ T δ R0 (N1 σ) + betaC κ δ (N1 σ) * y := by
  have hR : 0 < R0 + 2 * T / δ + Real.sqrt κ * y := by positivity
  have hC4 := max_C₄_le (κ := κ) hδ hR
  have hN := N1_nonneg σ
  have hcs := cX_nonneg (δ := δ) hκ
  have hNx : 0 ≤ N1 σ * ((2 / δ + cX κ δ) * N1 σ + 2 * N1 σ / δ) + N1 σ := by positivity
  have hCD := CD_nonneg hκ.le
  unfold Cgen
  rw [Kall_split]
  refine (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC4 hNx))
    hCD).trans (le_of_eq ?_)
  unfold alphaC betaC NxC
  ring

theorem isGenTest_mono {σ : ℂ → ℝ} {δ R M R' : ℝ} (h : IsGenTest σ δ R M) (hR : R ≤ R') :
    IsGenTest σ δ R' M :=
  ⟨h.pos, h.meas, h.bound, fun z hz => ⟨(h.supp z hz).1, (h.supp z hz).2.trans hR⟩⟩

theorem norm_cexp_I_mul (x : ℝ) : ‖cexp (I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

theorem integral_affine_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {t T α β : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hβ : 0 ≤ β) : ∫ ω, (α + β * |B t.toNNReal ω|) ∂P ≤ α + β * (1 + T) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have i1 : Integrable (fun ω => |B t.toNNReal ω|) P := (hB.integrable_eval _).abs
  have i2 : Integrable (fun ω => B t.toNNReal ω ^ 2) P := by
    have := integrable_pow hB t.toNNReal 2
    simpa [sq_abs] using this
  have hle : ∫ ω, |B t.toNNReal ω| ∂P ≤ 1 + T := by
    calc ∫ ω, |B t.toNNReal ω| ∂P ≤ ∫ ω, (1 + B t.toNNReal ω ^ 2) ∂P :=
          integral_mono i1 ((integrable_const 1).add i2) fun ω => by
            have := sq_abs (B t.toNNReal ω)
            nlinarith [sq_nonneg (|B t.toNNReal ω| - 1)]
      _ = 1 + t := by
          rw [integral_add (integrable_const 1) i2, integral_sq hB, Real.coe_toNNReal t ht]
          simp
      _ ≤ 1 + T := by linarith
  have hα : ∫ _ : Ω, α ∂P = α := by simp
  rw [integral_add (integrable_const α) (i1.const_mul β), integral_const_mul, hα]
  nlinarith

end Const

/-! ## The one-step estimate and the conclusion -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_inner (κ : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (ρ : TestFun H)
    [SFinite P] {V : Ω → C(Icc (0 : ℝ) s, ℝ)} (hV : Measurable V) :
    Measurable fun u : C(Icc (0 : ℝ) t, ℝ) =>
      ∫ ω', Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs u (V ω')) ∂P := by
  have h1 : Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × Ω => catP ht hs q.1 (V q.2) :=
    (measurable_catP ht hs).comp (measurable_fst.prodMk (hV.comp measurable_snd))
  have h2 : Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × Ω =>
      Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs q.1 (V q.2)) :=
    (measurable_Hf κ (t + s) (add_nonneg ht hs) ρ).comp h1
  exact (h2.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

theorem norm_inner_le (κ : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (ρ : TestFun H)
    [IsProbabilityMeasure P]
    (hpos : ∀ τ (hτ : 0 ≤ τ) (f : C(Icc (0 : ℝ) τ, ℝ)), 0 ≤ Efun (Wof κ τ hτ f) τ ρ.1)
    (V : Ω → C(Icc (0 : ℝ) s, ℝ)) (u : C(Icc (0 : ℝ) t, ℝ)) :
    ‖∫ ω', Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs u (V ω')) ∂P‖ ≤ 1 :=
  (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun _ => norm_Hf_le (hpos _ _ _))).trans
    (by simp)

/-- The pointwise (in the pre-`t` path `u`) estimate. -/
theorem step_pointwise {κ : ℝ} (hκ : 0 < κ) {T : ℝ} (hT : 0 ≤ T) (ρ : TestFun H)
    {M δ R0 : ℝ} (hd : Dens ρ.1 (tsupport ρ.1) M δ) (hR0 : tsupport ρ.1 ⊆ Metric.closedBall 0 R0)
    (hR0p : 0 < R0)
    (hpos : ∀ τ (hτ : 0 ≤ τ) (f : C(Icc (0 : ℝ) τ, ℝ)), 0 ≤ Efun (Wof κ τ hτ f) τ ρ.1)
    {B' : ℝ≥0 → Ω → ℝ} (hBs : IsBrownianReal B' P) (hBsm : ∀ t, Measurable (B' t))
    (hBsc : ∀ ω, Continuous fun t => B' t ω)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hs1 : s ≤ 1) (htT : t ≤ T)
    (u : C(Icc (0 : ℝ) t, ℝ)) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : |Wof κ t ht u t| = Real.sqrt κ * y) :
    ‖cexp (I * (Gpart κ (Wof κ t ht u) t ρ.1 : ℂ)) *
        Psi κ (pushR (revMap (Wof κ t ht u) t) ρ.1) B' P s - Hf κ t ht ρ.1 u‖ ≤
      (alphaC κ T δ R0 (N1 ρ.1) + betaC κ δ (N1 ρ.1) * y) * s ^ ((3 : ℝ) / 2) := by
  have hW1 : Continuous (Wof κ t ht u) := continuous_Wof κ t ht u
  have hgen := isGenTest_mono (isGenTest_pushR hW1 ht hd hR0)
    (R' := R0 + 2 * T / δ + Real.sqrt κ * y) (by
      rw [hy]
      have : 2 * t / δ ≤ 2 * T / δ := by gcongr; exact hd.delta.le
      linarith)
  have hN : N1 (pushR (revMap (Wof κ t ht u) t) ρ.1) = N1 ρ.1 :=
    N1_pushR (differentiableOn_revMap _ hW1 ht) (injOn_revMap _ hW1 ht)
      (fun z hz => deriv_revMap_ne_zero _ hW1 ht hz) (fun z hz => tf_eq_zero_of_not_mem ρ hz)
  have hE0 : 0 ≤ E0 (pushR (revMap (Wof κ t ht u) t) ρ.1) := by
    rw [← Efun_eq_E0 hW1 ht ρ]; exact hpos t ht _
  have hPsi := norm_Psi_sub_le hgen hκ hBs hBsm hBsc hs hs1
  have hCg := Cgen_le_affine (σ := pushR (revMap (Wof κ t ht u) t) ρ.1)
    hκ hd.delta hR0p hT hy0
  rw [hN] at hCg
  have hCg0 := Cgen_nonneg (σ := pushR (revMap (Wof κ t ht u) t) ρ.1)
    (R := R0 + 2 * T / δ + Real.sqrt κ * y) hκ hd.delta
  have hs32 : 0 ≤ s ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hs _
  rw [Hf_eq κ ht ρ, ← mul_sub, norm_mul, norm_cexp_I_mul, one_mul]
  refine hPsi.trans ?_
  have hexp : Real.exp (-E0 (pushR (revMap (Wof κ t ht u) t) ρ.1) / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  calc _ ≤ 1 * Cgen (pushR (revMap (Wof κ t ht u) t) ρ.1) κ δ
        (R0 + 2 * T / δ + Real.sqrt κ * y) * s ^ ((3 : ℝ) / 2) := by gcongr
    _ ≤ _ := by rw [one_mul]; gcongr

theorem abs_Wof_pathC {Ω : Type*} (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) {B : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) :
    |Wof κ t ht (pathC t B hc ω) t| = Real.sqrt κ * |B t.toNNReal ω| := by
  simp only [Wof, pathC, ContinuousMap.coe_mk, projIcc_right ht]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]

/-- **One step of the semigroup**: `‖Φ_{t+s} − Φ_t‖ ≤ C s^{3/2}` for `0 ≤ s ≤ 1`,
`t + s ≤ T`, with `C` independent of `t` and `s`. -/
theorem norm_Phi_add_sub_le {κ : ℝ} (hκ : 0 < κ) {T : ℝ} (hT : 0 ≤ T) (ρ : TestFun H)
    {M δ R0 : ℝ} (hd : Dens ρ.1 (tsupport ρ.1) M δ) (hR0 : tsupport ρ.1 ⊆ Metric.closedBall 0 R0)
    (hR0p : 0 < R0)
    (hpos : ∀ τ (hτ : 0 ≤ τ) (f : C(Icc (0 : ℝ) τ, ℝ)), 0 ≤ Efun (Wof κ τ hτ f) τ ρ.1)
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hts : t + s ≤ T) :
    ‖Phi κ (t + s) B P ρ.1 - Phi κ t B P ρ.1‖ ≤ Cst κ T δ R0 (N1 ρ.1) * s ^ ((3 : ℝ) / 2) := by
  have htT : t ≤ T := by linarith
  have hBs : IsBrownianReal (shiftB B t) P := hB.shift t.toNNReal
  have hBsm : ∀ u, Measurable (shiftB B t u) := fun u => (hBm _).sub (hBm _)
  have hUm : Measurable (pathC t B hc) := measurable_pathC t hBm hc
  have hVm : Measurable (pathC s (shiftB B t) (continuous_shiftB hc t)) :=
    measurable_pathC s hBsm (continuous_shiftB hc t)
  have hind := indepFun_pathC_shift hB hc t s
  have hGm : Measurable fun p : C(Icc (0 : ℝ) t, ℝ) × C(Icc (0 : ℝ) s, ℝ) =>
      Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs p.1 p.2) :=
    (measurable_Hf κ (t + s) (add_nonneg ht hs) ρ).comp (measurable_catP ht hs)
  have hGb : ∀ p : C(Icc (0 : ℝ) t, ℝ) × C(Icc (0 : ℝ) s, ℝ),
      ‖Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs p.1 p.2)‖ ≤ 1 := fun p =>
    norm_Hf_le (hpos _ _ _)
  have e1 : Phi κ (t + s) B P ρ.1 = ∫ ω, (∫ ω', Hf κ (t + s) (add_nonneg ht hs) ρ.1
      (catP ht hs (pathC t B hc ω) (pathC s (shiftB B t) (continuous_shiftB hc t) ω')) ∂P) ∂P := by
    rw [Phi_eq_integral_Hf κ (t + s) (add_nonneg ht hs) hc,
      ← integral_indep (G := fun p : C(Icc (0 : ℝ) t, ℝ) × C(Icc (0 : ℝ) s, ℝ) =>
        Hf κ (t + s) (add_nonneg ht hs) ρ.1 (catP ht hs p.1 p.2)) hUm hVm hind hGm hGb]
    congr 1
    funext ω
    rw [pathC_cat hc ht hs ω]
  have e2 : Phi κ t B P ρ.1 = ∫ ω, Hf κ t ht ρ.1 (pathC t B hc ω) ∂P :=
    Phi_eq_integral_Hf κ t ht hc ρ.1
  have hint1 : Integrable (fun ω => ∫ ω', Hf κ (t + s) (add_nonneg ht hs) ρ.1
      (catP ht hs (pathC t B hc ω) (pathC s (shiftB B t) (continuous_shiftB hc t) ω')) ∂P) P :=
    Integrable.of_bound
    ((measurable_inner κ ht hs ρ hVm (P := P)).comp hUm).aestronglyMeasurable 1
    (ae_of_all _ fun ω => norm_inner_le κ ht hs ρ hpos _ (pathC t B hc ω))
  have hint2 : Integrable (fun ω => Hf κ t ht ρ.1 (pathC t B hc ω)) P :=
    Integrable.of_bound ((measurable_Hf κ t ht ρ).comp hUm).aestronglyMeasurable 1
      (ae_of_all _ fun ω => norm_Hf_le (hpos _ _ _))
  rw [e1, e2, ← integral_sub hint1 hint2]
  have hbi : Integrable (fun ω => (alphaC κ T δ R0 (N1 ρ.1) + betaC κ δ (N1 ρ.1) *
      |B t.toNNReal ω|) * s ^ ((3 : ℝ) / 2)) P :=
    ((integrable_const _).add
      ((hB.toIsPreBrownianReal.integrable_eval _).abs.const_mul _)).mul_const _
  refine (norm_integral_le_of_norm_le hbi (ae_of_all _ fun ω => ?_)).trans ?_
  · rw [inner_eq κ ht hs ρ hc]
    exact step_pointwise hκ hT ρ hd hR0 hR0p hpos hBs hBsm (continuous_shiftB hc t) ht hs hs1
      htT _ (abs_nonneg _) (abs_Wof_pathC κ ht hc ω)
  rw [integral_mul_const]
  unfold Cst
  exact mul_le_mul_of_nonneg_right (integral_affine_abs_le hB.toIsPreBrownianReal ht htT
    (betaC_nonneg hκ hd.delta (N1_nonneg _))) (Real.rpow_nonneg hs _)

/-- A function with `‖Φ(t+s) − Φ(t)‖ ≤ C s^{3/2}` on `[0, T]` is constant there. -/
theorem eq_of_holder {Φ : ℝ → ℂ} {T C : ℝ} (hT : 0 < T)
    (h : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → s ≤ 1 → t + s ≤ T →
      ‖Φ (t + s) - Φ t‖ ≤ C * s ^ ((3 : ℝ) / 2)) :
    Φ T = Φ 0 := by
  have key : ∀ n : ℕ, T ≤ n → ‖Φ T - Φ 0‖ ≤ C * T * Real.sqrt (T / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := hT.trans_le hn
    have hh0 : 0 ≤ T / n := by positivity
    have hh1 : T / n ≤ 1 := by rw [div_le_one hn0]; exact hn
    have hnh : (n : ℝ) * (T / n) = T := by field_simp
    have htel : Φ T - Φ 0 =
        ∑ k ∈ Finset.range n, (Φ ((k : ℝ) * (T / n) + T / n) - Φ ((k : ℝ) * (T / n))) := by
      have := Finset.sum_range_sub (fun k : ℕ => Φ ((k : ℝ) * (T / n))) n
      simp only [Nat.cast_succ, add_mul, one_mul] at this
      rw [this, hnh]
      simp
    have h32 : (T / n) ^ ((3 : ℝ) / 2) = T / n * Real.sqrt (T / n) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hh0 (by norm_num)]
      norm_num
    rw [htel]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range n, ‖Φ ((k : ℝ) * (T / n) + T / n) - Φ ((k : ℝ) * (T / n))‖
        ≤ ∑ _k ∈ Finset.range n, C * (T / n) ^ ((3 : ℝ) / 2) := by
          refine Finset.sum_le_sum fun k hk => h _ _ (by positivity) hh0 hh1 ?_
          have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hk
          calc (k : ℝ) * (T / n) + T / n = ((k : ℝ) + 1) * (T / n) := by ring
            _ ≤ n * (T / n) := by gcongr
            _ = T := hnh
      _ = C * T * Real.sqrt (T / n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, h32]
          calc (n : ℝ) * (C * (T / n * Real.sqrt (T / n)))
              = C * ((n : ℝ) * (T / n)) * Real.sqrt (T / n) := by ring
            _ = _ := by rw [hnh]
  have hlim : Tendsto (fun n : ℕ => C * T * Real.sqrt (T / n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat T
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul (C * T)
    simpa using h2
  have hle : ‖Φ T - Φ 0‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop ⌈T⌉₊).mono fun n hn =>
      key n ((Nat.le_ceil T).trans (by exact_mod_cast hn)))
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- **The semigroup identity** `Φ_T = Φ_0`, given the nonnegativity of the energies (which
holds whenever a free-boundary GFF exists, `Efun_nonneg_of_gff`). -/
theorem Phi_const {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) (ρ : TestFun H)
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hpos : ∀ τ (hτ : 0 ≤ τ) (f : C(Icc (0 : ℝ) τ, ℝ)), 0 ≤ Efun (Wof κ τ hτ f) τ ρ.1) :
    Phi κ T B P ρ.1 = Phi κ 0 B P ρ.1 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  obtain ⟨r, hr⟩ := ρ.2.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hR0 : tsupport ρ.1 ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hB' : IsBrownianReal B' P :=
    ⟨hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm,
      ae_of_all _ hB'c⟩
  have hPhi : ∀ τ, Phi κ τ B P ρ.1 = Phi κ τ B' P ρ.1 := by
    intro τ
    unfold Phi
    refine integral_congr_ae ?_
    filter_upwards [hB'eq] with ω h
    have : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, h]
    rw [this]
  rw [hPhi, hPhi]
  exact eq_of_holder (Φ := fun τ => Phi κ τ B' P ρ.1) hT fun t s ht hs hs1 hts =>
    norm_Phi_add_sub_le hκ hT.le ρ hd hR0 (lt_max_of_lt_right one_pos) hpos hB' hB'm hB'c
      ht hs hs1 hts

end Main

end Semigroup
end QuantumZipper
