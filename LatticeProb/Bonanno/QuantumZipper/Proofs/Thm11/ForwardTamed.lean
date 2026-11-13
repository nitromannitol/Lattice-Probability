/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.ForwardTamed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ForwardFlow

/-!
# Tamed forward flows, adaptedness, real points and bounded images (THM11 FD-4, FD-5)

**FD-4.** For `c > 0` the `c`-tamed centered forward flow is the global solution of
`Z̃_t = a − W_t + ∫₀ᵗ 2/proj_c(Z̃_s) ds`, and `Ã_t = ∫₀ᵗ Im(−2/proj_c(Z̃_s)²) ds`.
It coincides with `(f_t(a), Im logDerivFwd)` while `Im ≥ c`, depends continuously on the
start point, the time and the driver (sup-norm), and hence is jointly measurable in
`(a, ω)` for the SLE driver, measurable with respect to any σ-algebra making `B_r`, `r ≤ t`,
measurable (adaptedness).

**FD-5.** Forward solutions from real points stay real and keep the sign of `x − W 0`;
comparison `Re f_t(a) < f_t(x)` (and the symmetric one on the left); boundedness of images.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper

open FwdHolo

variable {W : ℝ → ℝ}

/-! ## 0. Elementary facts on the tamed fields -/

lemma proj_sub_ofReal_tamed (c : ℝ) (x : ℂ) (r : ℝ) : proj c (x - r) = proj c x - r := by
  simp only [proj, Complex.sub_im, Complex.ofReal_im, sub_zero]; ring

lemma proj_im_ge_tamed (c : ℝ) (x : ℂ) : c ≤ (proj c x).im := by
  rw [proj_im]; exact le_max_left _ _

lemma norm_proj_ge_tamed (c : ℝ) (x : ℂ) : c ≤ ‖proj c x‖ :=
  (proj_im_ge_tamed c x).trans (Complex.im_le_norm _)

lemma proj_ne_zero_tamed {c : ℝ} (hc : 0 < c) (x : ℂ) : proj c x ≠ 0 := by
  intro h; have := proj_im_ge_tamed c x; rw [h, Complex.zero_im] at this; linarith

lemma continuous_proj_tamed (c : ℝ) : Continuous (proj c) := (proj_lipschitz c).continuous

lemma tf_eq_tamed (W : ℝ → ℝ) (c t : ℝ) (x : ℂ) : tf W c t x = 2 / proj c (x - W t) := by
  rw [proj_sub_ofReal_tamed]; rfl

lemma norm_two_div_sub_le_tamed {c : ℝ} (hc : 0 < c) {A B : ℂ} (hA : c ≤ ‖A‖) (hB : c ≤ ‖B‖) :
    ‖2 / A - 2 / B‖ ≤ 2 * ‖A - B‖ / c ^ 2 := by
  have hA0 : A ≠ 0 := norm_pos_iff.mp (hc.trans_le hA)
  have hB0 : B ≠ 0 := norm_pos_iff.mp (hc.trans_le hB)
  have e : 2 / A - 2 / B = 2 * (B - A) / (A * B) := by field_simp
  rw [e, norm_div, norm_mul, norm_mul, norm_sub_rev B A]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have : c ^ 2 ≤ ‖A‖ * ‖B‖ := by rw [sq]; exact mul_le_mul hA hB hc.le (hc.le.trans hA)
  have hn := norm_nonneg (A - B)
  nlinarith

lemma dist_tf_le_tamed {c : ℝ} (hc : 0 < c) (W W' : ℝ → ℝ) (t : ℝ) (x : ℂ) {ε : ℝ}
    (h : |W t - W' t| ≤ ε) : dist (tf W' c t x) (tf W c t x) ≤ 2 * ε / c ^ 2 := by
  rw [dist_eq_norm]
  show ‖(2 : ℂ) / (proj c x - W' t) - 2 / (proj c x - W t)‖ ≤ _
  refine (norm_two_div_sub_le_tamed hc (norm_sub_ofReal_ge' _ (proj_im_ge_tamed c x))
    (norm_sub_ofReal_ge' _ (proj_im_ge_tamed c x))).trans ?_
  gcongr
  rw [sub_sub_sub_cancel_left, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- The `Z`-field of the tamed centered flow. -/
def tamedZField (c : ℝ) (x : ℂ) : ℂ := 2 / proj c x

/-- The `A`-field of the tamed flow: `Im(−2/proj_c(x)²)`. -/
def tamedAField (c : ℝ) (x : ℂ) : ℝ := (-2 / proj c x ^ 2).im

lemma continuous_tamedZField {c : ℝ} (hc : 0 < c) : Continuous (tamedZField c) :=
  continuous_const.div (continuous_proj_tamed c) (proj_ne_zero_tamed hc)

lemma continuous_tamedAField {c : ℝ} (hc : 0 < c) : Continuous (tamedAField c) :=
  Complex.continuous_im.comp (continuous_const.div ((continuous_proj_tamed c).pow 2)
    (fun x => pow_ne_zero 2 (proj_ne_zero_tamed hc x)))

lemma norm_tamedZField_le {c : ℝ} (hc : 0 < c) (x : ℂ) : ‖tamedZField c x‖ ≤ 2 / c := by
  unfold tamedZField
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  exact norm_proj_ge_tamed c x

lemma abs_tamedAField_le {c : ℝ} (hc : 0 < c) (x : ℂ) : |tamedAField c x| ≤ 2 / c ^ 2 := by
  unfold tamedAField
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_div, norm_neg, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  exact norm_proj_ge_tamed c x

lemma abs_tamedAField_sub_le {c : ℝ} (hc : 0 < c) (x y : ℂ) :
    |tamedAField c x - tamedAField c y| ≤ 8 / c ^ 3 * ‖x - y‖ := by
  set p := proj c x
  set q := proj c y
  have hp := norm_proj_ge_tamed c x
  have hq := norm_proj_ge_tamed c y
  have hp0 : p ≠ 0 := proj_ne_zero_tamed hc x
  have hq0 : q ≠ 0 := proj_ne_zero_tamed hc y
  have hpq : ‖p - q‖ ≤ 2 * ‖x - y‖ := by
    have := (proj_lipschitz c).dist_le_mul x y
    simpa [dist_eq_norm] using this
  have e : (-2 / p ^ 2) - (-2 / q ^ 2) = -(2 / p - 2 / q) * (1 / p + 1 / q) := by
    field_simp; ring
  have h1 : ‖2 / p - 2 / q‖ ≤ 2 * ‖p - q‖ / c ^ 2 := norm_two_div_sub_le_tamed hc hp hq
  have h2 : ‖1 / p + 1 / q‖ ≤ 2 / c := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_one]
    have : 1 / ‖p‖ ≤ 1 / c := by gcongr
    have : 1 / ‖q‖ ≤ 1 / c := by gcongr
    calc _ ≤ 1 / c + 1 / c := by gcongr
      _ = 2 / c := by ring
  unfold tamedAField
  rw [← Complex.sub_im]
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [e, norm_mul, norm_neg]
  calc _ ≤ (2 * ‖p - q‖ / c ^ 2) * (2 / c) := by gcongr
    _ ≤ (2 * (2 * ‖x - y‖) / c ^ 2) * (2 / c) := by gcongr
    _ = 8 / c ^ 3 * ‖x - y‖ := by field_simp; ring

/-! ## 1. Stability of tamed (un-centered) solutions -/

/-- **Stability of tamed solutions** with respect to the start point and the driver. -/
theorem tamedUnc_stability {W' : ℝ → ℝ} {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {V V' : ℝ → ℂ} {a a' : ℂ} {ε : ℝ}
    (hV0 : V 0 = a) (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (tf W c t (V t)) (Icc 0 T) t)
    (hV0' : V' 0 = a')
    (hV' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V' (tf W' c t (V' t)) (Icc 0 T) t)
    (hε : ∀ r ∈ Icc (0 : ℝ) T, |W r - W' r| ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, dist (V t) (V' t) ≤ (dist a a' + ε) * Real.exp (4 * T / c ^ 2) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 ⟨le_rfl, hT⟩)
  have hK : ((Real.toNNReal (2 / c ^ 2) * 2 : ℝ≥0) : ℝ) = 4 / c ^ 2 := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; push_cast; ring
  have hderivIci : ∀ {f f' : ℝ → ℂ},
      (∀ r ∈ Icc (0:ℝ) T, HasDerivWithinAt f (f' r) (Icc 0 T) r) →
      ∀ r ∈ Ico (0:ℝ) T, HasDerivWithinAt f (f' r) (Ici r) r := fun h r hr =>
    (h r (Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left hr.1))
  have hVc : ContinuousOn V (Icc 0 T) := fun r hr => (hV r hr).continuousWithinAt
  have hV'c : ContinuousOn V' (Icc 0 T) := fun r hr => (hV' r hr).continuousWithinAt
  have hg := dist_le_of_approx_trajectories_ODE (v := tf W c) (K := Real.toNNReal (2 / c ^ 2) * 2)
    (εf := 0) (εg := 2 * ε / c ^ 2) (δ := dist a a')
    (fun r => tf_lipschitz hc W r) hVc (hderivIci hV) (fun r _ => by rw [dist_self])
    hV'c (hderivIci hV')
    (fun r hr => dist_tf_le_tamed hc W W' r _ (hε r (Ico_subset_Icc_self hr)))
    (by rw [hV0, hV0'])
  intro t ht
  have h1 := hg t ht
  rw [gronwallBound_of_K_ne_0 (by rw [hK]; positivity), hK] at h1
  simp only [sub_zero, zero_add] at h1
  have hq : 2 * ε / c ^ 2 / (4 / c ^ 2) = ε / 2 := by field_simp; ring
  rw [hq] at h1
  have hE : Real.exp (4 / c ^ 2 * t) ≤ Real.exp (4 * T / c ^ 2) :=
    Real.exp_le_exp.2 (by rw [div_mul_eq_mul_div]; gcongr; exact ht.2)
  have hp := Real.exp_pos (4 / c ^ 2 * t)
  have hd := dist_nonneg (x := a) (y := a')
  refine h1.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hE hd, mul_le_mul_of_nonneg_left hE hε0]

/-! ## 2. The tamed flow -/

open Classical in
/-- The un-centered `c`-tamed flow `V_t = Z̃_t + W_t`, `V' = tf W c t V`, `V_0 = a`
(junk value `0` unless `W` is continuous and `c > 0`). -/
def tamedUnc (W : ℝ → ℝ) (c : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  if h : Continuous W ∧ 0 < c then
    Classical.choose (exists_tf_sol h.1 h.2 (le_max_right t 0) a) t else 0

/-- The centered `c`-tamed flow `Z̃_t(a)`. -/
def tamedZ (W : ℝ → ℝ) (c : ℝ) (a : ℂ) (t : ℝ) : ℂ := tamedUnc W c a t - W t

/-- The tamed argument process `Ã_t(a) = ∫₀ᵗ Im(−2/proj_c(Z̃_s)²) ds`. -/
def tamedA (W : ℝ → ℝ) (c : ℝ) (a : ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, tamedAField c (tamedZ W c a s)

theorem tamedUnc_eq_of_sol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {V : ℝ → ℂ} {a : ℂ} (hV0 : V 0 = a)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (tf W c t (V t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, tamedUnc W c a t = V t := by
  intro t ht
  rw [tamedUnc, dif_pos ⟨hW, hc⟩]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_tf_sol hW hc (le_max_right t 0) a)
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have h := tamedUnc_stability (W' := W) hc ht.1 hv0
    (fun s hs => (hvd s (hsub hs)).mono hsub) hV0
    (fun s hs => (hV s (hsubT hs)).mono hsubT) (ε := 0) (fun r _ => by simp) t ⟨ht.1, le_rfl⟩
  rw [dist_self, add_zero, zero_mul] at h
  exact dist_le_zero.mp h

theorem tamedUnc_zero (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) :
    tamedUnc W c a 0 = a := by
  rw [tamedUnc, dif_pos ⟨hW, hc⟩]
  exact (Classical.choose_spec (exists_tf_sol hW hc (le_max_right 0 0) a)).1

theorem tamedUnc_hasDerivWithinAt (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    (hT : 0 ≤ T) (a : ℂ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (tamedUnc W c a) (tf W c t (tamedUnc W c a t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_tf_sol hW hc hT a
  have heq := tamedUnc_eq_of_sol hW hc hT hv0 hvd
  intro t ht
  rw [heq t ht]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_tamedZ (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    (a : ℂ) : ContinuousOn (tamedZ W c a) (Icc 0 T) :=
  have h : ContinuousOn (tamedUnc W c a) (Icc 0 T) := fun t ht =>
    (tamedUnc_hasDerivWithinAt hW hc hT a t ht).continuousWithinAt
  h.sub (Complex.continuous_ofReal.comp hW).continuousOn

lemma tf_tamedUnc (W : ℝ → ℝ) (c : ℝ) (a : ℂ) (t : ℝ) :
    tf W c t (tamedUnc W c a t) = tamedZField c (tamedZ W c a t) := tf_eq_tamed W c t _

/-- **FD-4, integral equation.** `Z̃_t = a − W_t + ∫₀ᵗ 2/proj_c(Z̃_s) ds` for `t ≥ 0`. -/
theorem tamedZ_eq (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    tamedZ W c a t = a - W t + ∫ s in (0 : ℝ)..t, 2 / proj c (tamedZ W c a s) := by
  have hcont : ContinuousOn (tamedUnc W c a) (Icc 0 t) := fun s hs =>
    (tamedUnc_hasDerivWithinAt hW hc ht a s hs).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (tamedUnc W c a) (tamedZField c (tamedZ W c a s)) s := fun s hs => by
    rw [← tf_tamedUnc]
    exact (tamedUnc_hasDerivWithinAt hW hc ht a s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => tamedZField c (tamedZ W c a s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (continuous_tamedZField hc).comp_continuousOn (continuousOn_tamedZ hW hc ht a)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [tamedUnc_zero hW hc] at key
  show tamedUnc W c a t - W t = _
  have : (∫ s in (0 : ℝ)..t, 2 / proj c (tamedZ W c a s)) =
      ∫ s in (0 : ℝ)..t, tamedZField c (tamedZ W c a s) := rfl
  rw [this, key]; ring

theorem tamedA_eq (W : ℝ → ℝ) (c : ℝ) (a : ℂ) (t : ℝ) :
    tamedA W c a t = ∫ s in (0 : ℝ)..t, (-2 / proj c (tamedZ W c a s) ^ 2).im := rfl

/-! ## 3. Agreement with the forward flow while `Im ≥ c` -/

/-- A forward solution staying in `{Im ≥ c}` is the tamed flow. -/
theorem tamedZ_eq_of_isForwardSol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    (hT : 0 ≤ T) {a : ℂ} {u : ℝ → ℂ} (hu : IsForwardSol W a T u)
    (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (u t).im) :
    ∀ t ∈ Icc (0 : ℝ) T, tamedZ W c a t = u t := by
  have hV0 : u 0 + (W 0 : ℂ) = a := by rw [sol_zero hu hT]; ring
  have hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => u s + (W s : ℂ))
      (tf W c t (u t + (W t : ℂ))) (Icc 0 T) t := by
    intro t ht
    rw [tf_eq_tamed, add_sub_cancel_right, proj_of_le (him t ht)]
    exact hasDerivWithinAt_shift hu ht
  intro t ht
  have := tamedUnc_eq_of_sol hW hc hT hV0 hV t ht
  simp only [tamedZ, this, add_sub_cancel_right]

/-- The tamed flow, while in `{Im ≥ c}`, is a forward solution. -/
theorem isForwardSol_tamedZ (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {a : ℂ} (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (tamedZ W c a t).im) :
    IsForwardSol W a T (tamedZ W c a) :=
  isForwardSol_of_tf hW hc (tamedUnc_zero hW hc a) (tamedUnc_hasDerivWithinAt hW hc hT a)
    (fun t ht => by simpa [tamedZ] using him t ht)

/-- **FD-4, agreement.** While `Im Z̃ ≥ c` on `[0,T]`, `a` is alive and `f_t(a) = Z̃_t(a)`. -/
theorem fwdMap_eq_tamedZ (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {a : ℂ} (ha : 0 < a.im) (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (tamedZ W c a t).im) :
    (∃ u, IsForwardSol W a T u) ∧ ∀ t ∈ Icc (0 : ℝ) T, fwdMap W t a = tamedZ W c a t :=
  ⟨⟨_, isForwardSol_tamedZ hW hc hT him⟩,
    fun _ ht => fwdMap_eq hW ha (isForwardSol_tamedZ hW hc hT him) ht⟩

/-- **FD-4, agreement (converse form).** If `a` is alive on `[0,T]` and `Im f_t(a) ≥ c` there,
then `f_t(a) = Z̃_t(a)` on `[0,T]`. -/
theorem tamedZ_eq_fwdMap (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {a : ℂ} (ha : 0 < a.im) (hsol : ∃ u, IsForwardSol W a T u)
    (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (fwdMap W t a).im) :
    ∀ t ∈ Icc (0 : ℝ) T, tamedZ W c a t = fwdMap W t a := by
  obtain ⟨u, hu⟩ := hsol
  have hfu : ∀ t ∈ Icc (0 : ℝ) T, fwdMap W t a = u t := fun t ht => fwdMap_eq hW ha hu ht
  intro t ht
  rw [hfu t ht]
  exact tamedZ_eq_of_isForwardSol hW hc hT hu (fun s hs => hfu s hs ▸ him s hs) t ht

/-- **FD-4, argument process.** While `Im Z̃ ≥ c` on `[0,T]`, `Im logDerivFwd = Ã`. -/
theorem im_logDerivFwd_eq_tamedA (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    (hT : 0 ≤ T) {a : ℂ} (ha : 0 < a.im)
    (him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (tamedZ W c a t).im) :
    ∀ t ∈ Icc (0 : ℝ) T, (logDerivFwd W t a).im = tamedA W c a t := by
  obtain ⟨-, hf⟩ := fwdMap_eq_tamedZ hW hc hT ha him
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hne : ∀ s ∈ Icc (0 : ℝ) t, tamedZ W c a s ≠ 0 := fun s hs h => by
    have := him s (hsub hs); rw [h, Complex.zero_im] at this; linarith
  have hcont : ContinuousOn (fun s => -2 / tamedZ W c a s ^ 2) (Icc 0 t) :=
    continuousOn_const.div ((continuousOn_tamedZ hW hc ht.1 a).pow 2)
      (fun s hs => pow_ne_zero 2 (hne s hs))
  have hint : IntervalIntegrable (fun s => -2 / tamedZ W c a s ^ 2) volume 0 t := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht.1]; exact hcont
  have h1 : logDerivFwd W t a = ∫ s in (0 : ℝ)..t, -2 / tamedZ W c a s ^ 2 := by
    rw [logDerivFwd, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hf s (hsub hs), neg_div]
  have h2 : tamedA W c a t = ∫ s in (0 : ℝ)..t, Complex.imCLM (-2 / tamedZ W c a s ^ 2) := by
    rw [tamedA]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [tamedAField, proj_of_le (him s (hsub hs)), Complex.imCLM_apply]
  rw [h1, h2, Complex.imCLM.intervalIntegral_comp_comm hint, Complex.imCLM_apply]

/-! ## 4. Continuous dependence -/

/-- **FD-4, stability.** Dependence on start point and driver in sup norm. -/
theorem dist_tamedZ_le {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {c : ℝ}
    (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (a a' : ℂ) {ε : ℝ}
    (hε : ∀ r ∈ Icc (0 : ℝ) T, |W r - W' r| ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, dist (tamedZ W c a t) (tamedZ W' c a' t) ≤
      (dist a a' + ε) * Real.exp (4 * T / c ^ 2) + ε := by
  intro t ht
  have h := tamedUnc_stability hc hT (tamedUnc_zero hW hc a)
    (tamedUnc_hasDerivWithinAt hW hc hT a) (tamedUnc_zero hW' hc a')
    (tamedUnc_hasDerivWithinAt hW' hc hT a') hε t ht
  rw [dist_eq_norm] at h ⊢
  have e : tamedZ W c a t - tamedZ W' c a' t =
      (tamedUnc W c a t - tamedUnc W' c a' t) - ((W t : ℂ) - W' t) := by
    simp only [tamedZ]; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add h ?_)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hε t ht

theorem tamedZ_congr_drive {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (a : ℂ) (h : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r) :
    tamedZ W c a t = tamedZ W' c a t := by
  have := dist_tamedZ_le hW hW' hc ht a a (ε := 0) (fun r hr => by simp [h r hr]) t ⟨ht, le_rfl⟩
  rw [dist_self, zero_add, zero_mul, zero_add] at this
  exact dist_le_zero.mp this

/-- Time regularity: `|Z̃_t − Z̃_s| ≤ |W_t − W_s| + (2/c)|t − s|`. -/
theorem dist_tamedZ_time_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (tamedZ W c a t) (tamedZ W c a s) ≤ |W t - W s| + 2 / c * |t - s| := by
  have hint : ∀ {r : ℝ}, 0 ≤ r →
      IntervalIntegrable (fun s => tamedZField c (tamedZ W c a s)) volume 0 r := fun {r} hr => by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    exact (continuous_tamedZField hc).comp_continuousOn (continuousOn_tamedZ hW hc hr a)
  have et := tamedZ_eq hW hc a ht
  have es := tamedZ_eq hW hc a hs
  change tamedZ W c a t = a - W t + ∫ s in (0:ℝ)..t, tamedZField c (tamedZ W c a s) at et
  change tamedZ W c a s = a - W s + ∫ s in (0:ℝ)..s, tamedZField c (tamedZ W c a s) at es
  have e : tamedZ W c a t - tamedZ W c a s =
      -((W t : ℂ) - W s) + ∫ r in s..t, tamedZField c (tamedZ W c a r) := by
    rw [← intervalIntegral.integral_interval_sub_left (hint ht) (hint hs), et, es]; ring
  rw [dist_eq_norm, e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  · exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun r _ => norm_tamedZField_le hc _)

lemma tamed_continuousWithinAt_of_dist_le {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y] {F : X → Y} {S : Set X} {x0 : X} {φ : X → ℝ}
    (hφ : ContinuousWithinAt φ S x0) (h0 : φ x0 = 0)
    (hle : ∀ᶠ x in 𝓝[S] x0, dist (F x) (F x0) ≤ φ x) : ContinuousWithinAt F S x0 := by
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hle ?_
  have := hφ.tendsto; rwa [h0] at this

/-- `|Ã(a,W,t) − Ã(a',W',t)|` bound. -/
theorem abs_tamedA_sub_le {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {c : ℝ}
    (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) (a a' : ℂ) {ε : ℝ}
    (hε : ∀ r ∈ Icc (0 : ℝ) T, |W r - W' r| ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, |tamedA W c a t - tamedA W' c a' t| ≤
      8 / c ^ 3 * ((dist a a' + ε) * Real.exp (4 * T / c ^ 2) + ε) * T := by
  intro t ht
  have hi : ∀ {V : ℝ → ℝ}, Continuous V → ∀ b : ℂ,
      IntervalIntegrable (fun s => tamedAField c (tamedZ V c b s)) volume 0 t := fun hV b => by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (continuous_tamedAField hc).comp_continuousOn (continuousOn_tamedZ hV hc ht.1 b)
  rw [tamedA, tamedA, ← intervalIntegral.integral_sub (hi hW a) (hi hW' a')]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := 8 / c ^ 3 * ((dist a a' + ε) * Real.exp (4 * T / c ^ 2) + ε))
    (f := fun s => tamedAField c (tamedZ W c a s) - tamedAField c (tamedZ W' c a' s))
    (fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      rw [Real.norm_eq_abs]
      refine (abs_tamedAField_sub_le hc _ _).trans ?_
      gcongr
      rw [← dist_eq_norm]
      exact dist_tamedZ_le hW hW' hc hT a a' hε s ⟨hs.1.le, hs.2.trans ht.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at this
  refine this.trans ?_
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 ⟨le_rfl, hT⟩)
  gcongr
  exact ht.2

theorem abs_tamedA_time_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |tamedA W c a t - tamedA W c a s| ≤ 2 / c ^ 2 * |t - s| := by
  have hint : ∀ {r : ℝ}, 0 ≤ r →
      IntervalIntegrable (fun s => tamedAField c (tamedZ W c a s)) volume 0 r := fun {r} hr => by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    exact (continuous_tamedAField hc).comp_continuousOn (continuousOn_tamedZ hW hc hr a)
  rw [tamedA, tamedA, intervalIntegral.integral_interval_sub_left (hint ht) (hint hs),
    ← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => by rw [Real.norm_eq_abs]; exact abs_tamedAField_le hc _)

/-! ## 5. Measurability and adaptedness for the SLE driver -/

/-- Continuity of `(a, g) ↦ (Z̃_t, Ã_t)` for drivers `g ∈ C([0,t])`. -/
theorem continuous_tamed_path {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun p : ℂ × C(Icc (0:ℝ) t, ℝ) => tamedZ (extIccPath ht p.2) c p.1 t) ∧
    Continuous (fun p : ℂ × C(Icc (0:ℝ) t, ℝ) => tamedA (extIccPath ht p.2) c p.1 t) := by
  set E := Real.exp (4 * t / c ^ 2)
  have hgap : ∀ g g0 : C(Icc (0:ℝ) t, ℝ), ∀ r ∈ Icc (0:ℝ) t,
      |extIccPath ht g r - extIccPath ht g0 r| ≤ dist g g0 := fun g g0 r hr => by
    rw [extIccPath_of_mem ht _ hr, extIccPath_of_mem ht _ hr, ← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  have hφc : Continuous fun p : (ℂ × C(Icc (0:ℝ) t, ℝ)) × (ℂ × C(Icc (0:ℝ) t, ℝ)) =>
      (dist p.1.1 p.2.1 + dist p.1.2 p.2.2) * E + dist p.1.2 p.2.2 := by fun_prop
  constructor
  · refine continuous_iff_continuousAt.2 fun p0 => ?_
    rw [← continuousWithinAt_univ]
    refine tamed_continuousWithinAt_of_dist_le (φ := fun p =>
      (dist p.1 p0.1 + dist p.2 p0.2) * E + dist p.2 p0.2) ?_ (by simp)
      (Eventually.of_forall fun p => ?_)
    · exact (hφc.comp (continuous_id.prodMk continuous_const)).continuousWithinAt
    · exact dist_tamedZ_le (continuous_extIccPath ht _) (continuous_extIccPath ht _) hc ht
        p.1 p0.1 (hgap p.2 p0.2) t ⟨ht, le_rfl⟩
  · refine continuous_iff_continuousAt.2 fun p0 => ?_
    rw [← continuousWithinAt_univ]
    refine tamed_continuousWithinAt_of_dist_le (φ := fun p =>
      8 / c ^ 3 * ((dist p.1 p0.1 + dist p.2 p0.2) * E + dist p.2 p0.2) * t) ?_ (by simp)
      (Eventually.of_forall fun p => ?_)
    · exact ((continuous_const.mul (hφc.comp (continuous_id.prodMk continuous_const))).mul
        continuous_const).continuousWithinAt
    · rw [Real.dist_eq]
      exact abs_tamedA_sub_le (continuous_extIccPath ht _) (continuous_extIccPath ht _) hc ht
        p.1 p0.1 (hgap p.2 p0.2) t ⟨ht, le_rfl⟩

theorem tamedA_congr_drive {W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (a : ℂ) (h : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r) :
    tamedA W c a t = tamedA W' c a t := by
  have := abs_tamedA_sub_le hW hW' hc ht a a (ε := 0) (fun r hr => by simp [h r hr])
    t ⟨ht, le_rfl⟩
  rw [dist_self, zero_add, zero_mul, zero_add, mul_zero, zero_mul] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- **FD-4, joint measurability and adaptedness.** For the SLE driver `W = √κ B(·, ω)` with
continuous paths, if every `B r`, `r ≤ t`, is measurable (e.g. for the σ-algebra `𝓕_t`), then
`(a, ω) ↦ Z̃_t(a)` and `(a, ω) ↦ Ã_t(a)` are measurable. -/
theorem measurable_tamed_drive {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) {c : ℝ} (hc : 0 < c)
    (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous fun t => B t ω) {t : ℝ} (ht : 0 ≤ t)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ t → Measurable (B r)) :
    Measurable (fun p : ℂ × Ω => tamedZ (drive κ B p.2) c p.1 t) ∧
    Measurable (fun p : ℂ × Ω => tamedA (drive κ B p.2) c p.1 t) := by
  let _ : MeasurableSpace C(Icc (0:ℝ) t, ℝ) := borel _
  have : BorelSpace C(Icc (0:ℝ) t, ℝ) := ⟨rfl⟩
  have hdc : ∀ ω, Continuous (drive κ B ω) := fun ω =>
    continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)
  let Φ : Ω → C(Icc (0:ℝ) t, ℝ) := fun ω =>
    ⟨fun x => drive κ B ω x, (hdc ω).comp continuous_subtype_val⟩
  have hΦ : Measurable Φ := measurable_to_continuousMap_Icc Φ fun x => by
    show Measurable fun ω => Real.sqrt κ * B (x : ℝ).toNNReal ω
    refine (hBm _ ?_).const_mul _
    rw [Real.coe_toNNReal _ x.2.1]; exact x.2.2
  have hagree : ∀ ω, ∀ r ∈ Icc (0:ℝ) t, drive κ B ω r = extIccPath ht (Φ ω) r :=
    fun ω r hr => by rw [extIccPath_of_mem ht _ hr]; rfl
  have hpair : Measurable fun p : ℂ × Ω => (p.1, Φ p.2) :=
    measurable_fst.prodMk (hΦ.comp measurable_snd)
  obtain ⟨hZ, hA⟩ := continuous_tamed_path hc ht
  constructor
  · have e : (fun p : ℂ × Ω => tamedZ (drive κ B p.2) c p.1 t) =
        (fun p : ℂ × C(Icc (0:ℝ) t, ℝ) => tamedZ (extIccPath ht p.2) c p.1 t) ∘
          (fun p : ℂ × Ω => (p.1, Φ p.2)) := by
      funext p
      exact tamedZ_congr_drive (hdc p.2) (continuous_extIccPath ht _) hc ht p.1 (hagree p.2)
    rw [e]; exact hZ.measurable.comp hpair
  · have e : (fun p : ℂ × Ω => tamedA (drive κ B p.2) c p.1 t) =
        (fun p : ℂ × C(Icc (0:ℝ) t, ℝ) => tamedA (extIccPath ht p.2) c p.1 t) ∘
          (fun p : ℂ × Ω => (p.1, Φ p.2)) := by
      funext p
      exact tamedA_congr_drive (hdc p.2) (continuous_extIccPath ht _) hc ht p.1 (hagree p.2)
    rw [e]; exact hA.measurable.comp hpair

/-! ## 6. FD-5: real points, comparison, bounded images -/

/-- First-crossing principle: a continuous `h` with `h 0 > 0` whose derivative is positive at
every zero stays positive. -/
theorem pos_of_deriv_pos_at_zeros {h : ℝ → ℝ} {T : ℝ} (hcont : ContinuousOn h (Icc 0 T))
    (h0 : 0 < h 0)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, h t = 0 → ∃ d > 0, HasDerivWithinAt h d (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 < h t := by
  by_contra hcon
  push_neg at hcon
  set S := {t ∈ Icc (0 : ℝ) T | h t ≤ 0}
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨t1, ht1, ht1'⟩ := hcon
  have hSne : S.Nonempty := ⟨t1, ht1, ht1'⟩
  have hSb : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  set τ := sInf S
  have hτ : τ ∈ S := hSc.csInf_mem hSne hSb
  have hpos_before : ∀ s ∈ Icc (0 : ℝ) T, s < τ → 0 < h s := fun s hs hsτ => by
    by_contra hh; push_neg at hh
    exact absurd (csInf_le hSb ⟨hs, hh⟩) (not_le.2 hsτ)
  have hτ0 : 0 < τ := by
    rcases hτ.1.1.lt_or_eq with h' | h'
    · exact h'
    · exfalso; have := hτ.2; rw [← h'] at this; linarith
  have hτz : h τ = 0 := by
    have hiv := intermediate_value_Icc' hτ.1.1 (hcont.mono (Icc_subset_Icc_right hτ.1.2))
    obtain ⟨s, hs, hs0⟩ := hiv ⟨hτ.2, h0.le⟩
    rcases hs.2.lt_or_eq with h' | h'
    · exact absurd hs0 (hpos_before s ⟨hs.1, hs.2.trans hτ.1.2⟩ h').ne'
    · rw [← h']; exact hs0
  obtain ⟨d, hdpos, hder⟩ := hd τ hτ.1 hτz
  have htend := (hasDerivWithinAt_iff_tendsto_slope.1 hder).mono_left
    (nhdsWithin_le_of_mem (mem_of_superset (Ico_mem_nhdsLT hτ0) (fun s hs =>
      ⟨⟨hs.1, hs.2.le.trans hτ.1.2⟩, ne_of_lt hs.2⟩)))
  obtain ⟨s, hs1, hs2⟩ := ((htend.eventually (lt_mem_nhds hdpos)).and
    (Ioo_mem_nhdsLT hτ0)).exists
  rw [slope_def_field, hτz, sub_zero] at hs1
  have hhs := hpos_before s ⟨hs2.1.le, hs2.2.le.trans hτ.1.2⟩ hs2.2
  have hneg : s - τ < 0 := by linarith [hs2.2]
  have : h s / (s - τ) < 0 := div_neg_of_pos_of_neg hhs hneg
  linarith

lemma exists_pos_le_norm_fwdSol {z : ℂ} {T : ℝ} (hT : 0 ≤ T) {v : ℝ → ℂ}
    (hv : IsForwardSol W z T v) : ∃ m > 0, ∀ t ∈ Icc (0 : ℝ) T, m ≤ ‖v t‖ := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (continuous_norm.comp_continuousOn hv.1)
  exact ⟨‖v t₀‖, norm_pos_iff.2 (hv.2 t₀ ht₀).1, fun t ht => hmin ht⟩

/-- **FD-5.** A forward solution started at a real point stays real. -/
theorem im_isForwardSol_real (hW : Continuous W) {x : ℝ} {T : ℝ} (hT : 0 ≤ T) {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) : ∀ t ∈ Icc (0 : ℝ) T, (v t).im = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_pos_le_norm_fwdSol hT hv
  set f : ℝ → ℝ := fun s => (v s + (W s : ℂ)).im with hf
  have hfe : ∀ s, f s = (v s).im := fun s => by simp [hf]
  have hfd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f ((2 / v s).im) (Icc 0 T) s := fun s hs =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s (hasDerivWithinAt_shift hv hs)
  have hfc : ContinuousOn f (Icc 0 T) := fun s hs => (hfd s hs).continuousWithinAt
  have hfd' : ∀ s ∈ Ico (0 : ℝ) T, HasDerivWithinAt f ((2 / v s).im) (Ici s) s := fun s hs =>
    (hfd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))
  have hbound : ∀ s ∈ Ico (0 : ℝ) T, ‖(2 / v s).im‖ ≤ 2 / m ^ 2 * ‖f s‖ + 0 := by
    intro s hs
    have hss := Ico_subset_Icc_self hs
    have hns : m ^ 2 ≤ Complex.normSq (v s) := by
      rw [Complex.normSq_eq_norm_sq]; gcongr; exact hm s hss
    have hnp : 0 < Complex.normSq (v s) := lt_of_lt_of_le (by positivity) hns
    have e : (2 / v s).im = -(2 * (v s).im) / Complex.normSq (v s) := by
      rw [Complex.div_im]; norm_num; ring
    rw [e, hfe, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
      abs_of_pos hnp, add_zero, abs_two]
    calc 2 * |(v s).im| / Complex.normSq (v s) ≤ 2 * |(v s).im| / m ^ 2 := by
          gcongr
      _ = 2 / m ^ 2 * |(v s).im| := by ring
  have h0 : ‖f 0‖ ≤ 0 := by
    rw [hfe, sol_zero hv hT]; simp
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hfc hfd' h0 hbound
  intro t ht
  have := hg t ht
  rw [gronwallBound_ε0_δ0] at this
  rw [← hfe]; exact norm_le_zero_iff.mp this

/-- **FD-5.** Real points to the right of the driver stay to the right. -/
theorem re_pos_isForwardSol_real (hW : Continuous W) {x : ℝ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) (hx : W 0 < x) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 < (v t).re := by
  refine pos_of_deriv_pos_at_zeros (h := fun s => (v s).re)
    (Complex.continuous_re.comp_continuousOn hv.1) ?_ ?_
  · show 0 < (v 0).re
    rw [sol_zero hv hT, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]; linarith
  · intro t ht h0
    exfalso
    exact (hv.2 t ht).1 (Complex.ext (by simpa using h0)
      (by simpa using im_isForwardSol_real hW hT hv t ht))

/-- **FD-5.** Real points to the left of the driver stay to the left. -/
theorem re_neg_isForwardSol_real (hW : Continuous W) {x : ℝ} {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) (hx : x < W 0) :
    ∀ t ∈ Icc (0 : ℝ) T, (v t).re < 0 := by
  have := pos_of_deriv_pos_at_zeros (h := fun s => -(v s).re)
    (Complex.continuous_re.comp_continuousOn hv.1).neg ?_ ?_
  · intro t ht; have := this t ht; linarith
  · show 0 < -(v 0).re
    rw [sol_zero hv hT, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]; linarith
  · intro t ht h0
    exfalso
    exact (hv.2 t ht).1 (Complex.ext (by simpa using h0)
      (by simpa using im_isForwardSol_real hW hT hv t ht))

lemma re_two_div_sub_tamed {v w : ℂ} (hvi : v.im = 0) (hre : w.re = v.re) (hα : v.re ≠ 0) :
    (2 / v).re - (2 / w).re = 2 * v.re * w.im ^ 2 / (v.re ^ 2 * (v.re ^ 2 + w.im ^ 2)) := by
  rw [Complex.div_re, Complex.div_re, Complex.normSq_apply, Complex.normSq_apply, hvi, hre]
  have h1 : v.re * v.re + w.im * w.im ≠ 0 :=
    ne_of_gt (by nlinarith [mul_self_nonneg w.im, mul_self_pos.2 hα])
  have h2 : v.re ^ 2 + w.im ^ 2 ≠ 0 :=
    ne_of_gt (by nlinarith [sq_nonneg w.im, mul_self_pos.2 hα])
  norm_num
  field_simp
  ring

/-- **FD-5, comparison (right).** If `Re a < x` and `W 0 < x`, then `Re f_t(a) < f_t(x)` while
both are alive. -/
theorem re_fwdSol_lt_real (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ} (ha : 0 < a.im)
    {u : ℝ → ℂ} (hu : IsForwardSol W a T u) {x : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) (hax : a.re < x) (hx : W 0 < x) :
    ∀ t ∈ Icc (0 : ℝ) T, (u t).re < (v t).re := by
  have hvi := im_isForwardSol_real hW hT hv
  have hvp := re_pos_isForwardSol_real hW hT hv hx
  have hui := (im_isForwardSol_le hW ha hu).2
  have hWc : ContinuousOn (fun s => (W s : ℂ)) (Icc 0 T) :=
    (Complex.continuous_ofReal.comp hW).continuousOn
  have key := pos_of_deriv_pos_at_zeros
    (h := fun s => (v s + (W s : ℂ)).re - (u s + (W s : ℂ)).re)
    ((Complex.continuous_re.comp_continuousOn (hv.1.add hWc)).sub
      (Complex.continuous_re.comp_continuousOn (hu.1.add hWc))) ?_ ?_
  · intro t ht; have := key t ht; simp only [Complex.add_re, Complex.ofReal_re] at this; linarith
  · show 0 < (v 0 + (W 0 : ℂ)).re - (u 0 + (W 0 : ℂ)).re
    rw [sol_zero hv hT, sol_zero hu hT]; simp; linarith
  · intro t ht hz
    simp only [Complex.add_re, Complex.ofReal_re] at hz
    have hre : (u t).re = (v t).re := by linarith
    refine ⟨(2 / v t).re - (2 / u t).re, ?_, ?_⟩
    · rw [re_two_div_sub_tamed (hvi t ht) hre (hvp t ht).ne']
      have h1 := hvp t ht; have h2 := hui t ht
      exact div_pos (mul_pos (mul_pos two_pos h1) (pow_pos h2 2))
        (mul_pos (pow_pos h1 2) (by positivity))
    · exact (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_shift hv ht)).sub
        (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_shift hu ht))

/-- **FD-5, comparison (left).** If `x < Re a` and `x < W 0`, then `f_t(x) < Re f_t(a)` while
both are alive. -/
theorem real_lt_re_fwdSol (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ} (ha : 0 < a.im)
    {u : ℝ → ℂ} (hu : IsForwardSol W a T u) {x : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) (hax : x < a.re) (hx : x < W 0) :
    ∀ t ∈ Icc (0 : ℝ) T, (v t).re < (u t).re := by
  have hvi := im_isForwardSol_real hW hT hv
  have hvn := re_neg_isForwardSol_real hW hT hv hx
  have hui := (im_isForwardSol_le hW ha hu).2
  have hWc : ContinuousOn (fun s => (W s : ℂ)) (Icc 0 T) :=
    (Complex.continuous_ofReal.comp hW).continuousOn
  have key := pos_of_deriv_pos_at_zeros
    (h := fun s => (u s + (W s : ℂ)).re - (v s + (W s : ℂ)).re)
    ((Complex.continuous_re.comp_continuousOn (hu.1.add hWc)).sub
      (Complex.continuous_re.comp_continuousOn (hv.1.add hWc))) ?_ ?_
  · intro t ht; have := key t ht; simp only [Complex.add_re, Complex.ofReal_re] at this; linarith
  · show 0 < (u 0 + (W 0 : ℂ)).re - (v 0 + (W 0 : ℂ)).re
    rw [sol_zero hv hT, sol_zero hu hT]; simp; linarith
  · intro t ht hz
    simp only [Complex.add_re, Complex.ofReal_re] at hz
    have hre : (u t).re = (v t).re := by linarith
    refine ⟨(2 / u t).re - (2 / v t).re, ?_, ?_⟩
    · have e := re_two_div_sub_tamed (hvi t ht) hre (hvn t ht).ne
      have e' : (2 / u t).re - (2 / v t).re = -((2 / v t).re - (2 / u t).re) := by ring
      rw [e', e, ← neg_div]
      have h1 := hvn t ht; have h2 := hui t ht
      have : 0 < (u t).im ^ 2 := pow_pos h2 2
      refine div_pos ?_ (mul_pos (by nlinarith) (by nlinarith))
      nlinarith
    · exact (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_shift hu ht)).sub
        (Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_shift hv ht))

/-- **FD-5, bounded images.** If the barriers `±R` (with `|W 0| < R`) are not hit by time `T`,
then every alive `a` with `|Re a| < R` has `‖f_T(a)‖ ≤ |f_T(R)| + |f_T(−R)| + Im a`. -/
theorem norm_fwdMap_le_of_barriers (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {R : ℝ}
    (hW0 : |W 0| < R) {vp vm : ℝ → ℂ} (hp : IsForwardSol W (R : ℂ) T vp)
    (hm : IsForwardSol W ((-R : ℝ) : ℂ) T vm) {a : ℂ} (ha : a ∈ H \ fwdHull W T)
    (haR : |a.re| < R) : ‖fwdMap W T a‖ ≤ |(vp T).re| + |(vm T).re| + a.im := by
  have ha0 : 0 < a.im := ha.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  have hTm : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [fwdMap_eq hW ha0 hu hTm]
  rw [abs_lt] at hW0 haR
  have h1 := re_fwdSol_lt_real hW hT ha0 hu hp haR.2 hW0.2 T hTm
  have h2 := real_lt_re_fwdSol hW hT ha0 hu hm (by linarith) (by linarith) T hTm
  have him := (im_isForwardSol_le hW ha0 hu).1 ⟨le_rfl, hT⟩ hTm hT
  have hpos := (im_isForwardSol_le hW ha0 hu).2 T hTm
  simp only [sol_zero hu hT, Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  have hre : |(u T).re| ≤ |(vp T).re| + |(vm T).re| := abs_le.2
    ⟨by linarith [neg_abs_le (vm T).re, abs_nonneg (vp T).re],
      by linarith [le_abs_self (vp T).re, abs_nonneg (vm T).re]⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [abs_of_pos hpos]
  linarith

/-- **FD-5, bounded images (set form).** -/
theorem isBounded_fwdMap_image_of_barriers (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {R : ℝ}
    (hW0 : |W 0| < R) (hp : ∃ vp, IsForwardSol W (R : ℂ) T vp)
    (hm : ∃ vm, IsForwardSol W ((-R : ℝ) : ℂ) T vm) {S : Set ℂ} {M : ℝ}
    (hS : ∀ a ∈ S, |a.re| < R ∧ a.im ≤ M) :
    Bornology.IsBounded (fwdMap W T '' (S ∩ (H \ fwdHull W T))) := by
  obtain ⟨vp, hp⟩ := hp
  obtain ⟨vm, hm⟩ := hm
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|(vp T).re| + |(vm T).re| + M, ?_⟩
  rintro _ ⟨a, ⟨haS, ha⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_fwdMap_le_of_barriers hW hT hW0 hp hm ha (hS a haS).1).trans
    (by linarith [(hS a haS).2])

end QuantumZipper
