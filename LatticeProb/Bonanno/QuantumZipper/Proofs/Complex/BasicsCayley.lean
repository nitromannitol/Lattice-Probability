/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsCayley at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Cayley and Möbius toolkit (EXT-CA node A1)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A1**.

* `cayley z = (z - i)/(z + i)` and its inverse `cayleyInv w = i (1 + w)/(1 - w)`:
  a bijection `ℍ → 𝔻` (`bijOn_cayley_H`), a homeomorphism `ℍ̄ ≃ₜ 𝔻̄ \ {1}`
  (`cayleyHomeomorphHbar`), `cayley z → 1` as `z → ∞` (`tendsto_cayley_cobounded`) and
  `cayleyInv w → ∞` as `w → 1` (`tendsto_cayleyInv_nhdsNE_one`); the Möbius open partial
  homeomorphism `ℂ \ {-i} → ℂ \ {1}` (`cayleyOPH`).
* Real Möbius maps `z ↦ (a z + b)/(c z + d)`, `ad - bc > 0`, are bijections of `ℍ`
  (`bijOn_realMobius_H`); special cases `z ↦ -1/z` and `z ↦ a z + b` (`a > 0`, `b ∈ ℝ`).
* Disk Möbius maps `z ↦ (z - a)/(1 - ā z)`, `‖a‖ < 1`, are bijections of `𝔻` with inverse
  the map for `-a` (`bijOn_diskMobius_ball`).

Elementary computations; see Ahlfors, *Complex Analysis* (3rd ed. 1979), Ch. 3 §3 (linear
transformations; the disk automorphisms `(z - a)/(1 - ā z)` appear with Schwarz's lemma, Ch. 4 §3.4).
-/

noncomputable section

open Set Metric Filter Topology Complex Bornology
open scoped ComplexConjugate

namespace QuantumZipper.CA

/-! ### The Cayley transform -/

/-- The Cayley transform `z ↦ (z - i)/(z + i)`, mapping `ℍ` onto the unit disk. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `w ↦ i (1 + w)/(1 - w)`. -/
def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem add_I_ne_zero_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem one_sub_cayley {z : ℂ} (hz : z + I ≠ 0) : 1 - cayley z = 2 * I / (z + I) := by
  unfold cayley
  field_simp
  ring

theorem cayley_ne_one {z : ℂ} (hz : z + I ≠ 0) : cayley z ≠ 1 := by
  intro h
  have h2 := one_sub_cayley hz
  rw [h, sub_self] at h2
  exact (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hz) h2.symm

theorem cayleyInv_add_I {w : ℂ} (hw : w ≠ 1) : cayleyInv w + I = 2 * I / (1 - w) := by
  have : (1 - w) ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  unfold cayleyInv
  field_simp
  ring

theorem cayleyInv_ne_neg_I {w : ℂ} (hw : w ≠ 1) : cayleyInv w ≠ -I := by
  intro h
  have h2 := cayleyInv_add_I hw
  rw [h, neg_add_cancel] at h2
  exact (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.2 (Ne.symm hw))) h2.symm

theorem ne_neg_I_iff {z : ℂ} : z ≠ -I ↔ z + I ≠ 0 := by
  rw [Ne, Ne, add_eq_zero_iff_eq_neg]

theorem cayleyInv_cayley {z : ℂ} (hz : z + I ≠ 0) : cayleyInv (cayley z) = z := by
  have h1 : 1 - cayley z ≠ 0 := sub_ne_zero.2 (Ne.symm (cayley_ne_one hz))
  have h2 : cayley z * (z + I) = z - I := by unfold cayley; field_simp
  unfold cayleyInv
  rw [div_eq_iff h1]
  linear_combination h2

theorem cayley_cayleyInv {w : ℂ} (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  have h1 : (1 - w) ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have h2 : cayleyInv w + I ≠ 0 := by
    rw [cayleyInv_add_I hw]; exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) h1
  unfold cayley
  rw [div_eq_iff h2]
  unfold cayleyInv
  field_simp
  ring

/-- `1 - ‖cayley z‖² = 4 Im z / |z + i|²`. -/
theorem one_sub_sq_norm_cayley (z : ℂ) (hz : z + I ≠ 0) :
    1 - ‖cayley z‖ ^ 2 = 4 * z.im / normSq (z + I) := by
  have hn : normSq (z + I) ≠ 0 := (normSq_pos.2 hz).ne'
  rw [cayley, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
  field_simp
  simp only [normSq_apply, add_re, sub_re, add_im, sub_im, I_re, I_im]
  ring

/-- `Im (cayleyInv w) = (1 - ‖w‖²)/|1 - w|²`. -/
theorem im_cayleyInv (w : ℂ) : (cayleyInv w).im = (1 - ‖w‖ ^ 2) / normSq (1 - w) := by
  rw [cayleyInv, mul_div_assoc, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, div_re,
    Complex.sq_norm]
  simp only [normSq_apply, add_re, sub_re, add_im, sub_im, one_re, one_im]
  rw [← add_div]
  congr 1
  ring

theorem cayley_mem_ball {z : ℂ} (hz : z ∈ H) : cayley z ∈ ball (0 : ℂ) 1 := by
  have hz' : 0 < z.im := hz
  have h0 := add_I_ne_zero_of_im_nonneg hz'.le
  have h := one_sub_sq_norm_cayley z h0
  have : 0 < 4 * z.im / normSq (z + I) := div_pos (by linarith) (normSq_pos.2 h0)
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg (cayley z)]

theorem cayley_mem_closedBall {z : ℂ} (hz : z ∈ Hbar) : cayley z ∈ closedBall (0 : ℂ) 1 := by
  have hz' : 0 ≤ z.im := hz
  have h0 := add_I_ne_zero_of_im_nonneg hz'
  have h := one_sub_sq_norm_cayley z h0
  have : 0 ≤ 4 * z.im / normSq (z + I) := div_nonneg (by linarith) (normSq_nonneg _)
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg (cayley z)]

theorem cayleyInv_mem_H {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : cayleyInv w ∈ H := by
  rw [mem_ball_zero_iff] at hw
  have h1 : (1 - w) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hw; exact lt_irrefl _ hw
  show 0 < (cayleyInv w).im
  rw [im_cayleyInv]
  exact div_pos (by nlinarith [norm_nonneg w]) (normSq_pos.2 h1)

theorem cayleyInv_mem_Hbar {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : cayleyInv w ∈ Hbar := by
  rw [mem_closedBall_zero_iff] at hw
  show 0 ≤ (cayleyInv w).im
  rw [im_cayleyInv]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (normSq_nonneg _)

theorem bijOn_cayley_H : BijOn cayley H (ball (0 : ℂ) 1) := by
  refine ⟨fun z hz => cayley_mem_ball hz, fun z hz w hw hzw => ?_, fun w hw => ?_⟩
  · rw [← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt (show 0 < z.im from hz))),
      hzw, cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt (show 0 < w.im from hw)))]
  · have hw1 : w ≠ 1 := by
      rintro rfl; simp at hw
    exact ⟨cayleyInv w, cayleyInv_mem_H hw, cayley_cayleyInv hw1⟩

theorem bijOn_cayley_Hbar : BijOn cayley Hbar (closedBall (0 : ℂ) 1 \ {1}) := by
  refine ⟨fun z hz => ⟨cayley_mem_closedBall hz,
      cayley_ne_one (add_I_ne_zero_of_im_nonneg hz)⟩, fun z hz w hw hzw => ?_, fun w hw => ?_⟩
  · rw [← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg hz), hzw,
      cayleyInv_cayley (add_I_ne_zero_of_im_nonneg hw)]
  · exact ⟨cayleyInv w, cayleyInv_mem_Hbar hw.1, cayley_cayleyInv hw.2⟩

theorem differentiableAt_cayley {z : ℂ} (hz : z + I ≠ 0) : DifferentiableAt ℂ cayley z :=
  ((differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I) hz)

theorem differentiableAt_cayleyInv {w : ℂ} (hw : w ≠ 1) : DifferentiableAt ℂ cayleyInv w :=
  ((differentiableAt_const _).mul (differentiableAt_const _ |>.add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) (sub_ne_zero.2 (Ne.symm hw))

theorem continuousOn_cayley : ContinuousOn cayley {z | z ≠ -I} := fun _ hz =>
  (differentiableAt_cayley (ne_neg_I_iff.1 hz)).continuousAt.continuousWithinAt

theorem continuousOn_cayleyInv : ContinuousOn cayleyInv {w | w ≠ 1} := fun _ hw =>
  (differentiableAt_cayleyInv hw).continuousAt.continuousWithinAt

theorem differentiableOn_cayley_Hbar : DifferentiableOn ℂ cayley Hbar := fun _ hz =>
  (differentiableAt_cayley (add_I_ne_zero_of_im_nonneg hz)).differentiableWithinAt

theorem differentiableOn_cayleyInv_closedBall :
    DifferentiableOn ℂ cayleyInv (closedBall (0 : ℂ) 1 \ {1}) := fun _ hw =>
  (differentiableAt_cayleyInv hw.2).differentiableWithinAt

/-- The Cayley transform as an open partial homeomorphism `ℂ \ {-i} → ℂ \ {1}`. -/
def cayleyOPH : OpenPartialHomeomorph ℂ ℂ where
  toFun := cayley
  invFun := cayleyInv
  source := {z | z ≠ -I}
  target := {w | w ≠ 1}
  map_source' _ hz := cayley_ne_one (ne_neg_I_iff.1 hz)
  map_target' _ hw := cayleyInv_ne_neg_I hw
  left_inv' _ hz := cayleyInv_cayley (ne_neg_I_iff.1 hz)
  right_inv' _ hw := cayley_cayleyInv hw
  open_source := isOpen_ne
  open_target := isOpen_ne
  continuousOn_toFun := continuousOn_cayley
  continuousOn_invFun := continuousOn_cayleyInv

/-- `cayley z → 1` as `z → ∞`. -/
theorem tendsto_cayley_cobounded : Tendsto cayley (cobounded ℂ) (𝓝 1) := by
  have hg : Tendsto (fun u : ℂ => (1 - I * u) / (1 + I * u)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun u : ℂ => (1 - I * u) / (1 + I * u)) 0 :=
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).div
        ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt) (by simp)
    simpa using this.tendsto
  have hev : ∀ᶠ z in cobounded ℂ, z ≠ 0 :=
    (tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).mono fun z hz => norm_pos_iff.1 hz
  refine (hg.comp tendsto_inv₀_cobounded).congr' ?_
  filter_upwards [hev] with z hz
  simp only [Function.comp_apply, cayley]
  rcases eq_or_ne (z + I) 0 with h | h
  · have hz' : z = -I := eq_neg_of_add_eq_zero_left h
    subst hz'
    simp
  · have h2 : 1 + I * z⁻¹ ≠ 0 := by
      intro h2; apply h
      have : z * (1 + I * z⁻¹) = z + I := by field_simp
      rw [← this, h2, mul_zero]
    field_simp

/-- `cayleyInv w → ∞` as `w → 1`, `w ≠ 1`. -/
theorem tendsto_cayleyInv_nhdsNE_one : Tendsto cayleyInv (𝓝[≠] 1) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun w : ℂ => ‖I * (1 + w)‖) (𝓝[≠] 1) (𝓝 2) := by
    have : Continuous (fun w : ℂ => ‖I * (1 + w)‖) := by fun_prop
    have h := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
    convert h using 2
    simp only [norm_mul, norm_I, one_mul]
    norm_num
  have h2 : Tendsto (fun w : ℂ => ‖1 - w‖⁻¹) (𝓝[≠] 1) atTop := by
    have hsub : Tendsto (fun w : ℂ => 1 - w) (𝓝[≠] 1) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun w : ℂ => 1 - w) (𝓝 1) (𝓝 (1 - 1)) :=
          tendsto_const_nhds.sub tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact sub_ne_zero.2 (Ne.symm hw)
    have := tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp hsub)
    simpa [Function.comp_def, norm_inv] using this
  have := h1.pos_mul_atTop (by norm_num) h2
  refine this.congr fun w => ?_
  rw [cayleyInv, norm_div, div_eq_mul_inv]

/-! ### Automorphisms of `ℍ`: real Möbius maps -/

/-- The real Möbius map `z ↦ (a z + b)/(c z + d)`. -/
def realMobius (a b c d : ℝ) (z : ℂ) : ℂ := (a * z + b) / (c * z + d)

theorem realMobius_im (a b c d : ℝ) (z : ℂ) :
    (realMobius a b c d z).im = (a * d - b * c) * z.im / normSq (c * z + d) := by
  rw [realMobius, div_im]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
  rw [div_sub_div_same]
  congr 1
  ring

theorem realMobius_denom_ne_zero {a b c d : ℝ} (h : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ H) :
    (c : ℂ) * z + d ≠ 0 := by
  have hz' : 0 < z.im := hz
  intro h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp at hre him
  rcases him with hc | hz0
  · subst hc; simp at hre; subst hre; simp at h
  · linarith

theorem realMobius_mem_H {a b c d : ℝ} (h : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ H) :
    realMobius a b c d z ∈ H := by
  show 0 < (realMobius a b c d z).im
  rw [realMobius_im]
  exact div_pos (mul_pos h hz) (normSq_pos.2 (realMobius_denom_ne_zero h hz))

theorem realMobius_inv_apply {a b c d : ℝ} (h : 0 < a * d - b * c) {z : ℂ} (hz : z ∈ H) :
    realMobius d (-b) (-c) a (realMobius a b c d z) = z := by
  have h0 := realMobius_denom_ne_zero h hz
  have hdet : ((a : ℂ) * d - b * c) ≠ 0 := by exact_mod_cast h.ne'
  have h0' : (d : ℂ) + z * c ≠ 0 := by rw [add_comm, mul_comm]; exact h0
  have e1 : (d : ℂ) * (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) + ((-b : ℝ) : ℂ) =
      ((a : ℂ) * d - b * c) * z / ((c : ℂ) * z + d) := by
    rw [eq_div_iff h0, add_mul, mul_assoc, div_mul_cancel₀ _ h0]; push_cast; ring
  have e2 : ((-c : ℝ) : ℂ) * (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) + (a : ℂ) =
      ((a : ℂ) * d - b * c) / ((c : ℂ) * z + d) := by
    rw [eq_div_iff h0, add_mul, mul_assoc, div_mul_cancel₀ _ h0]; push_cast; ring
  unfold realMobius
  rw [e1, e2]
  field_simp

theorem bijOn_realMobius_H {a b c d : ℝ} (h : 0 < a * d - b * c) :
    BijOn (realMobius a b c d) H H := by
  have h' : 0 < d * a - (-b) * (-c) := by linarith
  refine ⟨fun z hz => realMobius_mem_H h hz, fun z hz w hw hzw => ?_, fun w hw => ?_⟩
  · rw [← realMobius_inv_apply h hz, hzw, realMobius_inv_apply h hw]
  · refine ⟨realMobius d (-b) (-c) a w, realMobius_mem_H h' hw, ?_⟩
    have := realMobius_inv_apply h' hw
    simpa using this

/-- `z ↦ a z + b` (`a > 0`, `b ∈ ℝ`) is a bijection of `ℍ`. -/
theorem bijOn_affine_H {a b : ℝ} (ha : 0 < a) : BijOn (fun z : ℂ => a * z + b) H H := by
  have := bijOn_realMobius_H (a := a) (b := b) (c := 0) (d := 1) (by simpa using ha)
  refine this.congr fun z _ => ?_
  simp [realMobius]

/-! ### Automorphisms of `𝔻`: disk Möbius maps -/

/-- The disk Möbius map `z ↦ (z - a)/(1 - ā z)`. -/
def diskMobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

theorem normSq_denom_sub_normSq_num (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

theorem diskMobius_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := by linear_combination -h
  have := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, norm_one] at this
  nlinarith [norm_nonneg a, norm_nonneg z]

theorem one_sub_sq_norm_diskMobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - ‖diskMobius a z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / normSq (1 - conj a * z) := by
  have h0 := diskMobius_denom_ne_zero ha hz
  have hn : normSq (1 - conj a * z) ≠ 0 := (normSq_pos.2 h0).ne'
  rw [diskMobius, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
    Complex.sq_norm, eq_div_iff hn, sub_mul, div_mul_cancel₀ _ hn, one_mul]
  linear_combination normSq_denom_sub_normSq_num a z

theorem diskMobius_mem_ball {a z : ℂ} (ha : ‖a‖ < 1) (hz : z ∈ ball (0 : ℂ) 1) :
    diskMobius a z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hz ⊢
  have h := one_sub_sq_norm_diskMobius ha hz.le
  have : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / normSq (1 - conj a * z) :=
    div_pos (mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z]))
      (normSq_pos.2 (diskMobius_denom_ne_zero ha hz.le))
  nlinarith [norm_nonneg (diskMobius a z)]

theorem diskMobius_self (a : ℂ) : diskMobius a a = 0 := by simp [diskMobius]

theorem diskMobius_neg_diskMobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMobius (-a) (diskMobius a z) = z := by
  have h0 := diskMobius_denom_ne_zero ha hz
  have hna : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [mul_comm, Complex.mul_conj']
    intro h
    have : ‖a‖ ^ 2 = 1 := by exact_mod_cast (sub_eq_zero.1 h).symm
    nlinarith [norm_nonneg a]
  have h0' : 1 - z * conj a ≠ 0 := by rw [mul_comm]; exact h0
  have hna' : 1 - a * conj a ≠ 0 := by rw [mul_comm]; exact hna
  have e1 : (z - a) / (1 - conj a * z) - -a = z * (1 - conj a * a) / (1 - conj a * z) := by
    field_simp; ring
  have e2 : 1 - conj (-a) * ((z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    rw [map_neg]; field_simp; ring
  unfold diskMobius
  rw [e1, e2]
  field_simp

theorem differentiableOn_diskMobius {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (diskMobius a) (closedBall (0 : ℂ) 1) := fun z hz => by
  have : DifferentiableAt ℂ (fun w : ℂ => (w - a) / (1 - conj a * w)) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop)
      (diskMobius_denom_ne_zero ha (mem_closedBall_zero_iff.1 hz))
  exact this.differentiableWithinAt

end QuantumZipper.CA
