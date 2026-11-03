/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.KernelIdentities at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue

/-!
# M4-R1: kernel identities for folded circles

Closed forms of `K(fc(z,r), fc(w,ρ)) = kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ)`.

* Boundary (`s t : ℝ`): `kernelCov_fc_real_separated` (K1), `kernelCov_fc_real_sameCenter` (K2),
  `kernelCov_fc_real_nested` (K3, big circle first), `kernelCov_fc_real_nested'` (small first).
* `neumannH_smul` (K4).
* Interior (`z w ∈ ℍ`, radii `≤ Im`): `kernelCov_fc_interior_separated`,
  `kernelCov_fc_interior_nested`, `kernelCov_fc_interior_nested'`,
  `kernelCov_fc_interior_sameCenter`.
* Normalization circle: `kernelCov_fc_bigCircle_right`, `kernelCov_fc_bigCircle_left`.
* Affine covariance: `kernelCov_fc_affine`.
-/

noncomputable section

open MeasureTheory
open scoped Real ComplexConjugate
open QuantumZipper.CircleMV

namespace QuantumZipper

namespace KernelId

/-- The folded-circle potential `x ↦ ∫ neumannH x y d(foldedCircle a r)(y)`, in closed form. -/
def fcPot (r : ℝ) (a x : ℂ) : ℝ :=
  -Real.log (max r ‖a - x‖) - Real.log (max r ‖a - conj x‖)

theorem integral_neumannH_foldedCircle_right' (a x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ y, neumannH x y ∂(foldedCircle a r) = fcPot r a x := by
  simp_rw [neumannH_symm x]
  exact integral_neumannH_foldedCircle a x hr

theorem continuous_fcPot {r : ℝ} (hr : 0 < r) (a : ℂ) : Continuous (fcPot r a) := by
  unfold fcPot
  refine ((continuous_const.max ?_).log fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne').neg.sub
    ((continuous_const.max ?_).log fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne')
  · exact (continuous_const.sub continuous_id).norm
  · exact (continuous_const.sub Complex.continuous_conj).norm

theorem fcPot_foldH (ρ : ℝ) (w x : ℂ) : fcPot ρ w (foldH x) = fcPot ρ w x := by
  unfold foldH
  split_ifs
  · rfl
  · unfold fcPot; rw [Complex.conj_conj]; ring

/-- Potential form of the folded-circle kernel. -/
theorem kernelCov_fc_eq_integral (z w : ℂ) (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) =
      ∫ x, fcPot ρ w x ∂(circleUnif z r) := by
  unfold kernelCov
  simp_rw [integral_neumannH_foldedCircle_right' w _ hρ]
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable
    (continuous_fcPot hρ w).aestronglyMeasurable]
  simp_rw [fcPot_foldH]

theorem norm_sub_conj_swap (w x : ℂ) : ‖w - conj x‖ = ‖x - conj w‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]

theorem im_add_im_le_norm_sub_conj (x w : ℂ) : x.im + w.im ≤ ‖x - conj w‖ := by
  have h : (x - conj w).im = x.im + w.im := by simp
  rw [← h]; exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

theorem im_sub_le_of_norm {x z : ℂ} {r : ℝ} (h : ‖x - z‖ = r) : z.im - r ≤ x.im := by
  have h1 : (z - x).im ≤ ‖z - x‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
  rw [norm_sub_rev, h] at h1; simp at h1; linarith

theorem integral_neumannH_circleUnif (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ x, neumannH x w ∂(circleUnif z r) =
      -Real.log (max r ‖z - w‖) - Real.log (max r ‖z - conj w‖) := by
  have hm : Measurable fun x => neumannH x w :=
    measurable_neumannH.comp (measurable_id.prodMk measurable_const)
  rw [← integral_neumannH_foldedCircle z w hr, foldedCircle, integral_map
    measurable_foldH.aemeasurable hm.aestronglyMeasurable]
  simp_rw [neumannH_foldH]

/-- Master identity 1: the second circle is a.e. outside the first circle's reach. -/
theorem kernelCov_fc_master_out (z w : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (h : ∀ᵐ x ∂(circleUnif z r), ρ ≤ ‖x - w‖ ∧ ρ ≤ ‖x - conj w‖) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) =
      -Real.log (max r ‖z - w‖) - Real.log (max r ‖z - conj w‖) := by
  rw [kernelCov_fc_eq_integral z w r hρ, ← integral_neumannH_circleUnif z w hr]
  refine integral_congr_ae (h.mono fun x hx => ?_)
  simp only [fcPot, neumannH]
  rw [norm_sub_rev w x, norm_sub_conj_swap, max_eq_right hx.1, max_eq_right hx.2]

/-- Master identity 2. -/
theorem kernelCov_fc_master_mixed (z w : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (h : ∀ᵐ x ∂(circleUnif z r), ‖x - w‖ ≤ ρ ∧ ρ ≤ ‖x - conj w‖) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) =
      -Real.log ρ - Real.log (max r ‖z - conj w‖) := by
  rw [kernelCov_fc_eq_integral z w r hρ]
  rw [integral_congr_ae (g := fun x => -Real.log ρ - Real.log ‖x - conj w‖) (h.mono fun x hx => ?_)]
  · rw [integral_sub (integrable_const _) (integrable_log_norm_sub_circleUnif z (conj w) r),
      integral_log_norm_sub_circleUnif z _ hr]
    simp
  · simp only [fcPot]
    rw [norm_sub_rev w x, norm_sub_conj_swap, max_eq_left hx.1, max_eq_right hx.2]

/-- Master identity 3. -/
theorem kernelCov_fc_master_in (z w : ℂ) (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ᵐ x ∂(circleUnif z r), ‖x - w‖ ≤ ρ ∧ ‖x - conj w‖ ≤ ρ) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) = -2 * Real.log ρ := by
  rw [kernelCov_fc_eq_integral z w r hρ]
  rw [integral_congr_ae (g := fun _ => -2 * Real.log ρ) (h.mono fun x hx => ?_)]
  · simp
  · simp only [fcPot]
    rw [norm_sub_rev w x, norm_sub_conj_swap, max_eq_left hx.1, max_eq_left hx.2]; ring

theorem ae_norm_sub_center (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂(circleUnif z r), ‖x - z‖ = r := by
  filter_upwards [ae_circleUnif z r] with x hx
  rw [hx, abs_of_pos hr]

theorem norm_ofReal_sub (s t : ℝ) : ‖(s : ℂ) - (t : ℂ)‖ = |s - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem conj_ofReal' (t : ℝ) : conj (t : ℂ) = t := Complex.conj_ofReal t

end KernelId

open KernelId

/-! ## Boundary identities -/

/-- (K1) Separated boundary semicircles. -/
theorem kernelCov_fc_real_separated {s t r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (h : r + ρ ≤ |s - t|) :
    kernelCov neumannH (foldedCircle s r) (foldedCircle t ρ) = -2 * Real.log |s - t| := by
  have hae : ∀ᵐ x : ℂ ∂(circleUnif (s : ℂ) r), ρ ≤ ‖x - (t : ℂ)‖ ∧ ρ ≤ ‖x - conj (t : ℂ)‖ := by
    filter_upwards [ae_norm_sub_center (s : ℂ) hr] with x hx
    rw [conj_ofReal']
    have := norm_sub_norm_le ((s : ℂ) - t) (s - x)
    rw [norm_ofReal_sub, norm_sub_rev (s : ℂ) x, hx] at this
    have e : (s : ℂ) - t - (s - x) = x - t := by ring
    rw [e] at this
    constructor <;> linarith
  rw [kernelCov_fc_master_out _ _ hr hρ hae, conj_ofReal', norm_ofReal_sub,
    max_eq_right (by linarith)]
  ring

/-- (K3) Nested boundary semicircles, big one first. -/
theorem kernelCov_fc_real_nested {s t r ρ : ℝ} (hρ : 0 < ρ) (h : |t - s| + ρ ≤ r) :
    kernelCov neumannH (foldedCircle s r) (foldedCircle t ρ) = -2 * Real.log r := by
  have hr : 0 < r := by linarith [abs_nonneg (t - s)]
  have hae : ∀ᵐ x : ℂ ∂(circleUnif (s : ℂ) r), ρ ≤ ‖x - (t : ℂ)‖ ∧ ρ ≤ ‖x - conj (t : ℂ)‖ := by
    filter_upwards [ae_norm_sub_center (s : ℂ) hr] with x hx
    rw [conj_ofReal']
    have := norm_sub_norm_le (x - s) (t - s)
    rw [norm_ofReal_sub, hx] at this
    have e : x - s - (t - s) = x - t := by ring
    rw [e] at this
    constructor <;> linarith
  rw [kernelCov_fc_master_out _ _ hr hρ hae, conj_ofReal', norm_ofReal_sub,
    max_eq_left (by rw [abs_sub_comm]; linarith)]
  ring

/-- Nested boundary semicircles, small one first. -/
theorem kernelCov_fc_real_nested' {s t r ρ : ℝ} (hr : 0 < r) (h : |s - t| + r ≤ ρ) :
    kernelCov neumannH (foldedCircle s r) (foldedCircle t ρ) = -2 * Real.log ρ := by
  have hρ : 0 < ρ := by linarith [abs_nonneg (s - t)]
  have hae : ∀ᵐ x : ℂ ∂(circleUnif (s : ℂ) r), ‖x - (t : ℂ)‖ ≤ ρ ∧ ‖x - conj (t : ℂ)‖ ≤ ρ := by
    filter_upwards [ae_norm_sub_center (s : ℂ) hr] with x hx
    rw [conj_ofReal']
    have := norm_add_le (x - s) (s - t)
    rw [norm_ofReal_sub, hx] at this
    have e : x - s + (s - t) = x - t := by ring
    rw [e] at this
    constructor <;> linarith
  exact kernelCov_fc_master_in _ _ _ hρ hae

/-- (K2) Concentric boundary semicircles. -/
theorem kernelCov_fc_real_sameCenter {s r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    kernelCov neumannH (foldedCircle s r) (foldedCircle s ρ) = -2 * Real.log (max r ρ) := by
  rcases le_total ρ r with h | h
  · rw [max_eq_left h]; exact kernelCov_fc_real_nested hρ (by simpa using h)
  · rw [max_eq_right h]; exact kernelCov_fc_real_nested' hr (by simpa using h)

/-- (K4) Scaling of the Neumann kernel. -/
theorem neumannH_smul {x y : ℂ} {l : ℝ} (hl : 0 < l) (hxy : x ≠ y) (hxy' : x ≠ conj y) :
    neumannH ((l : ℂ) * x) ((l : ℂ) * y) = neumannH x y - 2 * Real.log l := by
  unfold neumannH
  have e1 : ‖(l : ℂ) * x - l * y‖ = l * ‖x - y‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  have e2 : ‖(l : ℂ) * x - conj ((l : ℂ) * y)‖ = l * ‖x - conj y‖ := by
    rw [map_mul, Complex.conj_ofReal, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hl]
  rw [e1, e2, Real.log_mul hl.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)),
    Real.log_mul hl.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy'))]
  ring

/-! ## Interior identities -/

/-- Separated interior circles: the kernel is the pointwise `neumannH`. -/
theorem kernelCov_fc_interior_separated {z w : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hrz : r ≤ z.im) (hρw : ρ ≤ w.im) (h : r + ρ ≤ ‖z - w‖) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) = neumannH z w := by
  have hae : ∀ᵐ x ∂(circleUnif z r), ρ ≤ ‖x - w‖ ∧ ρ ≤ ‖x - conj w‖ := by
    filter_upwards [ae_norm_sub_center z hr] with x hx
    have h1 := norm_sub_norm_le (z - w) (z - x)
    rw [norm_sub_rev z x, hx] at h1
    have e : z - w - (z - x) = x - w := by ring
    rw [e] at h1
    have h2 := im_add_im_le_norm_sub_conj x w
    have h3 := im_sub_le_of_norm hx
    constructor <;> linarith
  have hc := im_add_im_le_norm_sub_conj z w
  rw [kernelCov_fc_master_out _ _ hr hρ hae, max_eq_right (by linarith),
    max_eq_right (by linarith)]
  rfl

/-- Nested interior circles, big one first. -/
theorem kernelCov_fc_interior_nested {z w : ℂ} {r ρ : ℝ} (hρ : 0 < ρ)
    (hrz : r ≤ z.im) (hρw : ρ ≤ w.im) (h : ‖w - z‖ + ρ ≤ r) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) =
      -Real.log r - Real.log ‖z - conj w‖ := by
  have hr : 0 < r := by linarith [norm_nonneg (w - z)]
  have hae : ∀ᵐ x ∂(circleUnif z r), ρ ≤ ‖x - w‖ ∧ ρ ≤ ‖x - conj w‖ := by
    filter_upwards [ae_norm_sub_center z hr] with x hx
    have h1 := norm_sub_norm_le (x - z) (w - z)
    rw [hx] at h1
    have e : x - z - (w - z) = x - w := by ring
    rw [e] at h1
    have h2 := im_add_im_le_norm_sub_conj x w
    have h3 := im_sub_le_of_norm hx
    constructor <;> linarith
  have hc := im_add_im_le_norm_sub_conj z w
  rw [kernelCov_fc_master_out _ _ hr hρ hae, max_eq_left (by rw [norm_sub_rev]; linarith),
    max_eq_right (by linarith)]

/-- Nested interior circles, small one first. -/
theorem kernelCov_fc_interior_nested' {z w : ℂ} {r ρ : ℝ} (hr : 0 < r)
    (hrz : r ≤ z.im) (hρw : ρ ≤ w.im) (h : ‖z - w‖ + r ≤ ρ) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle w ρ) =
      -Real.log ρ - Real.log ‖z - conj w‖ := by
  have hρ : 0 < ρ := by linarith [norm_nonneg (z - w)]
  have hae : ∀ᵐ x ∂(circleUnif z r), ‖x - w‖ ≤ ρ ∧ ρ ≤ ‖x - conj w‖ := by
    filter_upwards [ae_norm_sub_center z hr] with x hx
    have h1 := norm_add_le (x - z) (z - w)
    rw [hx] at h1
    have e : x - z + (z - w) = x - w := by ring
    rw [e] at h1
    have h2 := im_add_im_le_norm_sub_conj x w
    have h3 := im_sub_le_of_norm hx
    constructor <;> linarith
  have hc := im_add_im_le_norm_sub_conj z w
  rw [kernelCov_fc_master_mixed _ _ hr hρ hae, max_eq_right (by linarith)]

/-- Concentric interior circles. -/
theorem kernelCov_fc_interior_sameCenter {z : ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hrz : r ≤ z.im) (hρz : ρ ≤ z.im) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle z ρ) =
      -Real.log (max r ρ) - Real.log ‖z - conj z‖ := by
  rcases le_total ρ r with h | h
  · rw [max_eq_left h]; exact kernelCov_fc_interior_nested hρ hrz hρz (by simpa using h)
  · rw [max_eq_right h]; exact kernelCov_fc_interior_nested' hr hrz hρz (by simpa using h)

/-! ## The normalization circle `fc(0,R)` -/

/-- A folded circle inside `B(0,R)` against `fc(0,R)`. -/
theorem kernelCov_fc_bigCircle_right {a : ℂ} {r R : ℝ} (hr : 0 < r) (h : ‖a‖ + r ≤ R) :
    kernelCov neumannH (foldedCircle a r) (foldedCircle 0 R) = -2 * Real.log R := by
  have hR : 0 < R := by linarith [norm_nonneg a]
  refine kernelCov_fc_master_in _ _ _ hR ?_
  filter_upwards [ae_norm_sub_center a hr] with x hx
  have h1 := norm_add_le (x - a) a
  rw [hx, sub_add_cancel] at h1
  simp only [map_zero, sub_zero]
  constructor <;> linarith

/-- `fc(0,R)` against a folded circle inside `B(0,R)`. -/
theorem kernelCov_fc_bigCircle_left {b : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (h : ‖b‖ + ρ ≤ R) :
    kernelCov neumannH (foldedCircle 0 R) (foldedCircle b ρ) = -2 * Real.log R := by
  have hR : 0 < R := by linarith [norm_nonneg b]
  have hae : ∀ᵐ x ∂(circleUnif 0 R), ρ ≤ ‖x - b‖ ∧ ρ ≤ ‖x - conj b‖ := by
    filter_upwards [ae_norm_sub_center 0 hR] with x hx
    rw [sub_zero] at hx
    have h1 := norm_sub_norm_le x b
    have h2 := norm_sub_norm_le x (conj b)
    rw [Complex.norm_conj] at h2
    constructor <;> linarith
  rw [kernelCov_fc_master_out _ _ hR hρ hae, zero_sub, zero_sub, norm_neg, norm_neg,
    Complex.norm_conj, max_eq_left (by linarith)]
  ring

/-! ## Affine covariance (real translation, positive dilation) -/

namespace KernelId

theorem integrable_circleUnif_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (z : ℂ) (r : ℝ) :
    Integrable f (circleUnif z r) := by
  unfold circleUnif
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2
    (by positivity)).ne')
  rw [integrable_map_measure hf.aestronglyMeasurable (measurable_circleMap z r).aemeasurable]
  exact ((hf.comp (continuous_circleMap z r)).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self

theorem circleUnif_affine (t : ℝ) (l : ℝ) (a : ℂ) (r : ℝ) :
    circleUnif ((t : ℂ) + l * a) (l * r) =
      (circleUnif a r).map (fun x => (t : ℂ) + l * x) := by
  have hm : Measurable (fun x : ℂ => (t : ℂ) + l * x) :=
    (measurable_const.add (measurable_const.mul measurable_id))
  unfold circleUnif
  rw [Measure.map_smul, Measure.map_map hm (measurable_circleMap a r)]
  all_goals first
    | exact hm.aemeasurable
    | (congr 2; funext θ; simp only [Function.comp, circleMap, Complex.ofReal_mul]; ring)

end KernelId

end QuantumZipper
